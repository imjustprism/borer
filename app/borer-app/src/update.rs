//! The check for a newer release of borer on GitHub, and the title bar's notice of one.
//!
//! The check is one `GET` of [`LATEST_URL`] carrying only `User-Agent: borer-app/<version>`
//! ([`user_agent`]) and `Accept: application/vnd.github+json`: no identifier, file, cookie or
//! credential. It follows no redirect, gives up after [`TIMEOUT`], reads at most
//! [`MAX_BODY_BYTES`], and [`judge`] reads the answer. An interactive window starts it
//! [`FIRST_DELAY`] after it opens and again every [`PERIOD`]; the measurement and demo modes
//! never do. No request is made while `BORER_NO_UPDATE_CHECK` is `1` ([`OPT_OUT`]), while
//! Zed's `auto_update` setting is `false`, or while the person's settings file did not load
//! in full. Each check reads the setting anew, but the app reads the person's file only at
//! launch, so an edit made outside the app counts after a restart. Nothing is downloaded or installed: a newer release shows a button that opens
//! its page on GitHub, built from its version alone ([`Release::url`]).

use std::sync::Arc;
use std::time::Duration;

use borer_front::release::{
    LATEST_URL, MAX_BODY_BYTES, OPT_OUT, Outcome, Release, Version, judge, opted_out, user_agent,
};
use futures::AsyncReadExt as _;
use gpui::{
    AnyElement, App, AppContext as _, Context, Global, IntoElement as _, Task, TaskExt as _,
};
use http_client::{AsyncBody, HttpClient, HttpRequestExt as _, Method, RedirectPolicy, Request};
use settings::{Settings, SettingsContent};
use ui::{IconName, UpdateButton};
use workspace::notifications::NotificationId;
use workspace::{Toast, Workspace};

/// The product the check's `User-Agent` names ([`user_agent`]).
const PRODUCT: &str = "borer-app";

/// How long the check waits for GitHub's whole answer.
const TIMEOUT: Duration = Duration::from_secs(10);

/// How long after the window opens the first check starts.
const FIRST_DELAY: Duration = Duration::from_secs(5);

/// How long the app waits between checks while it runs.
const PERIOD: Duration = Duration::from_hours(24);

/// Zed's `auto_update` setting as the app reads it: whether it may ask GitHub for releases.
///
/// `true` by default; `false` means the app never sends the check's one request, the `GET`
/// of [`LATEST_URL`] with only its `User-Agent` and `Accept` headers.
struct CheckForUpdates(bool);

impl Settings for CheckForUpdates {
    fn from_settings(content: &SettingsContent) -> Self {
        Self(content.auto_update.unwrap_or(true))
    }
}

/// Why a check made no request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Off {
    /// `BORER_NO_UPDATE_CHECK` is `1`.
    Environment,
    /// The person's settings file was refused, did not parse or applied only in part.
    SettingsFile,
    /// Zed's `auto_update` setting is `false`.
    Setting,
    /// This build's version is not a plain release version to compare.
    Version,
}

impl Off {
    /// Returns what the palette's Check for Updates says for it.
    const fn says(self) -> &'static str {
        match self {
            Self::Environment => "Update checks are off: BORER_NO_UPDATE_CHECK is 1",
            Self::SettingsFile => "Update checks are off until the settings file loads in full",
            Self::Setting => "Update checks are off: auto_update is false in the settings file",
            Self::Version => "This build's version cannot be compared with a release",
        }
    }
}

/// The newer release the last check found, the one the person dismissed this run, and the
/// client checks go through.
#[derive(Default)]
struct Updates {
    /// The newer release found, if any.
    found: Option<Release>,
    /// The version whose notice the person closed.
    dismissed: Option<Version>,
    /// The client checks send through; `None` builds Zed's reqwest client off the UI thread.
    http: Option<Arc<dyn HttpClient>>,
    /// The daily checks, while the app runs.
    _daily: Option<Task<()>>,
}

impl Global for Updates {}

/// Starts the daily checks of an interactive window, the first after [`FIRST_DELAY`].
///
/// # Arguments
///
/// * `cx` - Application context.
pub fn start(cx: &mut App) {
    let daily = cx.spawn(async move |cx| {
        cx.background_executor().timer(FIRST_DELAY).await;
        loop {
            if let Ok(check) = cx.update(check) {
                check.await;
            }
            cx.background_executor().timer(PERIOD).await;
        }
    });
    let updates = std::mem::take(cx.default_global::<Updates>());
    cx.set_global(Updates {
        _daily: Some(daily),
        ..updates
    });
}

/// Starts one check, as the environment and the settings allow.
///
/// # Arguments
///
/// * `cx` - Application context.
///
/// # Returns
///
/// The check, which ends in what it found.
///
/// # Errors
///
/// Returns why no request was made, as [`check_with`] says.
fn check(cx: &mut App) -> Result<Task<Outcome>, Off> {
    check_with(std::env::var(OPT_OUT).ok().as_deref(), cx)
}

/// Starts one check off the UI thread unless something forbids it, and records what it
/// finds: a newer release shows the notice, a valid up-to-date answer takes it back.
///
/// # Arguments
///
/// * `opt_out` - The `BORER_NO_UPDATE_CHECK` value, `None` when unset.
/// * `cx` - Application context.
///
/// # Returns
///
/// The check, which ends in what it found.
///
/// # Errors
///
/// Returns [`Off`] naming the opt-out, the settings file that did not load, the setting or
/// the version that forbids a request; none was made.
fn check_with(opt_out: Option<&str>, cx: &mut App) -> Result<Task<Outcome>, Off> {
    CheckForUpdates::register(cx);
    if opted_out(opt_out) {
        return Err(Off::Environment);
    }
    if !crate::app_settings::file_applied(cx) {
        return Err(Off::SettingsFile);
    }
    if !CheckForUpdates::get_global(cx).0 {
        return Err(Off::Setting);
    }
    let running = Version::running().ok_or(Off::Version)?;
    let http = cx.default_global::<Updates>().http.clone();
    let asked = cx.background_spawn(async move {
        let answer = ask(http).await;
        judge(
            running,
            answer
                .as_ref()
                .map(|(status, body)| (*status, body.as_slice())),
        )
    });
    Ok(cx.spawn(async move |cx| {
        let outcome = asked.await;
        cx.update(|cx| record(outcome, cx));
        outcome
    }))
}

/// Shows a newer release's notice, or takes a shown one back on a valid up-to-date answer;
/// an answer that did not come or did not read changes nothing.
///
/// # Arguments
///
/// * `outcome` - What the check found.
/// * `cx` - Application context.
fn record(outcome: Outcome, cx: &mut App) {
    let found = match outcome {
        Outcome::Newer(release) => Some(release),
        Outcome::Current(_) => None,
        Outcome::Unusable(_) | Outcome::Unreachable => return,
    };
    cx.default_global::<Updates>().found = found;
    cx.refresh_windows();
}

/// Returns GitHub's answer to the latest-release request: its status and at most one byte
/// over [`MAX_BODY_BYTES`] of its body.
///
/// # Arguments
///
/// * `http` - The client to send through, `None` to build Zed's reqwest client here.
///
/// # Returns
///
/// `None` when the client cannot be built or no whole answer came: no connection, a
/// transport error or the [`TIMEOUT`].
async fn ask(http: Option<Arc<dyn HttpClient>>) -> Option<(u16, Vec<u8>)> {
    let http: Arc<dyn HttpClient> = match http {
        Some(http) => http,
        None => Arc::new(reqwest_client::ReqwestClient::user_agent(&user_agent(PRODUCT)).ok()?),
    };
    let request = Request::builder()
        .method(Method::GET)
        .uri(LATEST_URL)
        .header("User-Agent", user_agent(PRODUCT))
        .header("Accept", "application/vnd.github+json")
        .follow_redirects(RedirectPolicy::NoFollow)
        .timeout(TIMEOUT)
        .body(AsyncBody::default())
        .ok()?;
    let response = http.send(request).await.ok()?;
    let status = response.status().as_u16();
    let mut body = Vec::new();
    let cap = u64::try_from(MAX_BODY_BYTES).ok()?.saturating_add(1);
    response
        .into_body()
        .take(cap)
        .read_to_end(&mut body)
        .await
        .ok()?;
    Some((status, body))
}

/// Runs a check now, as the palette's Check for Updates asks, and says what it found, or
/// why it asked nothing, in a toast.
///
/// # Arguments
///
/// * `workspace` - The workspace the toast shows in.
/// * `cx` - Workspace context.
pub fn check_now(workspace: &mut Workspace, cx: &mut Context<'_, Workspace>) {
    let id = NotificationId::unique::<Updates>();
    match check(cx) {
        Err(off) => workspace.show_toast(Toast::new(id, off.says()), cx),
        Ok(asked) => cx
            .spawn(async move |workspace, cx| {
                let toast = toast(id, asked.await);
                workspace.update(cx, |workspace, cx| workspace.show_toast(toast, cx))
            })
            .detach_and_log_err(cx),
    }
}

/// Returns the toast that says what a check the person asked for found.
///
/// # Arguments
///
/// * `id` - The toast's id.
/// * `outcome` - What the check found.
fn toast(id: NotificationId, outcome: Outcome) -> Toast {
    match outcome {
        Outcome::Current(running) => {
            Toast::new(id, format!("borer is up to date ({running})")).autohide()
        }
        Outcome::Newer(release) => Toast::new(id, format!("borer {} is out", release.version))
            .on_click("Open the Release Page", move |_, cx| {
                cx.open_url(&release.url());
            }),
        Outcome::Unusable(status) => {
            Toast::new(id, format!("GitHub gave no usable answer (HTTP {status})")).autohide()
        }
        Outcome::Unreachable => Toast::new(id, "Could not reach GitHub").autohide(),
    }
}

/// Returns the title bar's button for the newer release found, unless it was dismissed: a
/// click opens its page in the system's browser, its x hides it for this run.
///
/// # Arguments
///
/// * `cx` - Application context.
///
/// # Returns
///
/// The button, or `None` when no newer release is known or its notice was dismissed.
#[must_use]
pub fn notice(cx: &App) -> Option<AnyElement> {
    let updates = cx.try_global::<Updates>()?;
    let release = updates
        .found
        .filter(|release| updates.dismissed != Some(release.version))?;
    let button = UpdateButton::new(IconName::Download, format!("Update to {}", release.version))
        .tooltip("Opens the release page on GitHub")
        .with_dismiss()
        .on_click(move |_, _, cx| cx.open_url(&release.url()))
        .on_dismiss(move |_, _, cx| {
            cx.default_global::<Updates>().dismissed = Some(release.version);
            cx.refresh_windows();
        });
    Some(button.into_any_element())
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::{Arc, Mutex};
    use std::time::Duration;

    use borer_front::release::{LATEST_URL, Outcome, Release, VERSION, Version};
    use gpui::{BorrowAppContext as _, TestAppContext};
    use http_client::{AsyncBody, FakeHttpClient, RedirectPolicy, RequestTimeout, Response};
    use settings::SettingsStore;

    use super::{Off, Updates, check_with, notice};
    use crate::app_view::tests::init;

    /// One request a fake client saw.
    #[derive(Debug)]
    struct Sent {
        /// Its method and address.
        line: (String, String),
        /// Every header, name and value.
        headers: Vec<(String, String)>,
        /// The redirects it allows.
        redirects: Option<RedirectPolicy>,
        /// How long it may take.
        timeout: Option<Duration>,
    }

    /// The requests a fake client saw.
    type Seen = Arc<Mutex<Vec<Sent>>>;

    /// What the fake client answers: a status and a body.
    type Answer = Arc<Mutex<(u16, String)>>;

    /// Starts the app's settings with `settings` as the person's file, and routes checks
    /// through a fake client that answers 200 with `body` until told otherwise.
    ///
    /// # Returns
    ///
    /// What the fake client saw, and its answer to change.
    fn setup(settings: &str, body: &str, cx: &mut TestAppContext) -> (Seen, Answer) {
        init(cx);
        let seen = Seen::default();
        let answer: Answer = Arc::new(Mutex::new((200, body.to_owned())));
        let (log, given) = (seen.clone(), answer.clone());
        let http = FakeHttpClient::create(move |request| {
            let headers = request
                .headers()
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_str().unwrap_or("").to_owned()))
                .collect();
            log.lock().unwrap().push(Sent {
                line: (request.method().to_string(), request.uri().to_string()),
                headers,
                redirects: request.extensions().get::<RedirectPolicy>().cloned(),
                timeout: request.extensions().get::<RequestTimeout>().map(|t| t.0),
            });
            let (status, body) = given.lock().unwrap().clone();
            async move {
                Ok(Response::builder()
                    .status(status)
                    .body(AsyncBody::from(body))?)
            }
        });
        cx.update(|cx| {
            cx.update_global(|store: &mut SettingsStore, cx| {
                drop(store.set_user_settings(settings, cx));
            });
            cx.default_global::<Updates>().http = Some(http);
        });
        (seen, answer)
    }

    /// Runs one check and returns what it found.
    ///
    /// # Errors
    ///
    /// Returns why no request was made.
    async fn checked(cx: &mut TestAppContext) -> Result<Outcome, Off> {
        let task = cx.update(|cx| check_with(None, cx))?;
        Ok(task.await)
    }

    /// Returns the newer release the app holds and whether the title bar shows it.
    fn shown(cx: &mut TestAppContext) -> (Option<Release>, bool) {
        cx.update(|cx| (cx.default_global::<Updates>().found, notice(cx).is_some()))
    }

    /// The release the tests find newer than any build.
    const NEWER: Release = Release {
        version: Version {
            major: 9,
            minor: 0,
            patch: 0,
        },
    };

    /// No request is made with a settings file that did not parse, even one that says
    /// nothing about updates, with `auto_update` false, or with `BORER_NO_UPDATE_CHECK=1`.
    #[gpui::test]
    async fn nothing_is_sent_when_checks_are_off(cx: &mut TestAppContext) {
        let (seen, _) = setup(r#"{"theme": "borer dark""#, "{}", cx);
        assert_eq!(checked(cx).await, Err(Off::SettingsFile));
        cx.update(|cx| {
            cx.update_global(|store: &mut SettingsStore, cx| {
                drop(store.set_user_settings(r#"{"auto_update": false}"#, cx));
            });
        });
        assert_eq!(checked(cx).await, Err(Off::Setting));
        let opted = cx.update(|cx| check_with(Some("1"), cx).err());
        assert_eq!(opted, Some(Off::Environment));
        assert!(seen.lock().unwrap().is_empty());
    }

    /// A newer release shows the notice at its canonical page, whatever page the answer
    /// names; the request carries only the two headers, follows no redirect and gives up
    /// after ten seconds.
    #[gpui::test]
    async fn a_newer_release_shows_the_notice(cx: &mut TestAppContext) {
        let body = r#"{"tag_name":"v9.0.0","html_url":"https://evil.example/x","draft":false}"#;
        let (seen, _) = setup("{}", body, cx);
        assert_eq!(checked(cx).await, Ok(Outcome::Newer(NEWER)));
        assert_eq!(shown(cx), (Some(NEWER), true));
        assert_eq!(
            NEWER.url(),
            "https://github.com/imjustprism/borer/releases/tag/v9.0.0"
        );
        let seen = seen.lock().unwrap();
        let sent = &seen[0];
        assert_eq!(sent.line, ("GET".to_owned(), LATEST_URL.to_owned()));
        assert_eq!(sent.redirects, Some(RedirectPolicy::NoFollow));
        assert_eq!(sent.timeout, Some(Duration::from_secs(10)));
        let want = [
            ("user-agent".to_owned(), format!("borer-app/{VERSION}")),
            (
                "accept".to_owned(),
                "application/vnd.github+json".to_owned(),
            ),
        ];
        assert_eq!(sent.headers.as_slice(), want.as_slice());
    }

    /// An equal, older or malformed answer shows no notice; a valid up-to-date answer takes
    /// a shown one back, an unusable one leaves it, and a redirect is unusable.
    #[gpui::test]
    async fn only_a_newer_release_shows_the_notice(cx: &mut TestAppContext) {
        let same = format!(r#"{{"tag_name":"v{VERSION}"}}"#);
        let (_, answer) = setup("{}", &same, cx);
        let answers = [
            (
                200,
                same.clone(),
                Outcome::Current(Version::running().unwrap()),
            ),
            (
                200,
                r#"{"tag_name":"v0.0.1"}"#.to_owned(),
                Outcome::Current(Version::running().unwrap()),
            ),
            (
                200,
                r#"{"tag_name":"v9"}"#.to_owned(),
                Outcome::Unusable(200),
            ),
            (302, String::new(), Outcome::Unusable(302)),
        ];
        for (status, body, want) in answers {
            *answer.lock().unwrap() = (status, body.clone());
            assert_eq!(checked(cx).await, Ok(want), "{status} {body}");
            assert_eq!(shown(cx), (None, false), "{status} {body}");
        }
        for (status, body, kept) in [
            (200, "not json", true),
            (302, "", true),
            (200, &*same, false),
        ] {
            cx.update(|cx| cx.default_global::<Updates>().found = Some(NEWER));
            *answer.lock().unwrap() = (status, body.to_owned());
            assert!(checked(cx).await.is_ok());
            let held = kept.then_some(NEWER);
            assert_eq!(shown(cx), (held, kept), "{status} {body}");
        }
    }
}
