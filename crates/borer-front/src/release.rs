//! borer's releases on GitHub as both front ends read them.
//!
//! It holds this build's [`VERSION`] and the version the CLI's `--version` and the app's
//! About show ([`shown_version`]), the repository releases come from ([`REPO`]), the one
//! opt-out of every update check ([`OPT_OUT`]), the [`Version`] a tag spells, and
//! [`judge`], what GitHub's latest-release answer ([`LATEST_URL`]) means to a build.
//!
//! The answer is untrusted: only its status, `tag_name`, `draft` and `prerelease` are read,
//! from at most [`MAX_BODY_BYTES`], a tag counts only as exactly `v<major>.<minor>.<patch>`,
//! and a release's page is built from those three numbers ([`Release::url`]), never taken
//! from the answer. The CLI keeps reading tags as it always has ([`Version::parse_tag`]);
//! the app reads only plain ones ([`Version::parse`]).

/// This build's package version, the workspace's, which every crate of a release shares.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The commit this build is from, twelve hex digits, or `unknown`.
pub const COMMIT: &str = env!("BORER_COMMIT");

/// `git describe --long` of this build against the release tags, empty when git did not say.
pub const DESCRIBE: &str = env!("BORER_DESCRIBE");

/// The repository releases are published from, `owner/name` on GitHub.
pub const REPO: &str = "imjustprism/borer";

/// The environment variable that turns every update check off when set to `1`.
pub const OPT_OUT: &str = "BORER_NO_UPDATE_CHECK";

/// The GitHub API's latest release of [`REPO`].
pub const LATEST_URL: &str = "https://api.github.com/repos/imjustprism/borer/releases/latest";

/// What every release page's address starts with, [`REPO`]'s releases on GitHub.
pub const RELEASES_PREFIX: &str = concat!(env!("CARGO_PKG_REPOSITORY"), "/releases/");

/// Most bytes of an answer the check reads; a longer one is not read.
pub const MAX_BODY_BYTES: usize = 256 << 10;

/// Returns this build's version as `borer --version` and the app's About show it.
#[must_use]
pub fn shown_version() -> String {
    version_of(VERSION, DESCRIBE)
}

/// Spells a build's version from its package version and its `git describe --long` against
/// the release tags.
///
/// A build of the tag `v<version>` is that version; any other (commits past the tag,
/// another tag, or no tag known) is `<version>-dev`, with the description when there is
/// one, so a report or `update --check` can tell a development build from the release it
/// started from.
///
/// # Arguments
///
/// * `version` - The package version.
/// * `describe` - `v<tag>-<commits>-g<hash>`, or empty when git did not say.
///
/// # Returns
///
/// The version to print.
#[must_use]
pub fn version_of(version: &str, describe: &str) -> String {
    if describe.starts_with(&format!("v{version}-0-g")) {
        return version.to_owned();
    }
    if describe.is_empty() {
        format!("{version}-dev")
    } else {
        format!("{version}-dev ({describe})")
    }
}

/// Returns the `User-Agent` a front end sends to GitHub: `product/` and this build's
/// [`VERSION`], such as `borer-app/0.3.1`.
///
/// # Arguments
///
/// * `product` - The binary's name, `borer` or `borer-app`.
#[must_use]
pub fn user_agent(product: &str) -> String {
    format!("{product}/{VERSION}")
}

/// Returns whether [`OPT_OUT`]'s value turns update checks off: only `1` does.
///
/// # Arguments
///
/// * `value` - The variable's value, `None` when unset.
#[must_use]
pub fn opted_out(value: Option<&str>) -> bool {
    value == Some("1")
}

/// A release's version, `major.minor.patch`, ordered as semantic versions without a
/// pre-release are.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Version {
    /// The major number.
    pub major: u64,
    /// The minor number.
    pub minor: u64,
    /// The patch number.
    pub patch: u64,
}

impl Version {
    /// Returns the version `text` spells as exactly three dot-separated decimal numbers,
    /// none with a sign or a leading zero.
    ///
    /// # Arguments
    ///
    /// * `text` - The version, such as `0.3.1`.
    ///
    /// # Returns
    ///
    /// `None` when `text` is anything else or a number overflows a `u64`.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Self::three(text, plain_number)
    }

    /// Returns the version a tag or version starts with, as the CLI has always read one:
    /// surrounding space and leading `v`s dropped, anything from a `-` or `+` on ignored.
    ///
    /// # Arguments
    ///
    /// * `text` - The tag or version, such as `v0.10.0-beta.1`.
    ///
    /// # Returns
    ///
    /// `None` when what is left is not three numbers that fit a `u64`.
    #[must_use]
    pub fn parse_tag(text: &str) -> Option<Self> {
        let core = text
            .trim()
            .trim_start_matches('v')
            .split(['-', '+'])
            .next()?;
        Self::three(core, |part| part.parse().ok())
    }

    /// Returns this build's version, `None` if [`VERSION`] is not plain.
    #[must_use]
    pub fn running() -> Option<Self> {
        Self::parse(VERSION)
    }

    /// Returns the version `text` spells as three dot-separated parts, each read by
    /// `number`.
    ///
    /// # Arguments
    ///
    /// * `text` - The version.
    /// * `number` - Reads one part, `None` when it is not a number.
    ///
    /// # Returns
    ///
    /// `None` when there are not exactly three parts or one does not read.
    fn three(text: &str, number: fn(&str) -> Option<u64>) -> Option<Self> {
        let mut parts = text.split('.');
        let version = Self {
            major: number(parts.next()?)?,
            minor: number(parts.next()?)?,
            patch: number(parts.next()?)?,
        };
        parts.next().is_none().then_some(version)
    }
}

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "v{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// Returns whether `tag` names a release newer than this build, both read as
/// [`Version::parse_tag`] reads them.
///
/// # Arguments
///
/// * `tag` - The release's tag.
#[must_use]
pub fn is_newer(tag: &str) -> bool {
    matches!(
        (Version::parse_tag(tag), Version::parse_tag(VERSION)),
        (Some(theirs), Some(ours)) if theirs > ours
    )
}

/// Returns the number `part` spells in decimal digits without a leading zero.
///
/// # Arguments
///
/// * `part` - One part of a version.
///
/// # Returns
///
/// `None` for anything else, or a number over [`u64::MAX`].
fn plain_number(part: &str) -> Option<u64> {
    let digits = part.bytes().all(|b| b.is_ascii_digit());
    let padded = part.len() > 1 && part.starts_with('0');
    (digits && !padded).then(|| part.parse().ok()).flatten()
}

/// A published release newer than the running build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Release {
    /// Its version.
    pub version: Version,
}

impl Release {
    /// Returns the release's page on GitHub, built from its three numbers alone.
    #[must_use]
    pub fn url(&self) -> String {
        format!("{RELEASES_PREFIX}tag/{}", self.version)
    }
}

/// What a check found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// The latest release is not newer than the running build, whose version this is.
    Current(Version),
    /// A newer release.
    Newer(Release),
    /// GitHub answered with this HTTP status, but not with a release the check could read.
    Unusable(u16),
    /// The request got no answer: no connection, a transport error or a timeout.
    Unreachable,
}

/// The fields of GitHub's latest-release answer the check reads; every other is ignored.
#[derive(serde::Deserialize)]
struct Latest {
    /// The release's tag, `v<major>.<minor>.<patch>` for a release the check counts.
    tag_name: String,
    /// Whether it is a pre-release, such as the rolling `dev-build`; never newer.
    #[serde(default)]
    prerelease: bool,
    /// Whether it is an unpublished draft; never newer.
    #[serde(default)]
    draft: bool,
}

/// Returns what GitHub's answer to the latest-release request means to a build at
/// `running`.
///
/// # Arguments
///
/// * `running` - The running build's version.
/// * `answer` - The answer's HTTP status and body, `None` when no answer came.
///
/// # Returns
///
/// [`Outcome::Newer`] for a published release tagged `v<major>.<minor>.<patch>` above
/// `running`, [`Outcome::Current`] for any other published release, draft or pre-release,
/// [`Outcome::Unusable`] for a status other than 200 or a body that is over
/// [`MAX_BODY_BYTES`], not GitHub's JSON or tagged otherwise, and [`Outcome::Unreachable`]
/// for no answer.
#[must_use]
pub fn judge(running: Version, answer: Option<(u16, &[u8])>) -> Outcome {
    let Some((status, body)) = answer else {
        return Outcome::Unreachable;
    };
    let read = (status == 200 && body.len() <= MAX_BODY_BYTES)
        .then(|| serde_json::from_slice::<Latest>(body).ok())
        .flatten()
        .and_then(|latest| Some((Version::parse(latest.tag_name.strip_prefix('v')?)?, latest)));
    match read {
        None => Outcome::Unusable(status),
        Some((version, latest)) if !latest.draft && !latest.prerelease && version > running => {
            Outcome::Newer(Release { version })
        }
        Some(_) => Outcome::Current(running),
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{
        LATEST_URL, MAX_BODY_BYTES, Outcome, RELEASES_PREFIX, REPO, Release, Version, judge,
        opted_out,
    };

    /// The version the tests run as.
    const RUNNING: Version = Version {
        major: 0,
        minor: 3,
        patch: 1,
    };

    /// Returns a latest-release answer for `tag` whose page claims to be `url`.
    fn answer(tag: &str, url: &str, prerelease: bool, draft: bool) -> Vec<u8> {
        serde_json::json!({
            "tag_name": tag,
            "html_url": url,
            "prerelease": prerelease,
            "draft": draft,
            "assets": [],
        })
        .to_string()
        .into_bytes()
    }

    /// Returns what the check makes of a published release tagged `tag`.
    fn released(tag: &str) -> Outcome {
        let url = format!("https://github.com/imjustprism/borer/releases/tag/{tag}");
        judge(RUNNING, Some((200, &answer(tag, &url, false, false))))
    }

    /// The addresses are the repository's, as the Cargo metadata names it, and only `1`
    /// opts out.
    #[test]
    fn the_addresses_name_the_repository() {
        assert_eq!(
            LATEST_URL,
            format!("https://api.github.com/repos/{REPO}/releases/latest")
        );
        assert_eq!(
            RELEASES_PREFIX,
            format!("https://github.com/{REPO}/releases/")
        );
        assert!(Version::running().is_some());
        assert!(opted_out(Some("1")));
        for kept in [None, Some(""), Some("0"), Some("true")] {
            assert!(!opted_out(kept), "{kept:?}");
        }
    }

    /// Versions parse only as three plain decimal numbers that fit a `u64`; a tag as the
    /// CLI reads it may carry a `v`, space and a suffix.
    #[test]
    fn versions_parse_only_when_plain() {
        assert_eq!(Version::parse("0.3.1"), Some(RUNNING));
        let max = format!("{0}.{0}.{0}", u64::MAX);
        assert!(Version::parse(&max).is_some());
        for bad in [
            "",
            "0.3",
            "0.3.1.4",
            "0.3.1-rc1",
            "+1.2.3",
            "01.2.3",
            "1..3",
            " 1.2.3",
            "1.2.3 ",
            "1.2.18446744073709551616",
            "1.2.x",
            "\u{0661}.2.3",
        ] {
            assert_eq!(Version::parse(bad), None, "{bad:?}");
        }
        assert!(Version::parse("0.10.0") > Version::parse("0.9.9"));
        assert_eq!(Version::parse_tag(" v0.3.1-rc1 "), Some(RUNNING));
        assert_eq!(Version::parse_tag("v00.3.1+x"), Some(RUNNING));
        assert_eq!(Version::parse_tag("latest"), None);
    }

    /// A newer release is found and opens its canonical page, the same or an older one is
    /// current, whatever page the answer claims.
    #[test]
    fn newer_same_and_older_releases() {
        let newer = Release {
            version: Version {
                major: 0,
                minor: 3,
                patch: 2,
            },
        };
        assert_eq!(released("v0.3.2"), Outcome::Newer(newer));
        assert_eq!(
            newer.url(),
            "https://github.com/imjustprism/borer/releases/tag/v0.3.2"
        );
        assert_eq!(released("v0.3.1"), Outcome::Current(RUNNING));
        assert_eq!(released("v0.2.9"), Outcome::Current(RUNNING));
        let huge = format!("v{0}.0.0", u64::MAX);
        assert!(matches!(released(&huge), Outcome::Newer(_)));
        for hostile in [
            "https://github.com/imjustprism/borer/releases/../../../evil/x/releases/download/v1/borer-app.zip",
            "https://evil.example/imjustprism/borer/releases/tag/v0.3.2",
            "javascript:alert(1)",
        ] {
            let body = answer("v0.3.2", hostile, false, false);
            let Outcome::Newer(release) = judge(RUNNING, Some((200, &body))) else {
                panic!("{hostile}");
            };
            assert_eq!(release.url(), newer.url(), "{hostile}");
        }
    }

    /// Drafts and pre-releases, the rolling `dev-build` among them, are never newer.
    #[test]
    fn drafts_and_prereleases_are_not_newer() {
        let url = "https://github.com/imjustprism/borer/releases/tag/v9.0.0";
        let current = Outcome::Current(RUNNING);
        let prerelease = answer("v9.0.0", url, true, false);
        assert_eq!(judge(RUNNING, Some((200, &prerelease))), current);
        let draft = answer("v9.0.0", url, false, true);
        assert_eq!(judge(RUNNING, Some((200, &draft))), current);
    }

    /// A malformed tag, a status other than 200 (a redirect among them), a body that is too
    /// long, not UTF-8 or not GitHub's JSON is unusable, with its status; no answer is
    /// unreachable.
    #[test]
    fn anything_unexpected_is_unusable() {
        for tag in [
            "dev-build",
            "0.4.0",
            "v0.4",
            "v0.4.0-rc1",
            "v99999999999999999999.0.0",
        ] {
            assert_eq!(released(tag), Outcome::Unusable(200), "{tag:?}");
        }
        let fine = answer("v1.0.0", "", false, false);
        for status in [301, 302, 403, 404, 500] {
            let got = judge(RUNNING, Some((status, &fine)));
            assert_eq!(got, Outcome::Unusable(status));
        }
        let mut long = fine;
        long.pop();
        long.resize(MAX_BODY_BYTES - 1, b' ');
        long.push(b'}');
        assert!(matches!(
            judge(RUNNING, Some((200, &long))),
            Outcome::Newer(_)
        ));
        long.insert(0, b' ');
        assert_eq!(judge(RUNNING, Some((200, &long))), Outcome::Unusable(200));
        for body in [
            &b"\xff\xfe{}"[..],
            b"",
            b"null",
            b"[]",
            b"{\"tag_name\": 3}",
            b"{\"tag_name\":\"v1.0.0\xff\"}",
        ] {
            let got = judge(RUNNING, Some((200, body)));
            assert_eq!(got, Outcome::Unusable(200), "{body:?}");
        }
        assert_eq!(judge(RUNNING, None), Outcome::Unreachable);
    }
}
