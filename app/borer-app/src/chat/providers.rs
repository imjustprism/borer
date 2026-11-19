//! The model providers the chat offers, each a thin adapter borer owns over a Zed API crate.
//!
//! An adapter calls the crate's request converter, stream and event mapper: `anthropic`,
//! `google_ai`, and `open_ai`'s chat completions, which one adapter speaks to `OpenAI`,
//! `OpenRouter`, Ollama and LM Studio.
//!
//! Nothing is registered anywhere: a provider is asked for its models only when the person
//! picks it, through the one HTTP client the chat hands providers ([`ChatHttp`]); the app's
//! own HTTP client stays blocked. Keys come from the provider's environment variable or the
//! system keychain, under the chat's own entry for the provider's URL ([`key_entry`]).

use std::sync::Arc;

use anthropic::completion::{AnthropicEventMapper, AnthropicPromptCacheMode, into_anthropic};
use credentials_provider::CredentialsProvider;
use futures::{AsyncReadExt as _, FutureExt as _, StreamExt as _, future::BoxFuture};
use google_ai::completion::{GoogleEventMapper, into_google};
use gpui::{App, AsyncApp, Global, SharedString};
use http_client::http::HeaderValue;
use http_client::{
    AsyncBody, CustomHeaders, Host, HttpClient, Method, RedirectPolicy, Request, Response, Url,
};
use language_model::chat_completion::ChatCompletionEventMapper;
use language_model::{
    LanguageModel, LanguageModelClient, LanguageModelCompletionError,
    LanguageModelCompletionStream, LanguageModelProviderId, LanguageModelProviderName,
    LanguageModelRequest, LanguageModelToolChoiceSupport,
};
use open_ai::completion::{ChatCompletionMaxTokensParameter, into_open_ai};

use super::thread::Chosen;

/// Most models of a provider kept from its list.
const MODELS_MAX: usize = 200;

/// The context window assumed for a model an OpenAI-compatible list gives no size for.
const OPEN_AI_WINDOW: u64 = 128_000;

/// A provider the chat offers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Offered {
    /// Anthropic's API, for Claude, with an API key.
    Anthropic,
    /// The `OpenAI` API, for GPT, with an API key.
    OpenAi,
    /// Google AI's API, for Gemini, with an API key.
    Google,
    /// `OpenRouter`, which carries many vendors' models, with an API key.
    OpenRouter,
    /// An Ollama server, on this machine unless its URL in settings says otherwise.
    Ollama,
    /// An LM Studio server, on this machine unless its URL in settings says otherwise.
    LmStudio,
}

impl Offered {
    /// Every provider the chat offers, in the picker's order.
    pub const ALL: [Self; 6] = [
        Self::Anthropic,
        Self::OpenAi,
        Self::Google,
        Self::OpenRouter,
        Self::Ollama,
        Self::LmStudio,
    ];

    /// Returns what the picker and the change feed call the provider.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::Anthropic => "Claude",
            Self::OpenAi => "GPT",
            Self::Google => "Gemini",
            Self::OpenRouter => "OpenRouter",
            Self::Ollama => "Ollama",
            Self::LmStudio => "LM Studio",
        }
    }

    /// Returns the environment variable that holds the provider's key, `None` for a server
    /// that takes none.
    #[must_use]
    pub const fn key_var(self) -> Option<&'static str> {
        match self {
            Self::Anthropic => Some("ANTHROPIC_API_KEY"),
            Self::OpenAi => Some("OPENAI_API_KEY"),
            Self::Google => Some("GEMINI_API_KEY"),
            Self::OpenRouter => Some("OPENROUTER_API_KEY"),
            Self::Ollama | Self::LmStudio => None,
        }
    }

    /// Returns the provider's id, which the request converters key provider state with.
    const fn id(self) -> LanguageModelProviderId {
        LanguageModelProviderId::new(match self {
            Self::Anthropic => "anthropic",
            Self::OpenAi => "openai",
            Self::Google => "google",
            Self::OpenRouter => "openrouter",
            Self::Ollama => "ollama",
            Self::LmStudio => "lmstudio",
        })
    }

    /// Returns the provider's URL: its API's, or for Ollama and LM Studio the one the
    /// settings' `language_models` section names (Ollama's with `/v1`, where it speaks
    /// `OpenAI`'s chat completions), else the default.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context holding the settings.
    #[must_use]
    pub fn url(self, cx: &App) -> SharedString {
        let models = cx
            .try_global::<settings::SettingsStore>()
            .and_then(|store| store.merged_settings().language_models.as_ref());
        let set = |url: Option<&String>| url.filter(|u| !u.trim().is_empty()).cloned();
        let url = match self {
            Self::Anthropic => anthropic::ANTHROPIC_API_URL.to_owned(),
            Self::OpenAi => open_ai::OPEN_AI_API_URL.to_owned(),
            Self::Google => google_ai::API_URL.to_owned(),
            Self::OpenRouter => "https://openrouter.ai/api/v1".to_owned(),
            Self::Ollama => {
                let set = set(models.and_then(|m| m.ollama.as_ref()?.api_url.as_ref()));
                let base = set.unwrap_or_else(|| "http://localhost:11434".to_owned());
                format!("{}/v1", base.trim_end_matches('/'))
            }
            Self::LmStudio => set(models.and_then(|m| m.lmstudio.as_ref()?.api_url.as_ref()))
                .unwrap_or_else(|| "http://localhost:1234/api/v0".to_owned()),
        };
        url.trim_end_matches('/').to_owned().into()
    }
}

/// Where a provider's requests go.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Endpoint {
    /// The provider.
    pub offered: Offered,
    /// Its base URL, with no trailing slash.
    pub url: SharedString,
}

impl Endpoint {
    /// Returns where `offered`'s requests go now ([`Offered::url`]).
    ///
    /// # Arguments
    ///
    /// * `offered` - The provider.
    /// * `cx` - Application context holding the settings.
    #[must_use]
    pub fn of(offered: Offered, cx: &App) -> Self {
        Self {
            offered,
            url: offered.url(cx),
        }
    }

    /// Returns the URL's host and port as the person reads it, the whole URL when it does
    /// not parse; it says where requests go, not whether they stay on this machine
    /// ([`super::thread::Chosen::is_local`] says that).
    #[must_use]
    pub fn host(&self) -> String {
        Url::parse(&self.url).ok().map_or_else(
            || self.url.to_string(),
            |url| match (url.host_str(), url.port()) {
                (Some(host), Some(port)) => format!("{host}:{port}"),
                (Some(host), None) => host.to_owned(),
                (None, _) => self.url.to_string(),
            },
        )
    }

    /// Returns whether requests stay on this machine: the URL's host is `localhost` or a
    /// loopback address. A URL that does not parse is not local.
    #[must_use]
    pub fn is_local(&self) -> bool {
        Url::parse(&self.url).is_ok_and(|url| match url.host() {
            Some(Host::Domain(name)) => name.eq_ignore_ascii_case("localhost"),
            Some(Host::Ipv4(ip)) => ip.is_loopback(),
            Some(Host::Ipv6(ip)) => ip.is_loopback(),
            None => false,
        })
    }
}

/// How a model's requests are written and its stream read.
#[derive(Debug, Clone)]
enum Wire {
    /// Anthropic's messages API, with the model as its list gave it.
    Anthropic(anthropic::Model),
    /// Google AI's `streamGenerateContent`, with the model as its list gave it.
    Google(google_ai::Model),
    /// `OpenAI`'s chat completions.
    OpenAi,
}

/// The chat's HTTP client as a provider's requests go through it: none follows a redirect.
///
/// So no key or transcript is re-sent to another host; a redirect is an error naming the
/// host that answered it.
struct NoRedirects(Arc<dyn HttpClient>);

impl HttpClient for NoRedirects {
    fn user_agent(&self) -> Option<&HeaderValue> {
        self.0.user_agent()
    }

    fn proxy(&self) -> Option<&Url> {
        self.0.proxy()
    }

    fn send(
        &self,
        mut request: Request<AsyncBody>,
    ) -> BoxFuture<'static, anyhow::Result<Response<AsyncBody>>> {
        request.extensions_mut().insert(RedirectPolicy::NoFollow);
        let host = borer_engine::text::one_line(request.uri().host().unwrap_or_default());
        let sent = self.0.send(request);
        async move {
            let response = sent.await?;
            if response.status().is_redirection() {
                let to = response
                    .headers()
                    .get("location")
                    .and_then(|to| to.to_str().ok())
                    .map(borer_engine::text::one_line)
                    .unwrap_or_default();
                anyhow::bail!(
                    "{host} answered {} with a redirect to {to}; the chat follows none, so nothing more was sent",
                    response.status()
                );
            }
            Ok(response)
        }
        .boxed()
    }
}

/// One model of a provider, sending its requests over the chat's HTTP client.
struct Remote {
    /// Where its requests go.
    endpoint: Endpoint,
    /// The key it sends, empty for a server that takes none.
    key: Arc<str>,
    /// The chat's HTTP client.
    http: Arc<dyn HttpClient>,
    /// How its requests are written.
    wire: Wire,
}

impl LanguageModelClient for Remote {
    fn stream_completion(
        &self,
        model: &LanguageModel,
        request: LanguageModelRequest,
        cx: &AsyncApp,
    ) -> BoxFuture<'static, Result<LanguageModelCompletionStream, LanguageModelCompletionError>>
    {
        let (http, key, url) = (
            self.http.clone(),
            self.key.clone(),
            self.endpoint.url.clone(),
        );
        let offered = self.endpoint.offered;
        let (id, name) = (
            offered.id(),
            LanguageModelProviderName::new(offered.label()),
        );
        let model_id = model.id.0.to_string();
        let headers = CustomHeaders::default();
        let executor = cx.background_executor().clone();
        let wire = self.wire.clone();
        async move {
            let events = match wire {
                Wire::Anthropic(model) => {
                    let request = into_anthropic(
                        request,
                        model.id.clone(),
                        model.default_temperature,
                        model.max_output_tokens,
                        model.mode.clone(),
                        AnthropicPromptCacheMode::Automatic,
                        &id,
                    )?;
                    let beta = model.beta_headers();
                    let events =
                        anthropic::stream_completion(&*http, &url, &key, request, beta, &headers)
                            .await?;
                    AnthropicEventMapper::new(name, id)
                        .map_stream(events)
                        .boxed()
                }
                Wire::Google(model) => {
                    let request = into_google(request, model.id.clone(), model.mode)?;
                    let events =
                        google_ai::stream_generate_content(&*http, &url, &key, request, &headers)
                            .await?;
                    GoogleEventMapper::new().map_stream(events).boxed()
                }
                Wire::OpenAi => {
                    let request = into_open_ai(
                        request,
                        &model_id,
                        false,
                        offered == Offered::OpenAi,
                        None,
                        ChatCompletionMaxTokensParameter::MaxCompletionTokens,
                        None,
                        false,
                    )?;
                    let events = open_ai::stream_completion(
                        &*http,
                        offered.label(),
                        &url,
                        &key,
                        request,
                        &headers,
                    )
                    .await?;
                    ChatCompletionEventMapper::new().map_stream(events).boxed()
                }
            };
            Ok(language_model::stream_in_background(events, executor))
        }
        .boxed()
    }
}

/// Returns a model of `endpoint`'s provider as the picker lists it, able to call tools.
pub(crate) fn listed(endpoint: &Endpoint, id: &str, name: String, window: u64) -> LanguageModel {
    let offered = endpoint.offered;
    LanguageModel {
        supports_tools: true,
        supports_streaming_tools: true,
        tool_choice_support: LanguageModelToolChoiceSupport {
            auto: true,
            any: true,
            none: true,
        },
        ..LanguageModel::new(
            id.to_owned().into(),
            name.into(),
            offered.id(),
            LanguageModelProviderName::new(offered.label()),
            format!("{}/{id}", offered.id().0),
            window,
        )
    }
}

/// Asks `endpoint`'s provider for its models, at most [`MODELS_MAX`], each ready to send
/// with the provider's key ([`read_key`]).
///
/// # Arguments
///
/// * `endpoint` - The provider and its URL.
/// * `http` - The chat's HTTP client.
/// * `cx` - Async context reading the key.
///
/// # Errors
///
/// Returns that a provider that takes a key has none, the keychain's error, the
/// provider's refusal, or that its list did not read.
pub async fn models(
    endpoint: Endpoint,
    http: Arc<dyn HttpClient>,
    cx: &AsyncApp,
) -> anyhow::Result<Vec<Chosen>> {
    let http: Arc<dyn HttpClient> = Arc::new(NoRedirects(http));
    let offered = endpoint.offered;
    let key: Arc<str> = match (
        read_key(offered, &endpoint.url, cx).await?,
        offered.key_var(),
    ) {
        (Some(key), _) => key,
        (None, None) => "".into(),
        (None, Some(var)) => anyhow::bail!(
            "{} has no key: save one, or set {var}; nothing was sent",
            offered.label()
        ),
    };
    let headers = CustomHeaders::default();
    let url = endpoint.url.to_string();
    let listed: Vec<(LanguageModel, Wire)> = match endpoint.offered {
        Offered::Anthropic => anthropic::list_models(&*http, &url, &key, &headers)
            .await
            .map_err(|e| anyhow::anyhow!("{e:?}"))?
            .into_iter()
            .map(|m| {
                let model = listed(&endpoint, &m.id, m.display_name.clone(), m.max_input_tokens);
                (model, Wire::Anthropic(m))
            })
            .collect(),
        Offered::Google => google_ai::list_models(&*http, &url, &key, &headers)
            .await?
            .into_iter()
            .map(|m| {
                let model = listed(&endpoint, &m.id, m.display_name.clone(), m.max_input_tokens);
                (model, Wire::Google(m))
            })
            .collect(),
        Offered::OpenAi | Offered::OpenRouter | Offered::Ollama | Offered::LmStudio => {
            open_ai_models(&*http, &url, &key)
                .await?
                .into_iter()
                .map(|id| {
                    let model = listed(&endpoint, &id, id.clone(), OPEN_AI_WINDOW);
                    (model, Wire::OpenAi)
                })
                .collect()
        }
    };
    Ok(listed
        .into_iter()
        .take(MODELS_MAX)
        .map(|(model, wire)| {
            let client = Remote {
                endpoint: endpoint.clone(),
                key: key.clone(),
                http: http.clone(),
                wire,
            };
            Chosen {
                client: Arc::new(client),
                model,
                endpoint: endpoint.clone(),
            }
        })
        .collect())
}

/// Returns the model ids an OpenAI-compatible server lists at `{url}/models`.
///
/// # Errors
///
/// Returns the server's status and words when it refuses, or that its list did not read.
async fn open_ai_models(
    http: &dyn HttpClient,
    url: &str,
    key: &str,
) -> anyhow::Result<Vec<String>> {
    #[derive(serde::Deserialize)]
    struct Entry {
        id: String,
    }
    #[derive(serde::Deserialize)]
    struct Listing {
        data: Vec<Entry>,
    }
    let request = Request::builder()
        .method(Method::GET)
        .uri(format!("{url}/models"))
        .header("Authorization", format!("Bearer {}", key.trim()))
        .body(AsyncBody::default())?;
    let mut response = http.send(request).await?;
    let mut body = String::new();
    response.body_mut().read_to_string(&mut body).await?;
    anyhow::ensure!(
        response.status().is_success(),
        "{url}/models answered {}: {}",
        response.status(),
        borer_engine::text::one_line(&body)
    );
    let listing: Listing = serde_json::from_str(&body)?;
    Ok(listing.data.into_iter().map(|e| e.id).collect())
}

/// Returns `offered`'s key: from its environment variable, else from the system keychain
/// under `url`; `None` when neither holds one.
///
/// # Errors
///
/// Returns the keychain's error, or that the key it holds is not UTF-8.
pub async fn read_key(
    offered: Offered,
    url: &str,
    cx: &AsyncApp,
) -> anyhow::Result<Option<Arc<str>>> {
    let from_env = offered
        .key_var()
        .and_then(|var| language_model::EnvVar::new(var.into()).value);
    if let Some(key) = from_env {
        return Ok(Some(key.into()));
    }
    let keys = cx.update(|cx| credentials(cx));
    let read = language_model::read_credentials(keys.as_ref(), &key_entry(url), cx).await?;
    read.map(|(_, bytes)| Ok(String::from_utf8(bytes)?.into()))
        .transpose()
}

/// Prefix of the keychain entry the chat keeps a provider's key under, so the app never
/// reads, overwrites or deletes another program's entry for the same URL.
pub const KEY_ENTRY: &str = "borer-app/chat-key/";

/// Returns the keychain entry the chat keeps the key for the provider at `url` under:
/// [`KEY_ENTRY`] and the URL. On Windows Zed's keychain provider names it
/// `zed:url=borer-app/chat-key/<url>`.
#[must_use]
pub fn key_entry(url: &str) -> String {
    format!("{KEY_ENTRY}{url}")
}

/// Keeps `key` in the system keychain under the chat's entry for `url` ([`key_entry`]), or
/// deletes the key there for `None`.
///
/// # Errors
///
/// Returns the keychain's error.
pub async fn save_key(url: &str, key: Option<&str>, cx: &AsyncApp) -> anyhow::Result<()> {
    let keys = cx.update(|cx| credentials(cx));
    let entry = key_entry(url);
    match key {
        Some(key) => {
            keys.write_credentials(&entry, "Bearer", key.as_bytes(), cx)
                .await
        }
        None => keys.delete_credentials(&entry, cx).await,
    }
}

/// The one HTTP client the chat hands its providers, built on the first pick.
pub struct ChatHttp(pub Arc<dyn HttpClient>);

impl Global for ChatHttp {}

impl std::fmt::Debug for ChatHttp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ChatHttp").finish_non_exhaustive()
    }
}

/// Returns the chat's HTTP client, building Zed's reqwest client on the first call.
///
/// # Errors
///
/// Returns an error when the client cannot be built.
pub fn http(cx: &mut App) -> anyhow::Result<Arc<dyn HttpClient>> {
    if let Some(ChatHttp(http)) = cx.try_global::<ChatHttp>() {
        return Ok(http.clone());
    }
    let http: Arc<dyn HttpClient> = Arc::new(reqwest_client::ReqwestClient::user_agent(concat!(
        "borer-app/",
        env!("CARGO_PKG_VERSION")
    ))?);
    cx.set_global(ChatHttp(http.clone()));
    Ok(http)
}

/// Returns the credentials provider the chat keeps API keys with, Zed's keychain one.
///
/// It stores them in the system keychain (Credential Manager, Keychain, Secret Service).
/// The app sets no release channel, so Zed never picks its development provider, a file.
///
/// # Arguments
///
/// * `cx` - Application context.
#[must_use]
pub fn credentials(cx: &App) -> Arc<dyn CredentialsProvider> {
    zed_credentials_provider::global(cx)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::{Arc, Mutex};

    use futures::StreamExt as _;
    use gpui::{BorrowAppContext as _, TestAppContext};
    use http_client::{AsyncBody, FakeHttpClient, HttpClient, RedirectPolicy, Response};
    use language_model::{
        LanguageModelClient as _, LanguageModelCompletionEvent, LanguageModelRequest,
        LanguageModelRequestMessage, MessageContent, Role,
    };

    use super::{Endpoint, Offered, Remote, Wire, models};

    /// The method and path, and the body, of every request a stub was sent, in order.
    type Seen = Arc<Mutex<Vec<(String, String)>>>;

    /// Returns a stub HTTP client answering `answer(method and path)` with status 200, and
    /// what it was sent.
    fn stub(answer: fn(&str) -> &'static str) -> (Arc<dyn HttpClient>, Seen) {
        let seen = Arc::new(Mutex::new(Vec::new()));
        let log = seen.clone();
        let http = FakeHttpClient::create(move |request| {
            let log = log.clone();
            async move {
                let at = format!("{} {}", request.method(), request.uri().path());
                let mut body = String::new();
                futures::AsyncReadExt::read_to_string(&mut request.into_body(), &mut body).await?;
                let reply = answer(&at);
                log.lock().unwrap().push((at, body));
                Ok(Response::builder()
                    .status(200)
                    .body(AsyncBody::from(reply))?)
            }
        });
        (http, seen)
    }

    /// Returns a request holding one user message.
    fn hello() -> LanguageModelRequest {
        LanguageModelRequest {
            messages: vec![LanguageModelRequestMessage {
                role: Role::User,
                content: vec![MessageContent::Text("hello".to_owned())],
                cache: false,
                reasoning_details: None,
            }],
            ..LanguageModelRequest::default()
        }
    }

    /// Returns the text of a stream's events, in order.
    async fn text_of(client: &Remote, cx: &mut TestAppContext) -> String {
        let model = super::listed(&client.endpoint, "m", "m".to_owned(), 1);
        let events = client
            .stream_completion(&model, hello(), &cx.to_async())
            .await
            .unwrap();
        let events: Vec<_> = events.collect().await;
        events
            .into_iter()
            .filter_map(|e| match e.unwrap() {
                LanguageModelCompletionEvent::Text(text) => Some(text),
                _ => None,
            })
            .collect()
    }

    /// The OpenAI-compatible adapter lists a local server's models and streams a model's
    /// reply through `open_ai`'s converter and the chat-completions event mapper.
    #[gpui::test]
    async fn the_open_ai_adapter_lists_and_streams(cx: &mut TestAppContext) {
        let (http, seen) = stub(|at| match at {
            "GET /v1/models" => r#"{"data":[{"id":"qwen3"}]}"#,
            _ => concat!(
                "data: {\"choices\":[{\"index\":0,\"delta\":{\"content\":\"hi there\"}}]}\n\n",
                "data: {\"choices\":[{\"index\":0,\"delta\":{},\"finish_reason\":\"stop\"}]}\n\n",
                "data: [DONE]\n\n"
            ),
        });
        let endpoint = Endpoint {
            offered: Offered::Ollama,
            url: "http://localhost:11434/v1".into(),
        };
        let listed = models(endpoint, http, &cx.to_async()).await.unwrap();
        let ids: Vec<_> = listed.iter().map(|m| m.model.id.0.to_string()).collect();
        assert_eq!(ids, ["qwen3"]);
        let chosen = &listed[0];
        let events = chosen
            .client
            .stream_completion(&chosen.model, hello(), &cx.to_async())
            .await
            .unwrap();
        let events: Vec<_> = events.collect().await;
        assert!(
            events
                .iter()
                .any(|e| matches!(e, Ok(LanguageModelCompletionEvent::Text(t)) if t == "hi there"))
        );
        let seen = seen.lock().unwrap().clone();
        assert_eq!(seen[1].0, "POST /v1/chat/completions");
        assert!(seen[1].1.contains("\"model\":\"qwen3\""), "{}", seen[1].1);
    }

    /// No provider request follows a redirect: each goes out with a no-follow policy, and a
    /// redirect answered to a list or a stream is an error naming the host, sending nothing on.
    #[gpui::test]
    async fn no_provider_request_follows_a_redirect(cx: &mut TestAppContext) {
        let policies = Arc::new(Mutex::new(Vec::new()));
        let seen = policies.clone();
        let http = FakeHttpClient::create(move |request| {
            let seen = seen.clone();
            async move {
                seen.lock()
                    .unwrap()
                    .push(request.extensions().get::<RedirectPolicy>().cloned());
                Ok(Response::builder()
                    .status(307)
                    .header("location", "https://elsewhere.example.com/v1")
                    .body(AsyncBody::default())?)
            }
        });
        let endpoint = Endpoint {
            offered: Offered::Ollama,
            url: "http://localhost:11434/v1".into(),
        };
        let listed = models(endpoint, http, &cx.to_async()).await;
        let Err(why) = listed else {
            panic!("a redirect was followed");
        };
        let why = format!("{why:#}");
        assert!(
            why.contains("localhost") && why.contains("redirect"),
            "{why}"
        );
        assert_eq!(*policies.lock().unwrap(), [Some(RedirectPolicy::NoFollow)]);
    }

    /// The Anthropic adapter streams a reply through `anthropic`'s converter and event mapper.
    #[gpui::test]
    async fn the_anthropic_adapter_streams(cx: &mut TestAppContext) {
        let (http, seen) = stub(|_| {
            concat!(
                "data: {\"type\":\"content_block_start\",\"index\":0,\"content_block\":{\"type\":\"text\",\"text\":\"\"}}\n\n",
                "data: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"hi there\"}}\n\n",
                "data: {\"type\":\"message_delta\",\"delta\":{\"stop_reason\":\"end_turn\",\"stop_sequence\":null},\"usage\":{}}\n\n",
                "data: {\"type\":\"message_stop\"}\n\n"
            )
        });
        let model = anthropic::Model::from_listed(anthropic::ListModelEntry {
            id: "claude-test".to_owned(),
            display_name: "Claude Test".to_owned(),
            max_input_tokens: 1000,
            max_tokens: 100,
            capabilities: None,
        });
        let client = Remote {
            endpoint: Endpoint {
                offered: Offered::Anthropic,
                url: "https://api.anthropic.com".into(),
            },
            key: "k".into(),
            http,
            wire: Wire::Anthropic(model),
        };
        assert_eq!(text_of(&client, cx).await, "hi there");
        let seen = seen.lock().unwrap().clone();
        assert_eq!(seen[0].0, "POST /v1/messages");
        assert!(
            seen[0].1.contains("\"model\":\"claude-test\""),
            "{}",
            seen[0].1
        );
    }

    /// The Gemini adapter streams a reply through `google_ai`'s converter and event mapper.
    #[gpui::test]
    async fn the_google_adapter_streams(cx: &mut TestAppContext) {
        let (http, seen) = stub(
            |_| "data: {\"candidates\":[{\"content\":{\"parts\":[{\"text\":\"hi there\"}],\"role\":\"model\"},\"finishReason\":\"STOP\"}]}\n\n",
        );
        let model = google_ai::Model {
            id: "gemini-test".to_owned(),
            display_name: "Gemini Test".to_owned(),
            max_input_tokens: 1000,
            max_output_tokens: Some(100),
            mode: google_ai::GoogleModelMode::Default,
            supported_thinking_levels: Vec::new(),
            default_thinking_level: None,
        };
        let client = Remote {
            endpoint: Endpoint {
                offered: Offered::Google,
                url: "https://generativelanguage.googleapis.com".into(),
            },
            key: "k".into(),
            http,
            wire: Wire::Google(model),
        };
        assert_eq!(text_of(&client, cx).await, "hi there");
        let seen = seen.lock().unwrap().clone();
        assert_eq!(
            seen[0].0,
            "POST /v1beta/models/gemini-test:streamGenerateContent"
        );
    }

    /// Returns the body each adapter sends for the chat's opening request, by provider.
    async fn opening_bodies(cx: &mut TestAppContext) -> Vec<(Offered, serde_json::Value)> {
        let (http, seen) = stub(|_| "data: [DONE]\n\n");
        let claude = anthropic::Model::from_listed(anthropic::ListModelEntry {
            id: "claude-test".to_owned(),
            display_name: "Claude Test".to_owned(),
            max_input_tokens: 1000,
            max_tokens: 100,
            capabilities: None,
        });
        let gemini = google_ai::Model {
            id: "gemini-test".to_owned(),
            display_name: "Gemini Test".to_owned(),
            max_input_tokens: 1000,
            max_output_tokens: Some(100),
            mode: google_ai::GoogleModelMode::Default,
            supported_thinking_levels: Vec::new(),
            default_thinking_level: None,
        };
        let mut bodies = Vec::new();
        for offered in Offered::ALL {
            let wire = match offered {
                Offered::Anthropic => Wire::Anthropic(claude.clone()),
                Offered::Google => Wire::Google(gemini.clone()),
                Offered::OpenAi | Offered::OpenRouter | Offered::Ollama | Offered::LmStudio => {
                    Wire::OpenAi
                }
            };
            let client = Remote {
                endpoint: Endpoint {
                    offered,
                    url: "https://provider.example.com".into(),
                },
                key: "k".into(),
                http: http.clone(),
                wire,
            };
            let model = super::listed(&client.endpoint, "m", "m".to_owned(), 1);
            let request = super::super::thread::request_of(&hello().messages);
            let sent = client.stream_completion(&model, request, &cx.to_async());
            let _streamed = sent.await;
            let body = seen.lock().unwrap().pop().unwrap().1;
            bodies.push((offered, serde_json::from_str(&body).unwrap()));
        }
        bodies
    }

    /// The tool definitions each adapter sends are measured, and the prompt-cache hints
    /// the pinned API crates take are sent: Anthropic's cache marks on the last tool, the
    /// system prompt and the request, and `OpenAI`'s cache key; Gemini, `OpenRouter`, Ollama and
    /// LM Studio requests carry none.
    #[gpui::test]
    async fn the_tool_definitions_sent_are_measured_and_cached(cx: &mut TestAppContext) {
        let bodies = opening_bodies(cx).await;
        let sent: Vec<Offered> = bodies.iter().map(|(offered, _)| *offered).collect();
        assert_eq!(sent, Offered::ALL);
        for (offered, body) in bodies {
            let tools = body["tools"].to_string().len();
            let system = super::super::thread::SYSTEM.len();
            eprintln!("{offered:?}: tool definitions {tools} bytes, system prompt {system} bytes");
            assert!(tools > 1000, "{offered:?}: {body}");
            let said = body.to_string();
            match offered {
                Offered::Anthropic => {
                    let last = body["tools"].as_array().unwrap().last().unwrap();
                    assert_eq!(last["cache_control"]["ttl"], "1h", "{last}");
                    assert_eq!(body["system"][0]["cache_control"]["ttl"], "1h");
                    assert_eq!(body["cache_control"]["type"], "ephemeral");
                }
                Offered::OpenAi => {
                    let key = super::super::thread::PROMPT_CACHE_KEY;
                    assert_eq!(body["prompt_cache_key"], key, "{said}");
                }
                Offered::Google | Offered::OpenRouter | Offered::Ollama | Offered::LmStudio => {
                    assert!(!said.contains("cache"), "{said}");
                }
            }
        }
    }

    /// A provider is local only when its URL's host is loopback: an Ollama URL in settings
    /// that names another machine is not local.
    #[gpui::test]
    fn local_is_the_endpoints_host_being_loopback(cx: &mut TestAppContext) {
        let local = |url: &str| {
            Endpoint {
                offered: Offered::Ollama,
                url: url.to_owned().into(),
            }
            .is_local()
        };
        for url in [
            "http://localhost:11434/v1",
            "http://LOCALHOST:1234",
            "http://127.0.0.1:1234",
            "http://[::1]:1234",
        ] {
            assert!(local(url), "{url}");
        }
        for url in [
            "http://10.0.0.5:11434/v1",
            "http://ollama.example.com",
            "https://api.anthropic.com",
            "localhost:11434",
            "not a url",
        ] {
            assert!(!local(url), "{url}");
        }
        cx.update(settings::init);
        assert!(cx.update(|cx| Endpoint::of(Offered::Ollama, cx).is_local()));
        cx.update(|cx| {
            cx.update_global(|store: &mut settings::SettingsStore, cx| {
                let set = r#"{"language_models":{"ollama":{"api_url":"http://10.0.0.5:11434"}}}"#;
                store.set_user_settings(set, cx).result().unwrap();
            });
        });
        let endpoint = cx.update(|cx| Endpoint::of(Offered::Ollama, cx));
        assert_eq!(endpoint.url.as_ref(), "http://10.0.0.5:11434/v1");
        assert!(!endpoint.is_local());
    }
}
