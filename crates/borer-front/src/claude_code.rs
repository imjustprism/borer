//! The protocol the app's chat speaks with the `claude` program, Claude Code's command line.
//!
//! It holds the flags, the lines of its stream-JSON protocol, and borer's tools offered to
//! it as an in-process MCP server.
//!
//! The app starts `claude` with [`args`]; Claude Code holds its own sign-in, which borer never
//! reads. Each line either side writes is one JSON object. The app writes:
//!
//! - a person's message: `{"type":"user","message":{"role":"user","content":"<text>"},
//!   "parent_tool_use_id":null}` ([`user`]);
//! - an `initialize` control request, only when listing the models:
//!   `{"type":"control_request","request_id":"<id>","request":{"subtype":"initialize"}}`
//!   ([`initialize`]);
//! - an answer to each control request Claude Code sends: `{"type":"control_response",
//!   "response":{"subtype":"success","request_id":"<id>","response":{..}}}`, or
//!   `"subtype":"error"` with `"error":"<why>"` ([`respond`], [`refuse`]).
//!
//! Claude Code writes, of what the app reads ([`read`]); every other line is ignored:
//!
//! - `{"type":"assistant","message":{"content":[{"type":"text","text":".."},
//!   {"type":"tool_use",..}]},..}`: a reply's blocks, of which the text ones are kept
//!   ([`Event::Text`]);
//! - `{"type":"control_request","request_id":"<id>","request":{"subtype":"mcp_message",
//!   "server_name":"borer","message":<JSON-RPC>}}`: a call of the MCP server [`SERVER`]
//!   ([`Event::Mcp`]); `"subtype":"can_use_tool"` and any other subtype are refused
//!   ([`Event::Ask`]);
//! - `{"type":"control_response","response":{"subtype":"success","request_id":"<id>",
//!   "response":{"models":[{"value":"opus","displayName":"Opus","description":".."}],..}}}`:
//!   the answer to `initialize` ([`Event::Answered`]); its other fields, the signed-in
//!   account among them, are never read;
//! - `{"type":"result","subtype":"success","is_error":false,"result":"<text>",..}`: the end
//!   of a turn, `is_error` true with the reason in `result` (or the subtype) when it failed
//!   ([`Event::Done`]).
//!
//! The MCP server lives in the app: Claude Code sends its JSON-RPC inside `mcp_message`
//! requests and the app answers inside `{"mcp_response":<JSON-RPC>}` ([`mcp`], [`answered`]).
//! Lines are bounded before they are parsed ([`LINE_MAX`], [`TURN_MAX_BYTES`]); a line
//! that is not JSON is an error, never a panic.

use serde::Deserialize;
use serde_json::{Map, Value, json};

use crate::tools::TOOLS;

/// The name Claude Code knows borer's MCP server by; its tools are `mcp__borer__<tool>`.
pub const SERVER: &str = "borer";

/// Longest line read from Claude Code, in bytes: a longer one ends the turn as an error.
pub const LINE_MAX: usize = 8 << 20;

/// Most bytes read from Claude Code in one turn or one model listing.
pub const TURN_MAX_BYTES: usize = 64 << 20;

/// Most models kept from Claude Code's list.
pub const MODELS_MAX: usize = 64;

/// The MCP protocol version the server answers when Claude Code names none.
const PROTOCOL: &str = "2025-06-18";

/// A model Claude Code offers, as its `initialize` answer lists it.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Model {
    /// What `--model` takes for it, as `opus` or `default`.
    pub value: String,
    /// Its name as Claude Code shows it.
    #[serde(default)]
    pub display_name: String,
    /// What Claude Code says of it.
    #[serde(default)]
    pub description: String,
}

/// What one line from Claude Code means to the app.
#[derive(Debug, Clone, PartialEq)]
pub enum Event {
    /// Text of the model's reply, one block.
    Text(String),
    /// A JSON-RPC message for the MCP server [`SERVER`], to answer under `request`.
    Mcp {
        /// The control request's id, which the answer names.
        request: String,
        /// The JSON-RPC message.
        message: Value,
    },
    /// Any other control request, as a tool permission prompt or a message for another
    /// server: refused under `request`.
    Ask {
        /// The control request's id, which the refusal names.
        request: String,
    },
    /// The answer to a control request the app sent.
    Answered {
        /// The id the app sent it under.
        request: String,
        /// The models it listed, when it lists any; at most [`MODELS_MAX`].
        models: Vec<Model>,
        /// Why it failed, when it did.
        error: Option<String>,
    },
    /// The turn ended: `Err` with the reason when it failed.
    Done(Result<(), String>),
    /// A line the app has no use for.
    Other,
}

/// A line from Claude Code as its `type` field sorts it.
#[derive(Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
enum Line {
    /// A reply of the model.
    Assistant {
        /// The reply.
        message: Reply,
    },
    /// A request the app answers.
    ControlRequest {
        /// Its id.
        request_id: String,
        /// What it asks.
        request: Request,
    },
    /// The answer to a request the app sent.
    ControlResponse {
        /// The answer.
        response: Response,
    },
    /// The end of a turn.
    Result {
        /// Whether the turn failed.
        #[serde(default)]
        is_error: bool,
        /// How it ended, as `success` or `error_during_execution`.
        #[serde(default)]
        subtype: String,
        /// The reply's text, or the reason it failed.
        #[serde(default)]
        result: Option<String>,
    },
    /// Every other kind of line.
    #[serde(other)]
    Other,
}

/// A reply of the model.
#[derive(Deserialize)]
struct Reply {
    /// Its blocks.
    #[serde(default)]
    content: Vec<Block>,
}

/// One block of a reply.
#[derive(Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
enum Block {
    /// Text.
    Text {
        /// The text.
        text: String,
    },
    /// Every other block: tool calls, thinking.
    #[serde(other)]
    Other,
}

/// What a control request asks.
#[derive(Deserialize)]
#[serde(tag = "subtype", rename_all = "snake_case")]
enum Request {
    /// A message for an MCP server the app serves.
    McpMessage {
        /// The server's name.
        server_name: String,
        /// The JSON-RPC message.
        message: Value,
    },
    /// Every other request.
    #[serde(other)]
    Other,
}

/// The answer to a control request the app sent.
#[derive(Deserialize)]
struct Response {
    /// `success` or `error`.
    #[serde(default)]
    subtype: String,
    /// The id the app sent it under.
    #[serde(default)]
    request_id: String,
    /// What it answered.
    #[serde(default)]
    response: Option<Answer>,
    /// Why it failed.
    #[serde(default)]
    error: Option<String>,
}

/// What a control request answered, of what the app reads.
#[derive(Deserialize)]
struct Answer {
    /// The models offered, for `initialize`.
    #[serde(default)]
    models: Vec<Model>,
}

/// Returns what one line from Claude Code means.
///
/// # Arguments
///
/// * `line` - One line, without its line break; at most [`LINE_MAX`] bytes are read.
///
/// # Errors
///
/// Returns that the line is longer than [`LINE_MAX`] or is not JSON of a known shape.
pub fn read(line: &str) -> Result<Event, String> {
    if line.len() > LINE_MAX {
        return Err(format!("Claude Code wrote a line over {LINE_MAX} bytes"));
    }
    if line.trim().is_empty() {
        return Ok(Event::Other);
    }
    let parsed: Line = serde_json::from_str(line)
        .map_err(|e| format!("Claude Code wrote a line that does not read: {e}"))?;
    Ok(match parsed {
        Line::Assistant { message } => {
            let text: String = message
                .content
                .into_iter()
                .filter_map(|b| match b {
                    Block::Text { text } => Some(text),
                    Block::Other => None,
                })
                .collect();
            if text.is_empty() {
                Event::Other
            } else {
                Event::Text(text)
            }
        }
        Line::ControlRequest {
            request_id,
            request:
                Request::McpMessage {
                    server_name,
                    message,
                },
        } if server_name == SERVER => Event::Mcp {
            request: request_id,
            message,
        },
        Line::ControlRequest { request_id, .. } => Event::Ask {
            request: request_id,
        },
        Line::ControlResponse { response } => Event::Answered {
            request: response.request_id,
            models: response
                .response
                .map(|a| a.models.into_iter().take(MODELS_MAX).collect())
                .unwrap_or_default(),
            error: (response.subtype == "error").then(|| {
                response
                    .error
                    .unwrap_or_else(|| "no reason given".to_owned())
            }),
        },
        Line::Result {
            is_error,
            subtype,
            result,
        } => Event::Done(if is_error {
            Err(result.filter(|r| !r.trim().is_empty()).unwrap_or(subtype))
        } else {
            Ok(())
        }),
        Line::Other => Event::Other,
    })
}

/// Returns the flags `claude` is started with for the chat.
///
/// They make it read and write stream-JSON (`-p --input-format stream-json --output-format
/// stream-json --verbose`); load none of the person's customizations, slash commands or
/// saved sessions (`--safe-mode --disable-slash-commands --no-session-persistence`); offer
/// no built-in tool (`--tools ""`) and no MCP server but borer's, served by the app
/// (`--strict-mcp-config --mcp-config`); allow borer's tools alone and deny every prompt
/// (`--allowedTools`, `--permission-prompts none`); and tell the model `system` in place of
/// Claude Code's own prompt (`--system-prompt`).
///
/// # Arguments
///
/// * `model` - What `--model` takes, `None` for Claude Code's own choice.
/// * `system` - The system prompt.
#[must_use]
pub fn args(model: Option<&str>, system: &str) -> Vec<String> {
    let config = json!({ "mcpServers": { SERVER: { "type": "sdk", "name": SERVER } } });
    let allowed: Vec<String> = TOOLS
        .iter()
        .map(|t| format!("mcp__{SERVER}__{}", t.name))
        .collect();
    let mut args: Vec<String> = [
        "-p",
        "--input-format",
        "stream-json",
        "--output-format",
        "stream-json",
        "--verbose",
        "--safe-mode",
        "--disable-slash-commands",
        "--no-session-persistence",
        "--strict-mcp-config",
        "--mcp-config",
        config.to_string().as_str(),
        "--tools",
        "",
        "--permission-prompts",
        "none",
        "--allowedTools",
        allowed.join(",").as_str(),
        "--system-prompt",
        system,
    ]
    .map(str::to_owned)
    .into();
    if let Some(model) = model {
        args.extend(["--model".to_owned(), model.to_owned()]);
    }
    args
}

/// Returns the line that sends the person's `text` as a message.
#[must_use]
pub fn user(text: &str) -> String {
    let line = json!({
        "type": "user",
        "message": { "role": "user", "content": text },
        "parent_tool_use_id": null,
    });
    format!("{line}\n")
}

/// Returns the line that asks Claude Code to start and list its models, under `request`.
#[must_use]
pub fn initialize(request: &str) -> String {
    let line = json!({
        "type": "control_request",
        "request_id": request,
        "request": { "subtype": "initialize" },
    });
    format!("{line}\n")
}

/// Returns the line that answers the control request `request` with `response`.
#[must_use]
pub fn respond(request: &str, response: &Value) -> String {
    let line = json!({
        "type": "control_response",
        "response": { "subtype": "success", "request_id": request, "response": response },
    });
    format!("{line}\n")
}

/// Returns the line that refuses the control request `request`, saying `why`.
#[must_use]
pub fn refuse(request: &str, why: &str) -> String {
    let line = json!({
        "type": "control_response",
        "response": { "subtype": "error", "request_id": request, "error": why },
    });
    format!("{line}\n")
}

/// What the MCP server does with a JSON-RPC message.
#[derive(Debug, Clone, PartialEq)]
pub enum Mcp {
    /// Answer it with this message.
    Reply(Value),
    /// Run the tool `name` with `args`, then answer under `id` ([`answered`]).
    Call {
        /// The JSON-RPC id the answer names.
        id: Value,
        /// The tool.
        name: String,
        /// Its arguments.
        args: Value,
    },
}

/// Returns what the MCP server does with `message`: `initialize`, `tools/list` and every
/// notification are answered at once, `tools/call` runs a tool, any other method is
/// answered as not found.
#[must_use]
pub fn mcp(message: &Value) -> Mcp {
    let method = message.get("method").and_then(Value::as_str);
    let Some(id) = message.get("id").cloned() else {
        return Mcp::Reply(json!({ "jsonrpc": "2.0", "result": {} }));
    };
    let params = message.get("params");
    let result = match method {
        Some("initialize") => {
            let version = params
                .and_then(|p| p.get("protocolVersion"))
                .and_then(Value::as_str)
                .unwrap_or(PROTOCOL);
            json!({
                "protocolVersion": version,
                "capabilities": { "tools": {} },
                "serverInfo": { "name": SERVER, "version": env!("CARGO_PKG_VERSION") },
            })
        }
        Some("tools/list") => json!({ "tools": tools() }),
        Some("tools/call") => {
            let name = params.and_then(|p| p.get("name")).and_then(Value::as_str);
            let Some(name) = name else {
                return Mcp::Reply(failed(&id, -32602, "tools/call names no tool"));
            };
            let args = params
                .and_then(|p| p.get("arguments"))
                .cloned()
                .unwrap_or_else(|| Value::Object(Map::new()));
            return Mcp::Call {
                id,
                name: name.to_owned(),
                args,
            };
        }
        _ => return Mcp::Reply(failed(&id, -32601, "method not found")),
    };
    Mcp::Reply(json!({ "jsonrpc": "2.0", "id": id, "result": result }))
}

/// Returns the MCP answer under `id` to a tool call: `text`, an error when `is_error`.
#[must_use]
pub fn answered(id: &Value, text: &str, is_error: bool) -> Value {
    json!({
        "jsonrpc": "2.0",
        "id": id,
        "result": { "content": [{ "type": "text", "text": text }], "isError": is_error },
    })
}

/// Returns a JSON-RPC error under `id`.
fn failed(id: &Value, code: i32, message: &str) -> Value {
    json!({ "jsonrpc": "2.0", "id": id, "error": { "code": code, "message": message } })
}

/// Returns every tool of [`TOOLS`] as `tools/list` lists it.
fn tools() -> Vec<Value> {
    TOOLS
        .iter()
        .map(|t| {
            json!({
                "name": t.name,
                "description": t.description,
                "inputSchema": Value::Object(t.input_schema()),
            })
        })
        .collect()
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use serde_json::{Value, json};

    use super::{Event, LINE_MAX, Mcp, Model, args, mcp, read};

    /// The lines Claude Code 2.1.318 wrote, cut to the fields the app reads, and one of
    /// each kind it ignores.
    #[test]
    fn recorded_lines_read_as_their_events() {
        let init = r#"{"type":"system","subtype":"init","session_id":"s","tools":["mcp__borer__decompile"],"mcp_servers":[{"name":"borer","status":"connected"}]}"#;
        assert_eq!(read(init), Ok(Event::Other));
        let text = r#"{"type":"assistant","message":{"role":"assistant","content":[{"type":"text","text":"ok"},{"type":"tool_use","id":"t","name":"mcp__borer__query","input":{}}]},"parent_tool_use_id":null,"session_id":"s"}"#;
        assert_eq!(read(text), Ok(Event::Text("ok".to_owned())));
        let call = r#"{"type":"control_request","request_id":"r1","request":{"subtype":"mcp_message","server_name":"borer","message":{"method":"tools/call","params":{"name":"query","arguments":{"uri":"borer://triage"}},"jsonrpc":"2.0","id":3}}}"#;
        let Ok(Event::Mcp { request, message }) = read(call) else {
            panic!("not an MCP message");
        };
        assert_eq!(request, "r1");
        assert_eq!(
            mcp(&message),
            Mcp::Call {
                id: json!(3),
                name: "query".to_owned(),
                args: json!({ "uri": "borer://triage" }),
            }
        );
        let ask = r#"{"type":"control_request","request_id":"r2","request":{"subtype":"can_use_tool","tool_name":"Bash","input":{}}}"#;
        assert_eq!(
            read(ask),
            Ok(Event::Ask {
                request: "r2".to_owned()
            })
        );
        let other = r#"{"type":"control_request","request_id":"r3","request":{"subtype":"mcp_message","server_name":"elsewhere","message":{}}}"#;
        assert_eq!(
            read(other),
            Ok(Event::Ask {
                request: "r3".to_owned()
            })
        );
        let listed = r#"{"type":"control_response","response":{"subtype":"success","request_id":"i","response":{"commands":[],"models":[{"value":"default","resolvedModel":"m","displayName":"Default (recommended)","description":"d"}],"account":{"email":"x"}}}}"#;
        assert_eq!(
            read(listed),
            Ok(Event::Answered {
                request: "i".to_owned(),
                models: vec![Model {
                    value: "default".to_owned(),
                    display_name: "Default (recommended)".to_owned(),
                    description: "d".to_owned(),
                }],
                error: None,
            })
        );
        let done = r#"{"type":"result","subtype":"success","is_error":false,"result":"ok","session_id":"s"}"#;
        assert_eq!(read(done), Ok(Event::Done(Ok(()))));
        let failed = r#"{"type":"result","subtype":"success","is_error":true,"result":"Not logged in · Please run /login"}"#;
        assert_eq!(
            read(failed),
            Ok(Event::Done(Err(
                "Not logged in · Please run /login".to_owned()
            )))
        );
        let bare = r#"{"type":"result","subtype":"error_during_execution","is_error":true}"#;
        assert_eq!(
            read(bare),
            Ok(Event::Done(Err("error_during_execution".to_owned())))
        );
        assert_eq!(
            read(r#"{"type":"stream_event","event":{}}"#),
            Ok(Event::Other)
        );
    }

    /// Hostile lines are errors or ignored, never a panic: not JSON, a known kind with the
    /// wrong shape, deep nesting, and a line over the cap.
    #[test]
    fn hostile_lines_are_errors() {
        assert!(read("not json").is_err());
        assert!(read(r#"{"type":"assistant","message":7}"#).is_err());
        assert!(read(r#"{"no":"type"}"#).is_err());
        let deep = format!("{}{}", "[".repeat(100_000), "]".repeat(100_000));
        assert!(read(&deep).is_err());
        let long = format!(r#"{{"type":"x","pad":"{}"}}"#, "a".repeat(LINE_MAX));
        assert!(read(&long).unwrap_err().contains("over"));
        assert_eq!(read("  "), Ok(Event::Other));
    }

    /// The MCP server answers its handshake and lists every tool of the catalog; an unknown
    /// method and a call naming no tool are JSON-RPC errors.
    #[test]
    fn the_mcp_server_answers_its_handshake() {
        let Mcp::Reply(init) = mcp(
            &json!({"jsonrpc":"2.0","id":0,"method":"initialize","params":{"protocolVersion":"2025-11-25"}}),
        ) else {
            panic!("initialize runs nothing");
        };
        assert_eq!(init["result"]["protocolVersion"], "2025-11-25");
        let Mcp::Reply(listed) = mcp(&json!({"jsonrpc":"2.0","id":1,"method":"tools/list"})) else {
            panic!("tools/list runs nothing");
        };
        let tools = listed["result"]["tools"].as_array().unwrap();
        assert_eq!(tools.len(), crate::tools::TOOLS.len());
        assert!(tools.iter().all(|t| t["inputSchema"].is_object()));
        let note = mcp(&json!({"jsonrpc":"2.0","method":"notifications/initialized"}));
        assert_eq!(note, Mcp::Reply(json!({"jsonrpc":"2.0","result":{}})));
        let Mcp::Reply(unknown) = mcp(&json!({"jsonrpc":"2.0","id":2,"method":"prompts/list"}))
        else {
            panic!("an unknown method runs nothing");
        };
        assert_eq!(unknown["error"]["code"], -32601);
        let Mcp::Reply(nameless) = mcp(&json!({"jsonrpc":"2.0","id":2,"method":"tools/call"}))
        else {
            panic!("a call naming no tool runs nothing");
        };
        assert_eq!(nameless["error"]["code"], -32602);
    }

    /// The flags allow borer's tools alone, offer no built-in tool, and name the model only
    /// when one is chosen.
    #[test]
    fn the_flags_allow_only_borers_tools() {
        let flags = args(Some("sonnet"), "be brief");
        let after = |flag: &str| {
            let at = flags.iter().position(|f| f == flag).unwrap();
            flags[at + 1].clone()
        };
        assert_eq!(after("--tools"), "");
        assert_eq!(after("--permission-prompts"), "none");
        assert_eq!(after("--model"), "sonnet");
        assert_eq!(after("--system-prompt"), "be brief");
        assert!(
            after("--allowedTools")
                .split(',')
                .all(|t| t.starts_with("mcp__borer__"))
        );
        let config: Value = serde_json::from_str(&after("--mcp-config")).unwrap();
        assert_eq!(config["mcpServers"]["borer"]["type"], "sdk");
        assert!(!args(None, "").iter().any(|f| f == "--model"));
    }
}
