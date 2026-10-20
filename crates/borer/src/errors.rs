//! The JSON-RPC errors a tool or a resource answers with.

use rmcp::ErrorData;
use rmcp::model::{CallToolResponse, CallToolResult, ContentBlock, ErrorCode};

/// Builds an "invalid params" JSON-RPC error.
///
/// # Arguments
///
/// * `msg` - The message shown to the agent.
pub(crate) fn err_params(msg: impl std::fmt::Display) -> ErrorData {
    ErrorData::new(ErrorCode::INVALID_PARAMS, msg.to_string(), None)
}

/// Builds an "internal error" JSON-RPC error.
///
/// # Arguments
///
/// * `msg` - The message shown to the agent.
pub(crate) fn err_internal(msg: impl std::fmt::Display) -> ErrorData {
    ErrorData::new(ErrorCode::INTERNAL_ERROR, msg.to_string(), None)
}

/// Builds a "resource not found" JSON-RPC error.
///
/// # Arguments
///
/// * `msg` - The message shown to the agent.
pub(crate) fn err_not_found(msg: impl std::fmt::Display) -> ErrorData {
    ErrorData::new(ErrorCode::RESOURCE_NOT_FOUND, msg.to_string(), None)
}

/// Turns a known tool's failure into a tool result the agent reads.
///
/// The protocol keeps its errors for a request it cannot run: an unknown
/// tool. A tool that ran and failed (no binary loaded, a name nothing
/// matches, a file that does not open) answers with `isError` set, so the
/// model sees the message and corrects its next call.
///
/// # Arguments
///
/// * `known` - Whether the router has a tool of the requested name.
/// * `error` - What the tool, or the router on its behalf, failed with.
///
/// # Returns
///
/// The error's message as an `isError` result when `known`.
///
/// # Errors
///
/// The error itself when the tool is unknown.
pub(crate) fn tool_failure(known: bool, error: ErrorData) -> Result<CallToolResponse, ErrorData> {
    if known {
        Ok(CallToolResult::error(vec![ContentBlock::text(error.message)]).into())
    } else {
        Err(error)
    }
}

#[cfg(test)]
mod tests {
    use rmcp::model::CallToolResponse;

    /// A known tool's failure is an `isError` result carrying the message;
    /// an unknown tool's stays a protocol error.
    ///
    /// # Panics
    ///
    /// When either answer has the other shape.
    #[test]
    fn a_tool_failure_is_a_result_and_an_unknown_tool_an_error() {
        let failed = super::tool_failure(true, super::err_params("no binary loaded"));
        let Ok(CallToolResponse::Complete(result)) = failed else {
            panic!("a known tool's failure is a result: {failed:?}");
        };
        assert_eq!(result.is_error, Some(true));
        assert_eq!(
            result.content[0].as_text().map(|t| t.text.as_str()),
            Some("no binary loaded")
        );
        let unknown = super::tool_failure(false, super::err_params("tool not found"));
        assert!(unknown.is_err(), "{unknown:?}");
    }
}
