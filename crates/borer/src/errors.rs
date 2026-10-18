//! The JSON-RPC errors a tool or a resource answers with.

use rmcp::ErrorData;
use rmcp::model::ErrorCode;

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
