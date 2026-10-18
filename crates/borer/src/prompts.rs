//! The MCP prompts: agent workflows shipped next to the tools.

use rmcp::handler::server::wrapper::Parameters;
use rmcp::model::{PromptMessage, Role};
use rmcp::{prompt, prompt_router};

use crate::BorerServer;
use crate::params::{ExplainFunctionArgs, FindCheckArgs};
use crate::playbooks;

/// Agent workflows offered as MCP prompts: know-how shipped next to the
/// tools, whose texts the `borer://playbook` resources serve too
/// ([`playbooks`]).
#[prompt_router(vis = "pub(crate)")]
impl BorerServer {
    /// Returns the end-to-end triage workflow.
    #[expect(clippy::unused_self, reason = "rmcp prompt handlers are methods")]
    #[prompt(
        name = "triage",
        description = "Triage the loaded binary end to end (what it is, what it imports, what it hides, where to read first) in a token-frugal tool order."
    )]
    fn triage(&self) -> Vec<PromptMessage> {
        vec![PromptMessage::new_text(Role::User, playbooks::TRIAGE)]
    }

    /// Returns the workflow that maps a client's protocol and message system.
    #[expect(clippy::unused_self, reason = "rmcp prompt handlers are methods")]
    #[prompt(
        name = "protocol",
        description = "Map how a networked client talks and dispatches: wire ids, every command's record, the message classes with their fields and handlers, and the registration tables, in a token-frugal order."
    )]
    fn protocol(&self) -> Vec<PromptMessage> {
        vec![PromptMessage::new_text(Role::User, playbooks::PROTOCOL)]
    }

    /// Returns the workflow that locates a validation routine.
    ///
    /// # Arguments
    ///
    /// * `FindCheckArgs` - What is being validated.
    #[expect(clippy::unused_self, reason = "rmcp prompt handlers are methods")]
    #[prompt(
        name = "find_check",
        description = "Locate and explain the code that validates something (serial, license, password): from strings and constants to the comparison, ending with a rename plan."
    )]
    fn find_check(
        &self,
        Parameters(FindCheckArgs { what }): Parameters<FindCheckArgs>,
    ) -> Vec<PromptMessage> {
        vec![PromptMessage::new_text(
            Role::User,
            playbooks::FIND_CHECK.replace("<what>", &what),
        )]
    }

    /// Returns the workflow that explains one function.
    ///
    /// # Arguments
    ///
    /// * `ExplainFunctionArgs` - The function's address or name.
    #[expect(clippy::unused_self, reason = "rmcp prompt handlers are methods")]
    #[prompt(
        name = "explain_function",
        description = "Explain one function from its summary, decompilation and callers, then propose names to apply."
    )]
    fn explain_function(
        &self,
        Parameters(ExplainFunctionArgs { address }): Parameters<ExplainFunctionArgs>,
    ) -> Vec<PromptMessage> {
        vec![PromptMessage::new_text(
            Role::User,
            playbooks::EXPLAIN_FUNCTION.replace("<address>", &address),
        )]
    }
}
