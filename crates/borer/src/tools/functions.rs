//! `class_layout`, which can save a class's layout as a struct, and the tests of
//! the function tools the catalog answers ([`borer_front::tools`]).

use borer_engine::analysis::edit::{Edit, Force, Laid};
use borer_engine::program::Feature;
use borer_front::tools::HeldExt;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::params::ClassLayoutParams;
use crate::safety::{Effect, effects};
use crate::tools::annotate::listed;

#[tool_router(router = function_tools, vis = "pub(crate)")]
impl BorerServer {
    /// Renders a class layout recovered from its methods' field accesses,
    /// or with `apply` defines it as a user struct and types each method's
    /// object with it ([`borer_engine::analysis::apply::from_class`]).
    ///
    /// # Arguments
    ///
    /// * `ClassLayoutParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address is not a class method, nothing
    /// belongs to the class, or the struct to apply is refused.
    #[tool(
        description = "Infer a C++ class's fields, methods and vftable from how its methods use the object: offset, width, reads, writes; unnamed slots hint names their vtable family agrees on. For a known layout use set_type. apply=Name saves it as a struct (dry run until dry_run=false).",
        meta = effects(&[Effect::ChangesSession]),
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn class_layout(
        &self,
        Parameters(ClassLayoutParams {
            class,
            apply,
            dry_run,
        }): Parameters<ClassLayoutParams>,
    ) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Decompile, |p, a, o| {
            let name = match self.function_entry(p, a, &class) {
                Ok(entry) => {
                    let n = borer_engine::analysis::name_of(a, o, entry);
                    borer_engine::analysis::classes::class_of(&n)
                        .ok_or_else(|| format!("{n} is not a class method"))?
                        .to_owned()
                }
                Err(_) => class.clone(),
            };
            let Some(apply) = &apply else {
                let layout = borer_engine::analysis::apply::class_named(p, a, o, &name)?;
                return Ok(borer_engine::analysis::classes::render_layout(
                    &layout, a, o,
                ));
            };
            let dry = dry_run.unwrap_or(true);
            let edits = [Edit::Layout {
                from: Laid::Class(name),
                name: apply.clone(),
            }];
            self.edited((p, a, o), &edits, Force::Refuse, dry)
                .map(|plan| listed(&plan, dry))
                .map_err(|e| e.to_string())
        })
    }
}

#[cfg(test)]
mod tests {
    /// Before `load_binary`, `functions` refuses the way every other tool
    /// does: invalid params, naming the call to make first.
    ///
    /// It read the analysis outside the tool-body boundary and answered the
    /// one refusal its siblings give as invalid params as an internal error
    /// instead, so a client telling the two codes apart saw a broken server
    /// where every other tool showed a missing step.
    ///
    /// # Panics
    ///
    /// When the refusal differs from a sibling's in code or message.
    #[test]
    fn functions_refuses_without_a_binary_like_every_other_tool() {
        let server = crate::BorerServer::default();
        let refused = server
            .functions(rmcp::handler::server::wrapper::Parameters(
                crate::params::FunctionsParams {
                    filter: None,
                    sort: None,
                    offset: None,
                    limit: None,
                    count_only: None,
                },
            ))
            .expect_err("nothing is loaded");
        let sibling = server
            .function(rmcp::handler::server::wrapper::Parameters(
                crate::params::FunctionDetailParams {
                    address: "0x1000".to_owned(),
                    offset: None,
                },
            ))
            .expect_err("nothing is loaded");
        assert_eq!(refused.code, rmcp::model::ErrorCode::INVALID_PARAMS);
        assert_eq!(refused.code, sibling.code);
        assert_eq!(refused.message, sibling.message);
        assert_eq!(refused.message, crate::state::NO_BINARY);
    }

    /// `xrefs` reads a target that is neither an address nor a name as
    /// `Class+offset`.
    ///
    /// It lists the functions using that field through a pointer typed as
    /// the class, with the value stored and the instruction; a class
    /// nothing belongs to is refused, saying which forms the target may
    /// take.
    ///
    /// # Panics
    ///
    /// When the field's writer is missing, or the refusal does not name
    /// the field form.
    #[test]
    fn xrefs_reads_a_class_and_an_offset_as_a_field() {
        use crate::params::XrefsParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let mut code = vec![0xc3; 0x100];
        // ASM: mov dword [rcx+0x24], 5; ret
        code[..8].copy_from_slice(&[0xc7, 0x41, 0x24, 0x05, 0x00, 0x00, 0x00, 0xc3]);
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let mut overlay = borer_engine::analysis::Overlay::default();
        overlay.names.insert(0x1000, "Foo::Set".to_owned());
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            overlay: std::sync::Arc::new(std::sync::RwLock::new(overlay)),
            ..crate::BorerServer::default()
        };
        let xrefs = |address: &str| {
            server.xrefs(Parameters(XrefsParams {
                address: address.to_owned(),
                offset: None,
                limit: None,
                count_only: None,
            }))
        };
        let field = xrefs("Foo+0x24").expect("a field");
        assert!(
            field
                .starts_with("# Foo+0x24: 1 functions use it through a pointer typed as the class"),
            "{field}"
        );
        assert!(
            field.contains(
                "
0x1000	Foo::Set	a1	w	0x5	0x1000
"
            ),
            "{field}"
        );
        let refused = xrefs("Nope+0x24").expect_err("no such class");
        assert!(
            refused
                .message
                .ends_with("; nor is it Class+offset, a field of a class with methods or a vtable"),
            "{}",
            refused.message
        );
    }
}
