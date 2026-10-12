//! What an agent is handed before its first call: the server's instructions
//! and the prompts' texts.
//!
//! The instructions are built from the tool router, the prompt router and
//! the resource tables ([`instructions`]), so a tool, prompt or resource
//! added or renamed cannot leave them behind. The prompts' texts live here
//! as constants that the prompts and the `borer://playbook` resources both
//! read: in most hosts a prompt is offered to the human as a slash command,
//! never to the model, so the same text is a resource the agent can read.

use rmcp::model::Prompt;

use super::{RESOURCE_TEMPLATES, RESOURCES, resource_name};

/// The `triage` prompt's text.
pub(crate) const TRIAGE: &str = "Triage the currently loaded binary with the borer tools, cheapest first, and stop \
     as soon as you can say what it is and where its interesting code lives.\n \
     1. The resource borer://triage answers most of this in one call: format, whether \
     it is packed, anti-analysis tricks, crypto, APIs resolved at runtime, the strings \
     it generates rather than stores, what its imports let it do, and the functions to \
     read first with the evidence for each. Start there.\n \
     2. Only where that leaves a question: borer://protection and entropy(threshold=7.5) \
     for a packer payload, borer://dynimports for APIs behind GetProcAddress, \
     borer://stackstrings and strings(filter=...) for text it stores, \
     find_function_by_string for the most telling of those, and borer://checks for \
     serial and license validators.\n \
     3. function_summary on each candidate from the reading list; decompile only the \
     ones whose summary (callees, strings) makes them worth reading. \
     borer://emulate/<addr> runs a generator or a decoder to read its plaintext, and \
     takes a whole experiment: registers, arguments, patched bytes, a stop address, a \
     step trace.\n \
     4. Report: purpose, capabilities, notable functions with addresses, and the next \
     three functions to read. Apply set_name(dry_run=false) for anything you \
     identified and save_project so the names persist.";

/// The `protocol` prompt's text.
pub(crate) const PROTOCOL: &str = "Map the loaded client's protocol with the borer resources, tables first, and read \
     code only where a table leaves a question.\n \
     1. borer://vslot/<slot> lists every class whose virtual at that slot returns a \
     constant; a command class answers its wire id that way, so try the low slots \
     (3 is common) and keep the one whose values look like an id space.\n \
     2. borer://protocol/<slot> puts every class on one row with who sends it, the \
     handler that receives it, what it writes and what it reads; the rest of these \
     steps are its columns in full. \
     borer://schemas/<slot> joins those classes with the record each one decodes: \
     kind@offset per field, nested records, repeats, field names where the class or \
     the message it mirrors names them. That table is the wire protocol.\n \
     3. borer://schema/<class> for one command in full, with the reader behind every \
     field; borer://schema/<function> for any deserializer by address. The other \
     direction is borer://encodes/<slot> and borer://encode/<class>: what each \
     command writes onto the wire, in order, with widths and the field each value \
     came from, packed buffers split into their parts; borer://senders/<slot> names \
     the functions constructing each command, which is where the client sends it, \
     and borer://hooks/<slot> gives the addresses to hook: encoder, decoder, handler \
     and each send call site.\n \
     4. borer://messages[/filter] lists every class that registered a four-character \
     id with its named fields, the global its id lives in, and the functions reading \
     that global: the handlers. A sender fills the message, a handler turns it into a \
     command; follow a handler to the command class and back to step 2.\n \
     5. borer://shape/<function> on any registration function lists its whole family \
     with the string and data each one registers: attributes, settings, factories.\n \
     6. borer://grep/<text> finds every pseudo-C line program-wide (a call, a field \
     write, a constant) once the index is built; borer://fieldrefs/<offset> finds \
     every instruction touching one field offset.\n \
     7. Write the facts you rely on as anchors (field, vconst, function lines, and \
     encode or decode lines holding a row of the protocol table) and keep the \
     manifest: borer://anchors/<path> re-derives and judges every one after the \
     next client update, a packet whose layout changed included.\n \
     Any name met on the way: borer://about/<name> answers from every table at once. \
     8. Inside the client a command becomes messages between components (borer://map \
     lays out the subsystems first): \
     borer://ports/<filter> lists which component accepts which message and the \
     function each is dispatched to, and borer://attrs/<filter> lists the entity \
     attributes with their codes, types and the functions using them.";

/// The `find_check` prompt's text; `<what>` is what is validated.
pub(crate) const FIND_CHECK: &str = "Find the code that validates the <what> in the loaded binary.\n\
     1. find_function_by_string with filters related to it (e.g. \"invalid\", \
     \"wrong\", \"success\", \"registered\", \"<what>\") and search(kind=text) for \
     UI text; note every function that references such strings.\n\
     2. find_crypto_constants: a hash or cipher table near the check tells you how \
     the value is transformed before comparison.\n\
     3. function_summary, then decompile, the referencing functions; follow callers \
     (xrefs) upward until you reach the function that branches on the result.\n\
     4. In the decompilation, identify the comparison (== / != / memcmp-style loop), \
     the inputs feeding it, and every transformation on the way; quote the exact \
     pseudo-C lines with their addresses.\n\
     5. Explain the algorithm in plain language, state what input would pass, and \
     propose names for the functions and globals involved; apply them with \
     set_name(dry_run=false) and set_comment, then save_project.";

/// The `explain_function` prompt's text; `<address>` is the function.
pub(crate) const EXPLAIN_FUNCTION: &str = "Explain the function at <address>.\n\
     1. function_summary(<address>) for its shape, callers, callees and strings.\n\
     2. decompile(<address>); if a callee is unnamed and small, decompile it too so \
     the call reads meaningfully; use read(kind=cstr/ptr) on globals it touches.\n\
     3. xrefs to see how callers use it (arguments, return value).\n\
     4. Write: purpose in one sentence, parameters and return value, side effects, \
     notable constants or strings, and anything suspicious. Then propose a name for \
     the function and for each global it uses and apply them with \
     set_name(dry_run=false); attach a one-line set_comment at the entry.";

/// Every playbook by its prompt's name: the text, and the argument the text
/// leaves as `<argument>` for the prompt or the resource to fill.
pub(crate) const PLAYBOOKS: &[(&str, &str, Option<&str>)] = &[
    ("explain_function", EXPLAIN_FUNCTION, Some("address")),
    ("find_check", FIND_CHECK, Some("what")),
    ("protocol", PROTOCOL, None),
    ("triage", TRIAGE, None),
];

/// Returns a playbook's text with its argument filled in.
///
/// # Arguments
///
/// * `name` - The prompt's name (`find_check`).
/// * `argument` - The value of the argument its text leaves open; `None`
///   leaves `<what>` or `<address>` for the reader.
///
/// # Returns
///
/// The text, or `None` for a name no prompt has.
pub(crate) fn playbook(name: &str, argument: Option<&str>) -> Option<String> {
    let &(_, text, open) = PLAYBOOKS.iter().find(|p| p.0 == name)?;
    Some(match (open, argument) {
        (Some(open), Some(value)) => text.replace(&format!("<{open}>"), value),
        _ => text.to_owned(),
    })
}

/// The instructions up to the prompts: where to start and the tools of a
/// session, each tool written `{name}` and filled from the tool router.
const WORKFLOW: &str = "borer: agent-native binary analysis (x86/x64 PE/ELF/Mach-O; arm64 \
     functions, calls, references, disassembly and emulate/run, no decompile yet). Start: {load_binary}, then query borer://triage: what the file is, how it is \
     protected, what it can do, and the functions to read first ({load_binary} already \
     answers the summary {binary_info} repeats). Then {function_summary} triages a \
     function and {decompile} gives pseudo-C, both ending with the resources its facts \
     point at next (`# next: borer://solve/<addr>`); {find_function_by_string}, {strings}, \
     {symbols}, {search}, {find_crypto_constants} and {xrefs} locate code; {disassemble_function}, {cfg} and \
     {callgraph} go deeper; {read} and {hexdump} read data. Every `address` accepts \
     0x-hex (always the address), a name (function, import, overlay name), or bare \
     decimal digits; a name wins over bare text that also reads as a number, and one \
     nothing matches is answered with the nearest names. {set_name}, {set_comment} \
     (one opening with ? is an open question) and {set_type} (user structs whose \
     fields decompile then names) annotate, dry-run by default; {save_project} \
     persists them. For anything no single tool answers, {script} runs a sandboxed \
     Rhai script over the program in one call; its query(uri) reads any resource, \
     rows(uri) its table as maps, and help(\"query\") lists every resource. \
     Outputs are capped and paged; count_only and filter keep them small. An answer of \
     512 bytes or more ends with `# since=<tag>` (a mermaid graph: `%% since=<tag>`); \
     the same request with \"since\": \"<tag>\" added (on a URI: !since=<tag>) answers \
     with a one-line note if nothing changed, else only the changed lines.";

/// The instructions' resource sentence before the groups, tools written as
/// in [`WORKFLOW`].
const RESOURCES_LEAD: &str = "Resources are read by URI through resources/read or {query}; a \
     template read without its argument (borer://emulate) gives its grammar and an \
     example, and borer://help lists every one. A listing pages with !offset=<n> and \
     !limit=<n> on its URI, and borer://session says what this session loaded, \
     annotated and was answered. By intent:";

/// The instructions after the resources: the live tools and the reload.
const LIVE: &str = "Live: {live_attach}(process) opens the running program read-only and \
     maps the binary onto it; then {live_object} reads an object by its class's fields, \
     {live_instances} finds a class's objects by vtable, {live_read} reads typed values, \
     and {live_watch}(name, address) then {live_watch}(name) shows what changed; every \
     live address may be a static address or a name. After a rebuild of borer, \
     {reload} restarts the server in place.";

/// The resources by what an agent wants of them: every resource name in
/// exactly one group, which the instructions list them under.
const INTENTS: &[(&str, &[&str])] = &[
    ("start", &["triage", "info", "help", "playbook", "about"]),
    (
        "run code",
        &["emulate", "run", "solve", "scenario", "scenarios", "oracle"],
    ),
    (
        "data flow",
        &["taint", "layout", "fields", "fieldrefs", "calls", "why"],
    ),
    (
        "protection",
        &[
            "protection",
            "antianalysis",
            "checks",
            "capabilities",
            "dynimports",
            "iocs",
            "hashes",
        ],
    ),
    (
        "obfuscation",
        &["flat", "vm", "devirt", "unpack", "hidden", "stackstrings"],
    ),
    (
        "builds",
        &[
            "diff",
            "difffn",
            "carry",
            "migrate",
            "anchors",
            "changes",
            "fingerprint",
            "exportpack",
        ],
    ),
    (
        "protocol",
        &[
            "vslot", "schema", "schemas", "encode", "encodes", "senders", "hooks", "protocol",
            "messages", "ports", "attrs",
        ],
    ),
    (
        "classes",
        &[
            "classes",
            "singletons",
            "map",
            "shape",
            "asserts",
            "sources",
            "enums",
            "qt",
        ],
    ),
    (
        "code",
        &["function", "decompile", "disasm", "grep", "index"],
    ),
    ("session", &["session", "annotations", "packs", "script"]),
];

/// Every resource name the tables list, fixed and template, each once, in
/// table order.
fn resource_names() -> Vec<&'static str> {
    let mut names: Vec<&str> = Vec::new();
    for name in RESOURCES
        .iter()
        .map(|r| resource_name(r.0))
        .chain(RESOURCE_TEMPLATES.iter().map(|t| resource_name(t.0)))
    {
        if !names.contains(&name) {
            names.push(name);
        }
    }
    names
}

/// Builds the server's instructions from what it serves.
///
/// Each `{tool}` in the prose is filled from the tool router, the prompts
/// are listed from the prompt router with their arguments, and the
/// resources are listed by intent from the tables: a group's name the
/// tables no longer list is left out, and one no group holds is listed
/// under `other`, so the instructions name what the server serves.
///
/// # Arguments
///
/// * `tools` - The tool router's names.
/// * `prompts` - The prompt router's prompts.
///
/// # Returns
///
/// The instructions.
pub(crate) fn instructions(tools: &[String], prompts: &[Prompt]) -> String {
    let listed = resource_names();
    let mut groups: Vec<String> = INTENTS
        .iter()
        .filter_map(|&(intent, names)| {
            let kept: Vec<&str> = names
                .iter()
                .copied()
                .filter(|n| listed.contains(n))
                .collect();
            (!kept.is_empty()).then(|| format!("{intent}: {}", kept.join(", ")))
        })
        .collect();
    let other: Vec<&str> = listed
        .iter()
        .copied()
        .filter(|n| !INTENTS.iter().any(|(_, names)| names.contains(n)))
        .collect();
    if !other.is_empty() {
        groups.push(format!("other: {}", other.join(", ")));
    }
    let prompts: Vec<String> = prompts
        .iter()
        .map(|p| {
            let arguments: Vec<&str> = p
                .arguments
                .iter()
                .flatten()
                .map(|a| a.name.as_str())
                .collect();
            if arguments.is_empty() {
                p.name.clone()
            } else {
                format!("{}({})", p.name, arguments.join(", "))
            }
        })
        .collect();
    let text = format!(
        "{WORKFLOW}\nPrompts, each also a resource the agent can read, borer://playbook/<name>: {}.\n{RESOURCES_LEAD} {}.\n{LIVE}",
        prompts.join(", "),
        groups.join("; ")
    );
    with_tools(&text, tools)
}

/// Fills each `{name}` naming a tool with the name; any other brace is
/// left as it is.
///
/// # Arguments
///
/// * `text` - The prose.
/// * `tools` - The tool router's names.
fn with_tools(text: &str, tools: &[String]) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(open) = rest.find('{') {
        out.push_str(&rest[..open]);
        let after = &rest[open + 1..];
        match after
            .split_once('}')
            .filter(|(name, _)| tools.iter().any(|t| t == name))
        {
            Some((name, tail)) => {
                out.push_str(name);
                rest = tail;
            }
            None => {
                out.push('{');
                rest = after;
            }
        }
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod tests {
    use super::{INTENTS, PLAYBOOKS, instructions, playbook, resource_names};
    use crate::BorerServer;

    /// The tool router's names.
    fn tools() -> Vec<String> {
        BorerServer::tool_router()
            .list_all()
            .into_iter()
            .map(|t| t.name.into_owned())
            .collect()
    }

    /// The instructions name what the server serves, and only that.
    ///
    /// Every `{tool}` names a tool the router has, every prompt appears
    /// once with its arguments, every resource is in exactly one intent
    /// group and no group names a resource the tables lack, the workflow
    /// starts at the triage, and the whole fits the budget smoke checks.
    ///
    /// # Panics
    ///
    /// When a name is unknown, missing or repeated, or the text outgrows
    /// its budget.
    #[test]
    fn the_instructions_name_what_the_server_serves() {
        /// The instructions' budget in bytes, as `scripts/smoke.py` holds it.
        const BUDGET: usize = 3600;
        let prompts = BorerServer::prompt_router().list_all();
        let text = instructions(&tools(), &prompts);
        assert!(!text.contains('{') && !text.contains('}'), "{text}");
        assert!(
            text.contains("Start: load_binary, then query borer://triage: "),
            "{text}"
        );
        assert!(text.len() < BUDGET, "{} bytes: {text}", text.len());
        let line = text
            .lines()
            .find_map(|l| l.strip_prefix("Prompts, "))
            .unwrap_or_default();
        let named: Vec<&str> = line
            .split_once(": ")
            .map_or("", |(_, names)| names)
            .trim_end_matches('.')
            .split(", ")
            .collect();
        let expected: Vec<String> = prompts
            .iter()
            .map(|p| match p.name.as_str() {
                "find_check" => "find_check(what)".to_owned(),
                "explain_function" => "explain_function(address)".to_owned(),
                other => other.to_owned(),
            })
            .collect();
        assert_eq!(named, expected, "{text}");
        let listed = resource_names();
        let grouped: Vec<&str> = INTENTS
            .iter()
            .flat_map(|(_, names)| names.iter().copied())
            .collect();
        for name in &listed {
            assert_eq!(
                grouped.iter().filter(|g| *g == name).count(),
                1,
                "{name} is not in exactly one intent group"
            );
        }
        for name in &grouped {
            assert!(listed.contains(name), "{name} is grouped but not listed");
        }
        assert!(!text.contains("other: "), "{text}");
    }

    /// Every template is reachable from a `# next:` hint, a playbook or the
    /// instructions, so no template is one an agent can only find by
    /// listing resources; and every resource a hint names is a template.
    ///
    /// # Panics
    ///
    /// When a template is reachable from nothing, or a hint names a
    /// resource the tables lack.
    #[test]
    fn every_template_is_reachable_from_a_hint_a_playbook_or_the_instructions() {
        let hinted = borer_engine::analysis::render::NEXT_RESOURCES;
        let templates: Vec<&str> = crate::RESOURCE_TEMPLATES
            .iter()
            .map(|t| crate::resource_name(t.0))
            .collect();
        for name in hinted {
            assert!(templates.contains(&name), "a hint names borer://{name}");
        }
        let text = instructions(&tools(), &BorerServer::prompt_router().list_all());
        let words: Vec<&str> = text
            .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .collect();
        let cited: Vec<String> = PLAYBOOKS
            .iter()
            .flat_map(|&(_, playbook, _)| playbook.split("borer://").skip(1))
            .map(|rest| rest.chars().take_while(char::is_ascii_lowercase).collect())
            .collect();
        for name in &templates {
            assert!(
                hinted.contains(name) || cited.iter().any(|c| c == name) || words.contains(name),
                "borer://{name} is reachable from nothing"
            );
        }
    }

    /// A playbook cites only tools and resources the server has.
    ///
    /// A word followed by `(` or holding `_` is a tool or one of the
    /// parameters a playbook passes; a `borer://` name is a resource. A
    /// playbook naming a renamed tool or resource would send the agent to
    /// nothing.
    ///
    /// # Panics
    ///
    /// When a playbook cites a name the server lacks.
    #[test]
    fn every_name_a_playbook_cites_exists() {
        /// Parameters a playbook spells out, which are not tools.
        const PARAMETERS: &[&str] = &["dry_run"];
        let tools = tools();
        let resources = resource_names();
        let prompts = BorerServer::prompt_router().list_all();
        assert_eq!(
            prompts.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(),
            PLAYBOOKS.iter().map(|p| p.0).collect::<Vec<_>>(),
            "a playbook for every prompt"
        );
        for &(name, text, _) in PLAYBOOKS {
            let mut rest = text;
            while let Some(at) = rest.find("borer://") {
                rest = &rest[at + "borer://".len()..];
                let cited: String = rest.chars().take_while(char::is_ascii_lowercase).collect();
                assert!(
                    resources.contains(&cited.as_str()),
                    "{name} cites borer://{cited}"
                );
            }
            let word_char = |c: char| c.is_ascii_alphanumeric() || c == '_';
            for piece in text.split_inclusive(|c: char| !word_char(c)) {
                let (word, called) = match piece.strip_suffix('(') {
                    Some(word) => (word, true),
                    None => (piece.trim_end_matches(|c: char| !word_char(c)), false),
                };
                if word.is_empty() || !(word.contains('_') || called) {
                    continue;
                }
                assert!(
                    tools.iter().any(|t| t == word) || PARAMETERS.contains(&word),
                    "{name} cites {word}"
                );
            }
        }
        assert_eq!(
            playbook("find_check", Some("serial")).map(|t| t.matches("serial").count()),
            Some(2)
        );
        assert!(playbook("nosuch", None).is_none());
        let described = crate::RESOURCE_TEMPLATES
            .iter()
            .find(|t| t.0 == "borer://playbook/{name}")
            .map(|t| t.1)
            .unwrap_or_default();
        for p in &prompts {
            assert!(
                described.contains(p.name.as_str()),
                "{}: {described}",
                p.name
            );
        }
    }
}
