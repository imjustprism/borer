//! About: everything the analysis knows about one name, from every catalog,
//! in one answer.
//!
//! An agent meeting a name (`HitPoints`, `MoveCommand`,
//! `ClientMovementProperty`, `StillAliveTask::OnTick`) would otherwise ask
//! the attribute table, the class map, the message routes, the protocol
//! tables and the function summary in turn, most of them answering
//! nothing. This resolves the name against all of them and returns each
//! section that knows it, with the next reads worth making.

use std::fmt::Write as _;

use super::encode::{compact_writes, encoding_for_class};
use super::map::classes as map_classes;
use super::ports::{Route, routes};
use super::schema::{compact_fields, schema_for_class};
use super::{Analysis, Overlay, name_of, resolve, slot_name_of};
use crate::program::Program;

/// Most virtuals, routes or candidates listed in one section.
const LIST_MAX: usize = 24;

/// The classes a name can mean: itself when a class has that name, else
/// every class whose last segment is the name.
///
/// # Arguments
///
/// * `analysis` - The recovered classes.
/// * `name` - The name asked about.
fn classes_named(analysis: &Analysis, name: &str) -> Vec<String> {
    if analysis.classes.by_name.contains_key(name) {
        return vec![name.to_owned()];
    }
    if name.contains("::") {
        return Vec::new();
    }
    analysis
        .classes
        .by_name
        .keys()
        .filter(|k| k.rsplit("::").next() == Some(name))
        .cloned()
        .collect()
}

/// The functions named `Handle<Short>` for a command's short name.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `short` - The command's last name segment.
fn handlers_of(analysis: &Analysis, overlay: &Overlay, short: &str) -> Vec<String> {
    let want = format!("Handle{short}");
    analysis
        .functions
        .iter()
        .map(|f| name_of(analysis, overlay, f.entry))
        .filter(|n| n.rsplit("::").next() == Some(want.as_str()))
        .collect()
}

/// Appends one section on a class: its role, parent, instance, virtuals,
/// and what its role adds (routes for a component, handlers for a message,
/// the wire for a command).
///
/// # Arguments
///
/// * `out` - The answer so far.
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `class` - The class.
/// * `all_routes` - Every message route.
fn class_section(
    out: &mut String,
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
    all_routes: &[Route],
) {
    let Some(info) = analysis.classes.by_name.get(class) else {
        return;
    };
    let mapped = map_classes(analysis, overlay)
        .into_iter()
        .find(|c| c.name == class);
    let role = mapped.as_ref().map_or("class", |c| c.role.as_str());
    // INVARIANT: the count is the one `class` prints, the method index's,
    // not the namespace map's.
    let methods = super::classes::methods_of(analysis, overlay, class).len();
    let _ = writeln!(
        out,
        "## class {class}: {role}, parent {}, {methods} methods, instance {}",
        info.parent.as_deref().unwrap_or("-"),
        mapped
            .as_ref()
            .and_then(|c| c.instance.as_deref())
            .unwrap_or("-")
    );
    if let Some(table) = info.vtable {
        let slots: Vec<String> = info
            .slots
            .iter()
            .take(LIST_MAX)
            .enumerate()
            .map(|(k, &f)| format!("[{k}] {}", slot_name_of(analysis, overlay, f)))
            .collect();
        let _ = writeln!(out, "vtable {table:#x}: {}", slots.join(", "));
    }
    let accepts: Vec<&Route> = all_routes.iter().filter(|r| r.class == class).collect();
    if !accepts.is_empty() {
        let _ = writeln!(out, "## accepts {} messages", accepts.len());
        out.push_str("message\thandler\n");
        for r in accepts.iter().take(LIST_MAX) {
            let _ = writeln!(out, "{}\t{}", r.message, r.handler_label(analysis, overlay));
        }
    }
    let handled: Vec<&Route> = all_routes.iter().filter(|r| r.message == class).collect();
    if !handled.is_empty() {
        let _ = writeln!(out, "## handled by {} components", handled.len());
        out.push_str("component\thandler\n");
        for r in handled.iter().take(LIST_MAX) {
            let _ = writeln!(out, "{}\t{}", r.class, r.handler_label(analysis, overlay));
        }
    }
    if role == "command" {
        let short = class.rsplit("::").next().unwrap_or(class);
        let built = super::senders::constructed_by(analysis, overlay, class);
        let names: Vec<String> = built
            .senders
            .iter()
            .take(LIST_MAX)
            .map(|&s| name_of(analysis, overlay, s))
            .collect();
        let _ = writeln!(
            out,
            "## wire\nsent by: {}\nsend sites: {}\nhandler: {}\nencodes: {}\ndecodes: {}",
            if names.is_empty() {
                "-".to_owned()
            } else {
                names.join(", ")
            },
            built
                .sites
                .iter()
                .take(LIST_MAX)
                .map(|(site, _)| format!("{site:#x}"))
                .collect::<Vec<_>>()
                .join(" "),
            {
                let h = handlers_of(analysis, overlay, short);
                if h.is_empty() {
                    "-".to_owned()
                } else {
                    h.join(", ")
                }
            },
            encoding_for_class(program, analysis, overlay, class).map_or_else(
                || "-".to_owned(),
                |(e, w)| format!("{e:#x} {}", compact_writes(&w.fields))
            ),
            schema_for_class(program, analysis, overlay, class).map_or_else(
                || "-".to_owned(),
                |(e, s)| format!("{e:#x} {}", compact_fields(&s.fields))
            )
        );
    }
}

/// Everything the analysis knows about `name`: the attribute, the class or
/// classes, the message routes and the wire, and the function, each a
/// section of its own.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `name` - An attribute (name or code), a class (qualified or its last
///   segment), or a function (name or address).
#[must_use]
pub fn about_tsv(program: &Program, analysis: &Analysis, overlay: &Overlay, name: &str) -> String {
    let name = name.trim();
    let key = overlay.fingerprint();
    let mut out = String::new();
    let mut found = Vec::new();
    let attrs = analysis.derived.get_or_build_named("attrs", key, (), || {
        super::attributes::catalog(program, analysis, overlay)
    });
    let q = name.to_lowercase();
    if attrs.attrs.iter().any(|a| a.name.to_lowercase() == q) {
        found.push("attribute");
        let _ = writeln!(out, "## attribute {name}");
        out.push_str(&super::attributes::catalog_tsv(
            program, analysis, overlay, name, 1,
        ));
    }
    let all_routes = analysis
        .derived
        .get_or_build_named("ports", key, (), || routes(program, analysis, overlay));
    let classes = classes_named(analysis, name);
    match classes.as_slice() {
        [] => {}
        [one] => {
            found.push("class");
            class_section(&mut out, program, analysis, overlay, one, &all_routes);
        }
        many => {
            found.push("classes");
            let _ = writeln!(out, "## {} classes end in {name}", many.len());
            for c in many.iter().take(LIST_MAX) {
                let _ = writeln!(out, "{c}");
            }
        }
    }
    if let Ok(entry) = resolve(program, analysis, overlay, name)
        && let Some(f) = analysis.function_at(entry)
        && let Some(summary) = super::render::function_summary(program, analysis, overlay, f.entry)
    {
        found.push("function");
        let _ = writeln!(out, "## function {}", name_of(analysis, overlay, f.entry));
        out.push_str(&summary);
        if !summary.ends_with('\n') {
            out.push('\n');
        }
    }
    let head = if found.is_empty() {
        format!(
            "# nothing is named {}; borer://map, borer://attrs/<filter>, borer://ports/<filter> and borer://grep/<text> search wider\n",
            crate::text::quoted(name)
        )
    } else {
        format!(
            "# {} is known as: {}\n",
            crate::text::quoted(name),
            found.join(", ")
        )
    };
    head + out.as_str()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A name nothing knows says so and points wider; a function name
    /// finds the function's summary.
    ///
    /// # Panics
    ///
    /// When a section is missing or extra.
    #[test]
    fn about_answers_from_every_catalog_that_knows_the_name() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let none = about_tsv(&p, &a, &o, "NoSuchThing");
        assert!(
            none.starts_with("# nothing is named 'NoSuchThing'"),
            "{none}"
        );
        let f = about_tsv(&p, &a, &o, "sub_1000");
        assert!(f.starts_with("# 'sub_1000' is known as: function\n"), "{f}");
        assert!(f.contains("## function sub_1000\n"), "{f}");
    }
}
