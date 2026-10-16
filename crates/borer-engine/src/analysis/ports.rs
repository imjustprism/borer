//! Ports: which component accepts which message, and the function each
//! message is dispatched to.
//!
//! A message port (a component that receives messages: a property, a
//! manager, a UI handler) declares the messages it accepts in one virtual,
//! handing each message's
//! id to a helper that inserts it into the port's id list, and handles them
//! in another, comparing the incoming message's id against each and calling
//! the function that handles it or handling it inline. Reading both for
//! every port answers "who handles this message, and where" for the whole
//! program in one table. The helpers are a framework's own, so a pack names
//! them (`[messages] accept`); with none named there are no routes.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::attributes::{assigned_before, call_args, global_addr};
use super::classes::deref_pointee;
use super::{Analysis, Overlay, RefKind, name_of, plain_text_cached};
use crate::program::Program;

/// Fewest ports worth a worker each.
const PAR_MIN: usize = 8;

/// One message a port accepts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Route {
    /// The port's class.
    pub class: String,
    /// The message's id global.
    pub id: u64,
    /// The message's class, from the catalog or the branch's cast.
    pub message: String,
    /// The function the dispatch calls for it, when it calls one.
    pub handler: Option<u64>,
    /// The handler's name when the text calls one the analysis cannot
    /// resolve.
    pub handler_text: Option<String>,
    /// The dispatch virtual, when one tests for the id.
    pub dispatch: Option<u64>,
    /// The virtual declaring the message accepted.
    pub accept: u64,
}

impl Route {
    /// The handler as a table spells it: the function's name, else the
    /// text's name for it, else `inline` when a dispatch tests for the id
    /// without calling anything, else `-`.
    ///
    /// # Arguments
    ///
    /// * `analysis` - Discovery results.
    /// * `overlay` - Names in force.
    #[must_use]
    pub fn handler_label(&self, analysis: &Analysis, overlay: &Overlay) -> String {
        match (self.handler, &self.handler_text) {
            (Some(h), _) => name_of(analysis, overlay, h),
            (None, Some(t)) => t.clone(),
            (None, None) if self.dispatch.is_some() => "inline".to_owned(),
            (None, None) => "-".to_owned(),
        }
    }
}

/// What a dispatch does for one id it tests.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Branch {
    /// The handler the branch calls, as the text names it.
    handler: Option<String>,
    /// The message class the branch's cast names.
    message: Option<String>,
}

/// Which way an `if` tests an id.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Test {
    /// `==`: the handling branch is the block.
    Equal,
    /// `!=`: the handling branch follows the block, to the end of the
    /// enclosing one.
    NotEqual,
}

/// Tells whether a function name is one of the accepted-id helpers a pack
/// names.
///
/// # Arguments
///
/// * `name` - The function's name.
/// * `helpers` - The helpers' names, from `[messages] accept`.
fn is_accept_helper(name: &str, helpers: &[&str]) -> bool {
    helpers.contains(&name)
}

/// The id globals a declaring virtual inserts, in order.
///
/// # Arguments
///
/// * `text` - The virtual's pseudo-C.
/// * `helpers` - The helpers' names as the text spells them.
fn accepted_ids(text: &str, helpers: &[String]) -> Vec<u64> {
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let mut out: Vec<u64> = Vec::new();
    for (at, line) in lines.iter().enumerate() {
        for helper in helpers {
            let Some(args) = call_args(line, helper) else {
                continue;
            };
            let Some(var) = args.last().and_then(|a| a.strip_prefix('&')) else {
                continue;
            };
            let id =
                global_addr(var).or_else(|| assigned_before(&lines, at, var).and_then(global_addr));
            if let Some(id) = id
                && !out.contains(&id)
            {
                out.push(id);
            }
        }
    }
    out
}

/// Where a handling branch's lines run: inside an `==` test's block, or
/// after a `!=` test's block to the end of the enclosing one.
///
/// # Arguments
///
/// * `lines` - The dispatch's lines, trimmed.
/// * `at` - Index of the test.
/// * `test` - Which way the test goes.
fn branch(lines: &[&str], at: usize, test: Test) -> std::ops::Range<usize> {
    let mut depth = 0i32;
    let mut close = lines.len();
    for (k, line) in lines.iter().enumerate().skip(at) {
        depth += i32::try_from(line.matches('{').count()).unwrap_or(0);
        depth -= i32::try_from(line.matches('}').count()).unwrap_or(0);
        if k > at && depth <= 0 {
            close = k;
            break;
        }
    }
    if test == Test::Equal {
        return at + 1..close;
    }
    let mut depth = 0i32;
    let mut end = lines.len();
    for (k, line) in lines.iter().enumerate().skip(close + 1) {
        depth += i32::try_from(line.matches('{').count()).unwrap_or(0);
        depth -= i32::try_from(line.matches('}').count()).unwrap_or(0);
        if depth < 0 {
            end = k;
            break;
        }
    }
    close + 1..end.max(close + 1)
}

/// What a dispatch does for each id it tests: the handler it calls, the
/// message class its cast names, or neither.
///
/// # Arguments
///
/// * `text` - The dispatch's pseudo-C.
/// * `ids` - The ids to look for.
/// * `port` - The dispatch's port parameter (`a1` or `this`).
fn dispatched(text: &str, ids: &[u64], port: &str) -> BTreeMap<u64, Branch> {
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let mut out = BTreeMap::new();
    for (at, line) in lines.iter().enumerate() {
        let Some(cond) = line.strip_prefix("if (") else {
            continue;
        };
        let (test, lhs) = if let Some((l, _)) = cond.split_once(" == ") {
            (Test::Equal, l)
        } else if let Some((l, _)) = cond.split_once(" != ") {
            (Test::NotEqual, l)
        } else {
            continue;
        };
        let Some(id) = global_addr(lhs) else {
            continue;
        };
        if !ids.contains(&id) || out.contains_key(&id) {
            continue;
        }
        let region = branch(&lines, at, test);
        let mut handler = None;
        let mut message = None;
        for l in &lines[region] {
            if l.starts_with("if (")
                && global_addr(l.trim_start_matches("if (").split(' ').next().unwrap_or(""))
                    .is_some()
            {
                break;
            }
            if message.is_none()
                && let Some(class) = deref_pointee(l)
                && class.contains("::")
            {
                message = Some(class.to_owned());
            }
            if handler.is_none()
                && let Some(open) = l.find(&format!("({port}"))
            {
                let head = &l[..open];
                let name = head
                    .rsplit(|c: char| {
                        !(c.is_ascii_alphanumeric() || matches!(c, '_' | ':' | '<' | '>' | ','))
                    })
                    .next()
                    .unwrap_or("");
                let after = &l[open + 1 + port.len()..];
                if !name.is_empty()
                    && !name.contains("operator")
                    && (after.starts_with(',') || after.starts_with(')'))
                {
                    handler = Some(name.to_owned());
                }
            }
        }
        out.insert(id, Branch { handler, message });
    }
    out
}

/// The topmost class holding `f` in its table: the one whose parent does
/// not hold it at the same slot.
///
/// # Arguments
///
/// * `analysis` - The recovered classes.
/// * `f` - The function.
fn owner_of(analysis: &Analysis, f: u64) -> Option<(String, usize)> {
    let holders: Vec<(&String, usize)> = analysis
        .classes
        .by_name
        .iter()
        .filter_map(|(name, info)| info.slots.iter().position(|&s| s == f).map(|k| (name, k)))
        .collect();
    holders
        .iter()
        .find(|(name, k)| {
            analysis
                .classes
                .by_name
                .get(*name)
                .and_then(|c| c.parent.as_ref())
                .and_then(|p| analysis.classes.by_name.get(p))
                .is_none_or(|p| p.slots.get(*k) != Some(&f))
        })
        .or_else(|| holders.first())
        .map(|(name, k)| ((*name).clone(), *k))
}

/// The message class each wanted id belongs to: the class whose own id
/// getter, a virtual that is `lea rax, [id]; ret`, hands it out.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `wanted` - The id globals to name.
fn id_owners(
    program: &Program,
    analysis: &Analysis,
    wanted: &BTreeSet<u64>,
) -> BTreeMap<u64, String> {
    let Some(bitness) = program.arch.bitness() else {
        return BTreeMap::new();
    };
    let mut getters: BTreeMap<u64, u64> = BTreeMap::new();
    for info in analysis.classes.by_name.values() {
        for &f in &info.slots {
            if getters.contains_key(&f) || analysis.function(f).is_none_or(|x| x.instr_count != 2) {
                continue;
            }
            if let Some(g) = super::messages::returned_global(program, f, bitness)
                && wanted.contains(&g)
            {
                getters.insert(f, g);
            }
        }
    }
    getters
        .into_iter()
        .filter_map(|(f, g)| owner_of(analysis, f).map(|(class, _)| (g, class)))
        .collect()
}

/// Every message every port accepts, with its dispatch and handler.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `overlay` - Names in force.
///
/// # Returns
///
/// The routes by class, then id order of declaration.
#[must_use]
pub fn routes(program: &Program, analysis: &Analysis, overlay: &Overlay) -> Vec<Route> {
    let overlay_key = overlay.fingerprint();
    let named = analysis.packs.list("messages", "accept");
    if named.is_empty() {
        return Vec::new();
    }
    let helpers: Vec<(u64, String)> = analysis
        .functions
        .iter()
        .map(|f| (f.entry, name_of(analysis, overlay, f.entry)))
        .filter(|(_, n)| is_accept_helper(n, &named))
        .collect();
    if helpers.is_empty() {
        return Vec::new();
    }
    let helper_names: Vec<String> = helpers.iter().map(|(_, n)| n.clone()).collect();
    let accepts: Vec<u64> = helpers
        .iter()
        .filter_map(|(e, _)| analysis.xrefs.get(e))
        .flatten()
        .filter(|s| s.kind == RefKind::Call)
        .filter_map(|s| s.from_entry)
        .collect::<BTreeSet<u64>>()
        .into_iter()
        .collect();
    let declared: Vec<(u64, Vec<u64>)> = super::striped_with(
        &accepts,
        PAR_MIN,
        || (),
        |(), &accept| {
            let text = plain_text_cached(program, analysis, overlay, overlay_key, accept)?;
            let ids = accepted_ids(&text, &helper_names);
            (!ids.is_empty()).then_some((accept, ids))
        },
    )
    .into_iter()
    .flatten()
    .flatten()
    .collect();
    let wanted: BTreeSet<u64> = declared
        .iter()
        .flat_map(|(_, ids)| ids.iter().copied())
        .collect();
    let names = id_owners(program, analysis, &wanted);
    let found = super::striped_with(
        &declared,
        PAR_MIN,
        || (),
        |(), (accept, ids)| {
            let accept = *accept;
            let ids = ids.clone();
            let (class, _) = owner_of(analysis, accept)?;
            let slots = analysis
                .classes
                .by_name
                .get(&class)
                .map(|c| c.slots.clone())
                .unwrap_or_default();
            let dispatch = slots
                .iter()
                .copied()
                .filter(|&s| s != accept)
                .map(|s| {
                    let hits =
                        ids.iter()
                            .filter(|id| {
                                analysis.xrefs.get(id).is_some_and(|refs| {
                                    refs.iter().any(|r| r.from_entry == Some(s))
                                })
                            })
                            .count();
                    (hits, s)
                })
                .filter(|&(hits, _)| hits > 0)
                .max_by_key(|&(hits, s)| (hits, std::cmp::Reverse(s)))
                .map(|(_, s)| s);
            let handled = dispatch
                .and_then(|d| {
                    let text = plain_text_cached(program, analysis, overlay, overlay_key, d)?;
                    let port = if text.contains("(this, ") || text.contains("(this)") {
                        "this"
                    } else {
                        "a1"
                    };
                    Some(dispatched(&text, &ids, port))
                })
                .unwrap_or_default();
            let rows: Vec<Route> = ids
                .into_iter()
                .map(|id| {
                    let Branch {
                        handler: handler_text,
                        message: cast,
                    } = handled.get(&id).cloned().unwrap_or_default();
                    let handler = handler_text
                        .as_deref()
                        .and_then(|n| super::resolve(program, analysis, overlay, n).ok());
                    Route {
                        class: class.clone(),
                        id,
                        message: match names.get(&id) {
                            Some(n) if !n.starts_with("class_") => n.clone(),
                            owner => cast
                                .or_else(|| owner.cloned())
                                .unwrap_or_else(|| format!("id@{id:#x}")),
                        },
                        handler,
                        handler_text: if handler.is_some() {
                            None
                        } else {
                            handler_text
                        },
                        dispatch,
                        accept,
                    }
                })
                .collect();
            Some(rows)
        },
    );
    let mut out: Vec<Route> = found.into_iter().flatten().flatten().flatten().collect();
    out.sort_by(|a, b| a.class.cmp(&b.class).then(a.message.cmp(&b.message)));
    out.dedup_by(|a, b| a.class == b.class && a.id == b.id);
    out
}

/// Renders every route as a `#`-headed table.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `filter` - Case-insensitive substring of the port's or the message's
///   class; empty for all.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn routes_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    filter: &str,
    limit: usize,
) -> String {
    let all = analysis
        .derived
        .get_or_build_named("ports", overlay.fingerprint(), (), || {
            routes(program, analysis, overlay)
        });
    let ports: BTreeSet<&str> = all.iter().map(|r| r.class.as_str()).collect();
    let q = filter.to_lowercase();
    let picked: Vec<&Route> = all
        .iter()
        .filter(|r| {
            q.is_empty()
                || r.class.to_lowercase().contains(&q)
                || r.message.to_lowercase().contains(&q)
        })
        .collect();
    let called = picked
        .iter()
        .filter(|r| r.handler.is_some() || r.handler_text.is_some())
        .count();
    let shown = picked.len().min(limit);
    let mut out = format!(
        "# {} ports accept {} messages; {} routes shown here, {called} dispatched to a function, showing {shown}",
        ports.len(),
        all.len(),
        picked.len()
    );
    if analysis.packs.list("messages", "accept").is_empty() {
        out.push_str("; no pack names the accept helpers (`[messages] accept` lines in a pack)");
    }
    out.push('\n');
    out.push_str("port\tmessage\thandler\tdispatch\n");
    for r in picked.into_iter().take(limit) {
        let handler = r.handler_label(analysis, overlay);
        let dispatch = r
            .dispatch
            .map_or_else(|| "-".to_owned(), |d| name_of(analysis, overlay, d));
        let _ = writeln!(out, "{}\t{}\t{handler}\t{dispatch}", r.class, r.message);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One port's accept virtual: two ids, each inserted if absent.
    const ACCEPT: &str = "uint64_t rax, home_0;
home_0 = &g64_1413737c0;
rax = Util::Array<Messaging::Id const *>::BinarySearchIndex(a1 + 48, &home_0);
if (rax == -1) {
  home_0 = &g64_1413737c0;
  Util::Array<Messaging::Id const *>::InsertSorted(a1 + 48, &home_0);
}
home_0 = &g64_1413eb744;
rax = Util::Array<Messaging::Id const *>::BinarySearchIndex(a1 + 48, &home_0);
if (rax == -1) {
  home_0 = &g64_1413eb744;
  Util::Array<Messaging::Id const *>::InsertSorted(a1 + 48, &home_0);
}
";

    /// Its dispatch: one `!=` test around the rest, `==` tests with a
    /// handler call, one handled inline under a cast.
    const DISPATCH: &str = "rax = Core::Ptr<Messaging::Message>::operator ->(a2);
rax = rax->vfunc_3();
if (g32_14136fec0 != *(uint32_t*)rax) {
  rax = Core::Ptr<Messaging::Message>::operator ->(a2);
  rax = rax->vfunc_3();
  if (g32_1413737c0 == *(uint32_t*)rax) {
    return Widget::OnMove(a1, a2);
  }
  rax = Core::Ptr<Messaging::Message>::operator ->(a2);
  rax = rax->vfunc_3();
  if (g32_141376c00 == *(uint32_t*)rax) {
    rax = Core::Ptr<Messaging::StartedSkill>::operator ->(a2);
    a1->field_0xd1 = *(uint8_t*)(rax + 0x20) == 0;
  }
  return rax;
}
rax = Core::Ptr<Messaging::OnTick>::operator ->(a2);
return sub_140146334(a1, *(uint32_t*)(rax + 0x20));
";

    /// A declaring virtual yields its ids in order, each once.
    ///
    /// # Panics
    ///
    /// When the ids differ.
    #[test]
    fn accepted_ids_are_read_in_order() {
        let helpers = vec!["Util::Array<Messaging::Id const *>::InsertSorted".to_owned()];
        assert_eq!(
            accepted_ids(ACCEPT, &helpers),
            [0x1_4137_37c0, 0x1_413e_b744]
        );
        let named = ["Util::Array<Messaging::Id const *>::Append"];
        assert!(is_accept_helper(
            "Util::Array<Messaging::Id const *>::Append",
            &named
        ));
        assert!(!is_accept_helper(
            "Util::Array<Messaging::Id const *>::Delete",
            &named
        ));
    }

    /// A dispatch maps an `==` test to the call inside it, an inline branch
    /// to its cast, and a `!=` test to what follows its block.
    ///
    /// # Panics
    ///
    /// When a route differs from the text.
    #[test]
    fn a_dispatch_maps_each_id_to_its_branch() {
        let ids = [0x1_4137_37c0, 0x1_4137_6c00, 0x1_4136_fec0];
        let got = dispatched(DISPATCH, &ids, "a1");
        let branch = |handler: Option<&str>, message: Option<&str>| Branch {
            handler: handler.map(str::to_owned),
            message: message.map(str::to_owned),
        };
        assert_eq!(
            got.get(&0x1_4137_37c0),
            Some(&branch(Some("Widget::OnMove"), None))
        );
        assert_eq!(
            got.get(&0x1_4137_6c00),
            Some(&branch(None, Some("Messaging::StartedSkill")))
        );
        assert_eq!(
            got.get(&0x1_4136_fec0),
            Some(&branch(Some("sub_140146334"), Some("Messaging::OnTick")))
        );
    }

    /// An image with no message ports has an empty table with its header.
    ///
    /// # Panics
    ///
    /// When the header differs.
    #[test]
    fn an_image_without_ports_has_an_empty_table() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let text = routes_tsv(&p, &a, &Overlay::default(), "", 10);
        assert!(text.starts_with("# 0 ports accept 0 messages"), "{text}");
        assert_eq!(
            text.lines().nth(1),
            Some("port\tmessage\thandler\tdispatch")
        );
    }
}
