//! Every call site of one function or import, with the arguments the
//! decompiler resolves at each.

use super::*;
use crate::analysis::decompile::{CallArg, CallSite, call_sites};

/// Most rows one read lists; the rest page with `offset=`.
pub const CALLS_PAGE: usize = 200;

/// Most calling functions decompiled for one read; the rest are counted.
pub const CALLERS_MAX: usize = 500;

/// What a callee is reached through.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Reach {
    /// The callee's name, as a row writes its calls.
    pub(super) name: String,
    /// The callee's entry and those of the thunks jumping to it.
    pub(super) entries: BTreeSet<u64>,
    /// The constant addresses a call reads the callee from: its import
    /// slot, a pointer to it stored in data.
    pub(super) slots: BTreeSet<u64>,
    /// The bare import name, when the callee is an import.
    pub(super) import: Option<String>,
}

impl Reach {
    /// The ways to reach an import: its slot, and every thunk jumping
    /// through the slot.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis, for the thunks.
    /// * `slot` - The import's slot.
    /// * `name` - The import's name as the symbol table spells it.
    pub(super) fn import(a: &Analysis, slot: u64, name: &str) -> Reach {
        let bare = bare_name(name).to_owned();
        Reach {
            name: bare.clone(),
            entries: thunks(a, slot),
            slots: BTreeSet::from([slot]),
            import: Some(bare),
        }
    }

    /// Tells whether a call reaching `target` reaches the callee.
    ///
    /// # Arguments
    ///
    /// * `target` - The call's entry or the constant address it reads.
    fn reaches(&self, target: u64) -> bool {
        self.entries.contains(&target) || self.slots.contains(&target)
    }

    /// Tells whether a function is one of the thunks the callee is reached
    /// through, whose own jump is no call site.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis.
    /// * `entry` - The function.
    fn is_thunk(&self, a: &Analysis, entry: u64) -> bool {
        a.function(entry)
            .and_then(|f| f.thunk)
            .is_some_and(|s| self.slots.contains(&s))
    }
}

/// The entries of the functions that are one jump through `slot`.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `slot` - The slot.
fn thunks(a: &Analysis, slot: u64) -> BTreeSet<u64> {
    a.functions
        .iter()
        .filter(|f| f.thunk == Some(slot))
        .map(|f| f.entry)
        .collect()
}

/// Works out what a resolved callee address is reached through.
///
/// # Arguments
///
/// * `p` - The loaded image, for the import table.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `va` - The resolved address.
///
/// # Errors
///
/// When the address lies inside a function but is not its entry.
pub(super) fn reach_of(p: &Program, a: &Analysis, o: &Overlay, va: u64) -> Result<Reach, String> {
    if let Some(s) = p
        .symbols
        .iter()
        .find(|s| s.kind == SymbolKind::Import && s.addr == va && va != 0)
    {
        return Ok(Reach::import(a, va, &s.name));
    }
    let mut reach = if let Some(f) = a.function(va) {
        let mut entries = BTreeSet::from([va]);
        let mut slots = BTreeSet::new();
        let mut import = None;
        if let Some(slot) = f.thunk {
            entries.extend(thunks(a, slot));
            slots.insert(slot);
            import = p
                .symbols
                .iter()
                .find(|s| s.kind == SymbolKind::Import && s.addr == slot)
                .map(|s| bare_name(&s.name).to_owned());
        }
        Reach {
            name: short_name(a, o, va),
            entries,
            slots,
            import,
        }
    } else if let Some(f) = a.function_at(va) {
        return Err(format!(
            "{va:#x} is inside {} (entry {:#x}), not a function's entry; calls are made to an entry",
            short_name(a, o, f.entry),
            f.entry
        ));
    } else {
        Reach {
            name: format!("*{va:#x}"),
            entries: BTreeSet::new(),
            slots: BTreeSet::from([va]),
            import: None,
        }
    };
    let stored: Vec<u64> = reach
        .entries
        .iter()
        .flat_map(|e| a.xrefs_to(*e))
        .filter(|s| s.kind == RefKind::Table)
        .map(|s| s.va)
        .collect();
    reach.slots.extend(stored);
    Ok(reach)
}

/// One call site found for a callee.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Found {
    /// The calling function's entry.
    pub(super) caller: u64,
    /// The call instruction.
    pub(super) at: u64,
    /// The call as the decompiler recorded it; `None` for a call the
    /// cross-references list but no decompiled text makes.
    pub(super) site: Option<CallSite>,
}

/// Fewest callers worth decompiling across the cores: one large caller
/// takes tens of milliseconds, so even a handful pays for the threads.
const DECOMPILE_PAR_MIN: usize = 8;

/// The call sites of a callee, as many as the decompiled callers make.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(super) struct Gathered {
    /// The sites, in address order.
    pub(super) found: Vec<Found>,
    /// Functions calling the callee or reading its slot.
    pub(super) callers: usize,
    /// Of those, the ones decompiled; the rest are counted, not read.
    pub(super) read: usize,
}

/// Finds every call site of a callee from the decompiled text of its
/// callers.
///
/// The candidates are the functions with a call or a jump to one of the
/// callee's entries or slots, and those reading a slot as data (`mov rsi,
/// [VirtualProtect]` before `call rsi`). Each is decompiled once, through
/// the memo and across the cores, and its recorded calls ([`call_sites`]) that reach the callee
/// are the sites: a call through a register loaded from the slot is found
/// that way too. A call or jump the cross-references list but no text makes
/// (the function does not decompile, or the block was cut) is kept without
/// arguments. The thunks' own jumps are not call sites.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `reach` - What the callee is reached through.
/// * `cap` - Most callers decompiled; the rest are counted.
pub(super) fn gather(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    reach: &Reach,
    cap: usize,
) -> Gathered {
    let mut callers: BTreeSet<u64> = BTreeSet::new();
    let mut branches: BTreeMap<u64, u64> = BTreeMap::new();
    for (target, slot) in reach
        .entries
        .iter()
        .map(|e| (*e, false))
        .chain(reach.slots.iter().map(|s| (*s, true)))
    {
        for s in a.xrefs_to(target) {
            let Some(from) = s.from_entry.filter(|f| !reach.is_thunk(a, *f)) else {
                continue;
            };
            match s.kind {
                RefKind::Call | RefKind::Jmp => {
                    branches.insert(s.va, from);
                    callers.insert(from);
                }
                RefKind::Data if slot => {
                    callers.insert(from);
                }
                RefKind::Data | RefKind::Index | RefKind::Table | RefKind::Ptr => {}
            }
        }
    }
    let read_list: Vec<u64> = callers.iter().take(cap).copied().collect();
    let read = read_list.len();
    let decompiled = crate::analysis::striped_with(
        &read_list,
        DECOMPILE_PAR_MIN,
        || (),
        |(), &c| call_sites(p, a, o, c).unwrap_or_default(),
    );
    let mut found: Vec<Found> = Vec::new();
    for (&caller, sites) in read_list.iter().zip(decompiled) {
        for site in sites.unwrap_or_default() {
            if site.target.is_some_and(|t| reach.reaches(t)) {
                branches.remove(&site.at);
                found.push(Found {
                    caller,
                    at: site.at,
                    site: Some(site),
                });
            }
        }
    }
    let read_set: BTreeSet<u64> = read_list.into_iter().collect();
    found.extend(
        branches
            .into_iter()
            .filter(|(_, caller)| read_set.contains(caller))
            .map(|(at, caller)| Found {
                caller,
                at,
                site: None,
            }),
    );
    found.sort_by_key(|f| (f.at, f.caller));
    found.dedup_by_key(|f| (f.at, f.caller));
    Gathered {
        found,
        callers: callers.len(),
        read,
    }
}

/// How a filter compares an argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cmp {
    /// `aN=v`: equal to a number, containing a text, or unseen for `?`.
    Eq,
    /// `aN!=v`: anything `=` would not keep.
    Ne,
    /// `aN>v`: a constant above the number.
    Gt,
    /// `aN<v`: a constant below the number.
    Lt,
}

/// What a filter compares an argument with.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Want {
    /// A number, compared with a constant argument's value.
    Number(u64),
    /// `?`: a position the lifter recorded nothing for.
    Unseen,
    /// Text, a case-insensitive substring of the argument as written or of
    /// the string it points at.
    Text(String),
}

/// One `aN<op><value>` filter of a `calls` spec.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Predicate {
    /// The argument's position, zero-based (`a1` is 0).
    pos: usize,
    /// The comparison.
    cmp: Cmp,
    /// The value compared with.
    want: Want,
    /// The filter as written, for the header.
    shown: String,
}

impl Predicate {
    /// Reads one filter, `a3=0x40`, `a2!=?`, `a2>0x10000` or
    /// `a1=Software`.
    ///
    /// # Arguments
    ///
    /// * `token` - The filter as the spec carries it.
    ///
    /// # Returns
    ///
    /// The filter, or `None` when the token is not one (it is part of the
    /// callee's name).
    ///
    /// # Errors
    ///
    /// When it is one but its position is `a0` or `>`/`<` compares with
    /// something other than a number.
    fn parse(token: &str) -> Option<Result<Predicate, String>> {
        let rest = token.strip_prefix('a')?;
        let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
        let (n, tail) = rest.split_at(digits);
        let (cmp, value) = [
            ("!=", Cmp::Ne),
            ("=", Cmp::Eq),
            (">", Cmp::Gt),
            ("<", Cmp::Lt),
        ]
        .into_iter()
        .find_map(|(op, cmp)| tail.strip_prefix(op).map(|v| (cmp, v)))?;
        let n: usize = n.parse().ok()?;
        let Some(pos) = n.checked_sub(1) else {
            return Some(Err(format!(
                "{token}: arguments count from one as the decompiler names them; a1 is the first"
            )));
        };
        let want = if value == "?" {
            Want::Unseen
        } else if let Some(v) = number(value) {
            Want::Number(v)
        } else {
            Want::Text(value.to_lowercase())
        };
        if matches!(cmp, Cmp::Gt | Cmp::Lt) && !matches!(want, Want::Number(_)) {
            return Some(Err(format!(
                "{token}: > and < compare with a number (0x-hex or decimal)"
            )));
        }
        Some(Ok(Predicate {
            pos,
            cmp,
            want,
            shown: token.to_owned(),
        }))
    }

    /// Tells whether a call's arguments pass the filter.
    ///
    /// # Arguments
    ///
    /// * `args` - The call's arguments by position.
    fn keeps(&self, args: &[CallArg]) -> bool {
        let arg = args.get(self.pos);
        let equal = || match &self.want {
            Want::Unseen => arg.is_none_or(|a| a.text == "?"),
            Want::Number(v) => arg.is_some_and(|a| a.value == Some(*v)),
            Want::Text(t) => arg.is_some_and(|a| {
                a.text.to_lowercase().contains(t)
                    || a.string
                        .as_ref()
                        .is_some_and(|s| s.to_lowercase().contains(t))
            }),
        };
        let value = arg.and_then(|a| a.value);
        match (self.cmp, &self.want) {
            (Cmp::Eq, _) => equal(),
            (Cmp::Ne, _) => !equal(),
            (Cmp::Gt, Want::Number(v)) => value.is_some_and(|x| x > *v),
            (Cmp::Lt, Want::Number(v)) => value.is_some_and(|x| x < *v),
            (Cmp::Gt | Cmp::Lt, Want::Unseen | Want::Text(_)) => false,
        }
    }
}

/// Reads a filter's number: `0x`-hex, decimal, or a negative decimal as
/// the word's two's complement.
///
/// # Arguments
///
/// * `s` - The text.
fn number(s: &str) -> Option<u64> {
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        return u64::from_str_radix(hex, 16).ok();
    }
    if let Some(neg) = s.strip_prefix('-') {
        return neg.parse::<u64>().ok().map(u64::wrapping_neg);
    }
    s.bytes()
        .all(|b| b.is_ascii_digit())
        .then(|| s.parse().ok())
        .flatten()
}

/// The declared parameter count of an import, `this` included, as a call
/// on a `bitness`-bit target passes them.
///
/// # Arguments
///
/// * `name` - The bare import name.
/// * `bitness` - 32 or 64.
fn declared_params(name: &str, bitness: u32) -> Option<usize> {
    let proto = crate::analysis::prototypes::msvc_prototype(name)
        .or_else(|| crate::analysis::prototypes::declared(name, bitness))?;
    let params = if bitness == 32 {
        proto.stack_params()
    } else {
        proto.params
    };
    Some(usize::from(params) + usize::from(proto.this))
}

/// A call's arguments as a row lists them: padded with `?` to what the
/// import is declared to take, and with one `?` more where the text passes
/// fewer stack words than its callee reads.
///
/// # Arguments
///
/// * `site` - The recorded call.
/// * `declared` - The callee's declared parameter count, when known.
pub(super) fn listed_args(site: &CallSite, declared: Option<usize>) -> Vec<CallArg> {
    let mut args = site.args.clone();
    let want = declared.unwrap_or(args.len() + usize::from(site.short));
    while args.len() < want {
        args.push(CallArg {
            text: "?".to_owned(),
            value: None,
            string: None,
        });
    }
    args
}

/// Lists every call site of a function or an import with its arguments.
///
/// The spec is `<callee>[,aN<op><value>]...[,offset=<n>][,limit=<n>]`. The callee is a
/// function or an import by name or address; a call is counted whether it
/// is made directly, through a thunk, through the import slot, or through a
/// register loaded from the slot. Each row is a call as the pseudo-C makes
/// it, the arguments in the positions the callee reads them from: a
/// constant in hex, a string literal quoted, a global by name, any other
/// value as the expression the text writes, and `?` where the lifter saw
/// nothing (an import is padded to its declared parameters). Filters keep
/// the calls whose argument `aN` equals a number, contains a text (as
/// written or in the string it points at), is `?`, differs (`!=`), or is a
/// constant above or below a number (`>`, `<`). Rows are in address order,
/// [`CALLS_PAGE`] a page at most, `limit=` a smaller one; at most
/// [`CALLERS_MAX`] callers are decompiled.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - The spec as the URI carries it.
///
/// # Returns
///
/// The header, then a row per call of the page.
///
/// # Errors
///
/// When the program does not decompile, the spec names no callee, a
/// filter, the offset or the limit does not read, or the callee is not an
/// entry.
pub fn calls_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    if let Some(why) = p.refuses(Feature::Decompile) {
        return Err(why);
    }
    let mut name_parts: Vec<&str> = Vec::new();
    let mut filters: Vec<Predicate> = Vec::new();
    let mut offset = 0usize;
    let mut limit: Option<usize> = None;
    for token in spec.split(',').map(str::trim) {
        if let Some(n) = token.strip_prefix("offset=") {
            offset = n
                .parse()
                .map_err(|_| format!("bad offset {n:?}: a row count"))?;
        } else if let Some(n) = token.strip_prefix("limit=") {
            limit = Some(crate::table::row_limit(n)?);
        } else if let Some(filter) = Predicate::parse(token) {
            filters.push(filter?);
        } else {
            name_parts.push(token);
        }
    }
    let name = name_parts.join(",");
    if name.is_empty() {
        return Err(
            "calls needs a function or an import: borer://calls/<name>[,aN=<value>]...".to_owned(),
        );
    }
    let va = crate::analysis::resolve_suggesting(p, a, o, &name)?;
    let reach = reach_of(p, a, o, va)?;
    let gathered = gather(p, a, o, &reach, CALLERS_MAX);
    let declared = reach
        .import
        .as_deref()
        .zip(p.arch.bitness())
        .and_then(|(n, bits)| declared_params(n, bits));
    let rows: Vec<(&Found, Vec<CallArg>)> = gathered
        .found
        .iter()
        .map(|f| {
            let args = f
                .site
                .as_ref()
                .map_or_else(Vec::new, |s| listed_args(s, declared));
            (f, args)
        })
        .filter(|(f, args)| {
            filters.is_empty() || (f.site.is_some() && filters.iter().all(|w| w.keeps(args)))
        })
        .collect();
    let functions: BTreeSet<u64> = gathered.found.iter().map(|f| f.caller).collect();
    let via: Vec<String> = reach
        .slots
        .iter()
        .map(|s| format!("slot {s:#x}"))
        .chain(
            reach
                .entries
                .iter()
                .filter(|e| **e != va)
                .map(|e| format!("thunk {e:#x}")),
        )
        .collect();
    let mut out = format!(
        "# calls to {}{}: {} site{} in {} function{}\n",
        reach.name,
        if via.is_empty() {
            String::new()
        } else {
            format!(" ({})", via.join(", "))
        },
        gathered.found.len(),
        plural(gathered.found.len()),
        functions.len(),
        plural(functions.len())
    );
    if gathered.read < gathered.callers {
        let _ = writeln!(
            out,
            "# {} functions reach it; the first {} by address were decompiled, the other {} are not read",
            gathered.callers,
            gathered.read,
            gathered.callers - gathered.read
        );
    }
    if !filters.is_empty() {
        let shown: Vec<&str> = filters.iter().map(|w| w.shown.as_str()).collect();
        let _ = writeln!(
            out,
            "# where {}: {} site{}",
            shown.join(", "),
            rows.len(),
            plural(rows.len())
        );
    }
    let total = rows.len();
    let start = offset.min(total);
    let size = limit.map_or(CALLS_PAGE, |n| n.min(CALLS_PAGE));
    let page = &rows[start..total.min(start.saturating_add(size))];
    let _ = writeln!(out, "# {} from {offset}", showing(page.len(), total));
    if page.is_empty() {
        return Ok(out);
    }
    out.push_str("# site          caller                        call\n");
    for (f, args) in page {
        let caller = short_name(a, o, f.caller);
        let call = match &f.site {
            Some(site) => {
                let texts: Vec<&str> = args.iter().map(|a| a.text.as_str()).collect();
                format!(
                    "{}{}({})",
                    if site.tail { "return " } else { "" },
                    reach.name,
                    texts.join(", ")
                )
            }
            None => {
                "(not in the decompiled text: the function does not decompile or the block is cut)"
                    .to_owned()
            }
        };
        let _ = writeln!(out, "{:<#15x} {caller:<29} {call}", f.at);
    }
    let next = start + page.len();
    if next < total {
        let mut again: Vec<String> = vec![name];
        again.extend(filters.iter().map(|w| w.shown.clone()));
        again.push(format!("offset={next}"));
        again.extend(limit.map(|n| format!("limit={n}")));
        let _ = writeln!(
            out,
            "# {} more; borer://calls/{} for the next page",
            total - next,
            again.join(",")
        );
    }
    Ok(out)
}
