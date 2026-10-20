//! The x64 exception tables' handler data: the funclets a function's
//! handler runs on its frame.
//!
//! A 64-bit function that has destructors to run, a `catch` to enter or a
//! `__try` to guard registers a handler in its unwind information, and the
//! data after the handler's address says what it guards. `__CxxFrameHandler3`
//! reads a `FuncInfo` - the record the 32-bit runtime reads, with
//! image-relative addresses - whose unwind map names the cleanup funclets
//! and whose try-block map names the catch funclets. `__C_specific_handler`
//! reads a scope table, one record per `__try`, naming the filter or
//! `__finally` funclet and the `__except` body. Every one of those is code
//! the runtime enters with the parent's frame, that nothing calls and no
//! instruction names: a function of its own to a walk, and a piece of its
//! parent to a reader. A Rust binary carries three of them for every
//! function that has something to drop.
//!
//! `__CxxFrameHandler4`, the runtime since Visual Studio 2019, reads the
//! same maps written compactly: a header byte says which are present,
//! counts and states are variable-length integers, and only the addresses
//! keep their four bytes.
//!
//! The handler is named when the program names it - an import thunk, an
//! export - and told by the shape of its data when it does not: a runtime
//! linked in statically has no name, and the same records.

use crate::isa::x86::{FlowControl, OpKind, Register};

use crate::analysis::guards::{Clause, ClauseKind, Dialect, Guard};
use crate::analysis::{FuncletRole, read_u32};
use crate::fxmap::FxHashMap;
use crate::headers::ExceptionHandler;
use crate::num::from_usize;
use crate::program::{Program, SymbolKind};

/// Most `__try` scopes read from one table.
const SCOPES_MAX: u32 = 4096;
/// Most unwind states read from one `FuncInfo`.
const STATES_MAX: u32 = 4096;
/// Most try blocks read from one `FuncInfo`.
const TRY_BLOCKS_MAX: u32 = 1024;
/// Most catch clauses read from one try block.
const CATCHES_MAX: u32 = 64;
/// Most IP-to-state entries read from one `FuncInfo`.
const IP_MAP_MAX: u32 = 1 << 16;
/// The `FuncInfo` magic numbers `__CxxFrameHandler3` accepts.
const MAGIC: std::ops::RangeInclusive<u32> = 0x1993_0520..=0x1993_0522;

/// A funclet the tables name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Funclet {
    /// Entry of the function whose frame it runs on.
    pub parent: u64,
    /// Where it begins.
    pub entry: u64,
    /// What the runtime runs it for.
    pub role: FuncletRole,
}

/// What a handler's data is, once told.
enum Kind {
    /// A `FuncInfo` at this address.
    Cxx3(u64),
    /// A compact `FuncInfo4` at this address.
    Cxx4(u64),
    /// A scope table at the data itself.
    Seh,
    /// Something without funclets: a security-cookie check, a format this
    /// does not read.
    Other,
}

/// Lists every funclet the x64 exception tables name.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// One entry per funclet, in address order; a funclet two tables name
/// keeps the first parent.
#[must_use]
pub fn funclets(program: &Program) -> Vec<Funclet> {
    if !program.is_64 {
        return Vec::new();
    }
    let names = HandlerNames::of(program);
    let mut out = Vec::new();
    for h in &program.headers.exception_handlers {
        match kind(program, &names, h) {
            Kind::Cxx3(info) => cxx3(program, h.function, info, &mut out),
            Kind::Cxx4(info) => {
                if let Some(found) = cxx4(program, h.function, info) {
                    out.extend(found.funclets);
                }
            }
            Kind::Seh => {
                if let Some(found) = seh(program, h.function, h.data) {
                    out.extend(found.into_iter().filter(|f| !resumes_parent(program, f)));
                }
            }
            Kind::Other => {}
        }
    }
    out.sort_unstable_by_key(|f| (f.entry, f.parent));
    out.dedup_by_key(|f| f.entry);
    out
}

/// Lists where the functions the x64 exception tables name resume after
/// a handler: code of the parent that none of the parent's instructions
/// reaches, since only the runtime jumps there.
///
/// `__CxxFrameHandler4` keeps each catch's continuation in the record, the
/// address the runtime jumps to once the catch funclet returns; the older
/// runtime has the funclet return it instead, so its records name none. A
/// scope table's `__except` body is one too when it lies inside the range
/// the table declares for its parent; one moved away is a funclet.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// `(parent entry, continuation)` pairs, sorted, each once.
#[must_use]
pub fn continuations(program: &Program) -> Vec<(u64, u64)> {
    if !program.is_64 {
        return Vec::new();
    }
    let names = HandlerNames::of(program);
    let mut out = Vec::new();
    for h in &program.headers.exception_handlers {
        match kind(program, &names, h) {
            Kind::Cxx4(info) => {
                if let Some(found) = cxx4(program, h.function, info) {
                    out.extend(found.continuations.into_iter().map(|c| (h.function, c)));
                }
            }
            Kind::Seh => {
                if let Some(found) = seh(program, h.function, h.data) {
                    out.extend(
                        found
                            .iter()
                            .filter(|f| resumes_parent(program, f))
                            .map(|f| (f.parent, f.entry)),
                    );
                }
            }
            Kind::Cxx3(_) | Kind::Other => {}
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// Reads the guarded regions every x64 function's handler data declares.
///
/// A `FuncInfo` (either encoding) gives each try block a range of states
/// and the IP-to-state map gives each state its instruction ranges; a
/// scope table gives each `__try` its range directly. Records of one
/// table that share a handler and a target are one `__try` laid out in
/// pieces.
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// The guards of each function whose table holds any, by entry.
#[must_use]
pub(crate) fn guards(program: &Program) -> std::collections::BTreeMap<u64, Vec<Guard>> {
    let mut out = std::collections::BTreeMap::new();
    if !program.is_64 {
        return out;
    }
    let names = HandlerNames::of(program);
    for h in &program.headers.exception_handlers {
        let found = match kind(program, &names, h) {
            Kind::Cxx3(info) => cxx3_guards(program, h.function, info),
            Kind::Cxx4(info) => cxx4_guards(program, h.function, info),
            Kind::Seh => seh_guards(program, h.function, h.data),
            Kind::Other => None,
        };
        if let Some(found) = found.filter(|g| !g.is_empty()) {
            out.entry(h.function).or_insert(found);
        }
    }
    out
}

/// Returns where the function the exception table declares at `parent`
/// ends.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `parent` - The function's entry.
///
/// # Returns
///
/// The end, or `None` when the table declares no function there.
fn parent_end(program: &Program, parent: u64) -> Option<u64> {
    let ranges = &program.function_ranges;
    let k = ranges.partition_point(|r| r.0 < parent);
    ranges.get(k).filter(|r| r.0 == parent).map(|r| r.1)
}

/// Turns an IP-to-state map into the instruction ranges of each state.
///
/// Each entry holds from its address to the next entry's, and the last to
/// the parent's end; ranges outside the parent's own extent (a funclet's
/// entries, kept in the same map) are dropped.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `parent` - The function's entry.
/// * `map` - `(address, state)` entries in any order.
///
/// # Returns
///
/// `(start, end, state)` for each non-empty range.
fn state_spans(program: &Program, parent: u64, mut map: Vec<(u64, i64)>) -> Vec<(u64, u64, i64)> {
    map.sort_unstable();
    let end = parent_end(program, parent).unwrap_or(u64::MAX);
    let mut out = Vec::new();
    for (k, &(ip, state)) in map.iter().enumerate() {
        let next = map.get(k + 1).map_or(end, |n| n.0).min(end);
        if ip >= parent && ip < next {
            out.push((ip, next, state));
        }
    }
    out
}

/// Builds a guard from the states a try block spans.
///
/// # Arguments
///
/// * `spans` - The ranges of each state ([`state_spans`]).
/// * `low` - The try block's lowest state.
/// * `high` - Its highest.
/// * `clauses` - Its catch clauses.
///
/// # Returns
///
/// The guard, or `None` when no instruction is in its states or it has no
/// clause.
fn try_block(
    spans: &[(u64, u64, i64)],
    low: i64,
    high: i64,
    clauses: Vec<Clause>,
) -> Option<Guard> {
    let ranges: Vec<(u64, u64)> = spans
        .iter()
        .filter(|s| (low..=high).contains(&s.2))
        .map(|s| (s.0, s.1))
        .collect();
    (!ranges.is_empty() && !clauses.is_empty()).then(|| Guard {
        dialect: Dialect::Cxx,
        ranges: crate::analysis::guards::merged(ranges),
        clauses,
    })
}

/// Spells the declaration a catch handler names.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `adjectives` - The handler's `HT_*` flags.
/// * `descriptor` - The caught type's descriptor, `None` for `catch (...)`.
///
/// # Returns
///
/// The declaration as C++ writes it (`const Error &`), or `...`.
pub(crate) fn catch_decl(program: &Program, adjectives: u32, descriptor: Option<u64>) -> String {
    /// `HT_IsConst`.
    const CONST: u32 = 0x01;
    /// `HT_IsReference`.
    const REFERENCE: u32 = 0x08;
    /// `HT_IsStdDotDot`.
    const DOT_DOT: u32 = 0x40;
    let Some(ty) = descriptor
        .filter(|_| adjectives & DOT_DOT == 0)
        .and_then(|d| crate::analysis::rtti::caught_type(program, d))
    else {
        return "...".to_owned();
    };
    let constant = if adjectives & CONST != 0 {
        "const "
    } else {
        ""
    };
    let reference = if adjectives & REFERENCE != 0 {
        " &"
    } else {
        ""
    };
    format!("{constant}{ty}{reference}")
}

/// Reads the try blocks a `FuncInfo` declares.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `parent` - The function the record belongs to.
/// * `info` - The `FuncInfo` address.
///
/// # Returns
///
/// The guards, or `None` when the maps do not hold together.
fn cxx3_guards(program: &Program, parent: u64, info: u64) -> Option<Vec<Guard>> {
    let base = program.image_base;
    let rva = |at: u64| {
        read_u32(program, at)
            .filter(|&v| v != 0)
            .map(|v| base.wrapping_add(u64::from(v)))
    };
    let blocks = read_u32(program, info.wrapping_add(12))?;
    let n_ip = read_u32(program, info.wrapping_add(20))?;
    if blocks == 0 || blocks > TRY_BLOCKS_MAX || n_ip > IP_MAP_MAX {
        return None;
    }
    let tmap = rva(info.wrapping_add(16))?;
    let ipmap = rva(info.wrapping_add(24))?;
    let mut map = Vec::new();
    for k in 0..u64::from(n_ip) {
        let at = ipmap.wrapping_add(k * 8);
        let ip = base.wrapping_add(u64::from(read_u32(program, at)?));
        let state = read_u32(program, at.wrapping_add(4))?.cast_signed();
        map.push((ip, i64::from(state)));
    }
    let spans = state_spans(program, parent, map);
    let mut out = Vec::new();
    for block in 0..u64::from(blocks) {
        let entry = tmap.wrapping_add(block * 20);
        let low = read_u32(program, entry)?.cast_signed();
        let high = read_u32(program, entry.wrapping_add(4))?.cast_signed();
        let catches = read_u32(program, entry.wrapping_add(12))?.min(CATCHES_MAX);
        let handlers = rva(entry.wrapping_add(16))?;
        let mut clauses = Vec::new();
        for clause in 0..u64::from(catches) {
            let h = handlers.wrapping_add(clause * 20);
            let adjectives = read_u32(program, h)?;
            let funclet = rva(h.wrapping_add(12))?;
            if !crate::analysis::is_executable_va(program, funclet) {
                return None;
            }
            clauses.push(Clause {
                kind: ClauseKind::Catch(catch_decl(program, adjectives, rva(h.wrapping_add(4)))),
                funclet: Some(funclet),
                resume: None,
                selector: None,
            });
        }
        out.extend(try_block(&spans, i64::from(low), i64::from(high), clauses));
    }
    Some(out)
}

/// Reads the try blocks a compact `FuncInfo4` declares.
///
/// The header byte says which maps follow; the IP-to-state map is always
/// there, a count then pairs of compact integers: the distance from the
/// previous entry's address (the first from the function's start) and the
/// state plus one. A separated function, whose map is split by code
/// segment, is not read.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `parent` - The function the record belongs to.
/// * `info` - The `FuncInfo4` address.
///
/// # Returns
///
/// The guards, or `None` when the record does not hold together.
fn cxx4_guards(program: &Program, parent: u64, info: u64) -> Option<Vec<Guard>> {
    /// `isSeparated`: the IP-to-state map is split by code segment.
    const SEPARATED: u8 = 0x02;
    let base = program.image_base;
    let header = *program.read_va(info, 1)?.first()?;
    if header & SEPARATED != 0 || header & 0x10 == 0 {
        return None;
    }
    let mut at = info.wrapping_add(1);
    if header & 0x04 != 0 {
        at = at.wrapping_add(4);
    }
    if header & 0x08 != 0 {
        at = at.wrapping_add(4);
    }
    let try_map = base.wrapping_add(u64::from(read_u32(program, at)?));
    let ipmap = base.wrapping_add(u64::from(read_u32(program, at.wrapping_add(4))?));
    let (n_ip, mut q) = compact(program, ipmap)?;
    if n_ip > IP_MAP_MAX {
        return None;
    }
    let mut map = Vec::new();
    let mut ip = parent;
    for _ in 0..n_ip {
        let (delta, next) = compact(program, q)?;
        let (state, next) = compact(program, next)?;
        q = next;
        ip = ip.wrapping_add(u64::from(delta));
        map.push((ip, i64::from(state) - 1));
    }
    let spans = state_spans(program, parent, map);
    let (count, mut q) = compact(program, try_map)?;
    if count > TRY_BLOCKS_MAX {
        return None;
    }
    let mut out = Vec::new();
    for _ in 0..count {
        let (low, next) = compact(program, q)?;
        let (high, next) = compact(program, next)?;
        q = compact(program, next)?.1;
        let handlers = base.wrapping_add(u64::from(read_u32(program, q)?));
        q = q.wrapping_add(4);
        let (catches, mut h) = compact(program, handlers)?;
        if catches > CATCHES_MAX {
            return None;
        }
        let mut clauses = Vec::new();
        for _ in 0..catches {
            let flags = *program.read_va(h, 1)?.first()?;
            h = h.wrapping_add(1);
            let mut adjectives = 0;
            if flags & 0x01 != 0 {
                let (v, next) = compact(program, h)?;
                adjectives = v;
                h = next;
            }
            let mut descriptor = None;
            if flags & 0x02 != 0 {
                descriptor = Some(read_u32(program, h)?)
                    .filter(|&v| v != 0)
                    .map(|v| base.wrapping_add(u64::from(v)));
                h = h.wrapping_add(4);
            }
            if flags & 0x04 != 0 {
                h = compact(program, h)?.1;
            }
            let funclet = base.wrapping_add(u64::from(read_u32(program, h)?));
            h = h.wrapping_add(4);
            let mut resume = None;
            for _ in 0..((flags >> 4) & 3) {
                let cont = if flags & 0x08 != 0 {
                    let rva = read_u32(program, h)?;
                    h = h.wrapping_add(4);
                    base.wrapping_add(u64::from(rva))
                } else {
                    let (offset, next) = compact(program, h)?;
                    h = next;
                    parent.wrapping_add(u64::from(offset))
                };
                resume = resume.or(Some(cont));
            }
            if !crate::analysis::is_executable_va(program, funclet) {
                return None;
            }
            clauses.push(Clause {
                kind: ClauseKind::Catch(catch_decl(program, adjectives, descriptor)),
                funclet: Some(funclet),
                resume,
                selector: None,
            });
        }
        out.extend(try_block(&spans, i64::from(low), i64::from(high), clauses));
    }
    Some(out)
}

/// Reads the `__try` regions a scope table declares.
///
/// Records that share a handler and a target are one `__try` laid out in
/// pieces and become one guard. An `__except` body inside the parent is
/// where the parent resumes; one moved out of it is a funclet.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `parent` - The function the table belongs to.
/// * `data` - The table's address.
///
/// # Returns
///
/// The guards in table order, or `None` when the table does not hold
/// together ([`seh`]).
fn seh_guards(program: &Program, parent: u64, data: u64) -> Option<Vec<Guard>> {
    seh(program, parent, data)?;
    let count = read_u32(program, data)?;
    let base = program.image_base;
    let end = parent_end(program, parent);
    let mut out: Vec<(u32, u32, Guard)> = Vec::new();
    for i in 0..u64::from(count) {
        let rec = data.wrapping_add(4 + i * 16);
        let begin = base.wrapping_add(u64::from(read_u32(program, rec)?));
        let stop = base.wrapping_add(u64::from(read_u32(program, rec.wrapping_add(4))?));
        let handler = read_u32(program, rec.wrapping_add(8))?;
        let target = read_u32(program, rec.wrapping_add(12))?;
        if let Some((.., g)) = out
            .iter_mut()
            .find(|(h, t, _)| *h == handler && *t == target)
        {
            g.ranges.push((begin, stop));
            continue;
        }
        let at = |rva: u32| base.wrapping_add(u64::from(rva));
        let clause = if target == 0 {
            Clause {
                kind: ClauseKind::Finally,
                funclet: Some(at(handler)),
                resume: None,
                selector: None,
            }
        } else {
            let body = at(target);
            let inside = body > parent && end.is_some_and(|e| body < e);
            Clause {
                kind: ClauseKind::Except((handler > 1).then(|| at(handler))),
                funclet: (!inside).then_some(body),
                resume: Some(body),
                selector: None,
            }
        };
        out.push((
            handler,
            target,
            Guard {
                dialect: Dialect::Seh,
                ranges: vec![(begin, stop)],
                clauses: vec![clause],
            },
        ));
    }
    Some(
        out.into_iter()
            .map(|(.., mut g)| {
                g.ranges = crate::analysis::guards::merged(g.ranges);
                g
            })
            .collect(),
    )
}

/// Whether a funclet is an `__except` body inside the range the exception
/// table declares for its parent: a label of the parent, not a funclet.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `f` - The funclet.
fn resumes_parent(program: &Program, f: &Funclet) -> bool {
    if !matches!(f.role, FuncletRole::Except(_)) {
        return false;
    }
    let ranges = &program.function_ranges;
    let k = ranges.partition_point(|r| r.0 < f.parent);
    ranges
        .get(k)
        .is_some_and(|&(start, end)| start == f.parent && f.entry > start && f.entry < end)
}

/// What a `FuncInfo4` names.
struct Cxx4 {
    /// The funclets its maps name.
    funclets: Vec<Funclet>,
    /// Where the parent resumes after each catch, in the code.
    continuations: Vec<u64>,
}

/// The handler names one walk of the exception tables looks up, by address.
///
/// PERF: every handler is named by a symbol lookup, and a linear scan per
/// handler over every symbol was most of the walk on a PDB-carrying binary;
/// one pass over the symbols makes each lookup a hash probe. `or_insert`
/// keeps the first symbol of an address in file order, exactly what `find`
/// returned.
struct HandlerNames {
    /// Address to the first non-import symbol there.
    named: FxHashMap<u64, usize>,
    /// IAT/GOT slot to the first import there.
    imports: FxHashMap<u64, usize>,
}

impl HandlerNames {
    /// Indexes the program's symbols by address.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    ///
    /// # Returns
    ///
    /// The lookup tables for one walk.
    fn of(program: &Program) -> Self {
        let mut named: FxHashMap<u64, usize> = FxHashMap::default();
        let mut imports: FxHashMap<u64, usize> = FxHashMap::default();
        for (i, s) in program.symbols.iter().enumerate() {
            if s.kind == SymbolKind::Import {
                imports.entry(s.addr).or_insert(i);
            } else {
                named.entry(s.addr).or_insert(i);
            }
        }
        Self { named, imports }
    }

    /// Reads the name of the handler at `va`, lowercased.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    /// * `va` - The handler's address.
    ///
    /// # Returns
    ///
    /// The symbol name there, or the import's a thunk jumps to, or `None`.
    fn name(&self, program: &Program, va: u64) -> Option<String> {
        if let Some(&i) = self.named.get(&va) {
            return Some(program.symbols[i].name.to_lowercase());
        }
        let jump = crate::analysis::functions::decode_at(program, 64, va)?;
        if jump.flow_control() != FlowControl::IndirectBranch
            || jump.op0_kind() != OpKind::Memory
            || jump.memory_index() != Register::None
        {
            return None;
        }
        let slot = if jump.is_ip_rel_memory_operand() {
            jump.ip_rel_memory_address()
        } else if jump.memory_base() == Register::None {
            jump.memory_displacement64()
        } else {
            return None;
        };
        self.imports
            .get(&slot)
            .map(|&i| program.symbols[i].name.to_lowercase())
    }
}

/// Tells what a handler's data is.
///
/// The handler's name decides when the program has one; otherwise the data
/// is read as a `FuncInfo` address and then as a scope table, and believed
/// only when it holds together as one.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `names` - The handler-name lookups for this walk.
/// * `h` - The handler record.
fn kind(program: &Program, names: &HandlerNames, h: &ExceptionHandler) -> Kind {
    let name = names.name(program, h.handler).unwrap_or_default();
    let info = read_u32(program, h.data).map(|rva| program.image_base.wrapping_add(u64::from(rva)));
    let cxx3 =
        info.filter(|&i| read_u32(program, i).is_some_and(|m| MAGIC.contains(&(m & 0x1fff_ffff))));
    if name.contains("cxxframehandler3")
        || (name.contains("gshandlercheck_eh") && !name.contains("eh4"))
    {
        return cxx3.map_or(Kind::Other, Kind::Cxx3);
    }
    if name.contains("c_specific_handler") || name.contains("gshandlercheck_seh") {
        return Kind::Seh;
    }
    if name.contains("cxxframehandler4") || name.contains("eh4") {
        return info.map_or(Kind::Other, Kind::Cxx4);
    }
    if !name.is_empty() {
        return Kind::Other;
    }
    match cxx3 {
        Some(i) => Kind::Cxx3(i),
        None if seh(program, h.function, h.data).is_some() => Kind::Seh,
        None => match info {
            Some(i) if cxx4(program, h.function, i).is_some_and(|f| !f.funclets.is_empty()) => {
                Kind::Cxx4(i)
            }
            _ => Kind::Other,
        },
    }
}

/// Reads a compact integer, the encoding `FuncInfo4` uses for its counts,
/// states and offsets.
///
/// The low bits of the first byte give the length: `xxx0` one byte,
/// `xx01` two, `x011` three, `0111` four, `1111` a full word after the
/// marker; the value is the little-endian bytes shifted past the marker.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `at` - Where the integer begins.
///
/// # Returns
///
/// The value and the address after it, or `None` off the end of the image.
fn compact(program: &Program, at: u64) -> Option<(u32, u64)> {
    let first = *program.read_va(at, 1)?.first()?;
    let (len, shift) = match first & 0x0f {
        n if n & 1 == 0 => (1, 1),
        n if n & 3 == 1 => (2, 2),
        n if n & 7 == 3 => (3, 3),
        7 => (4, 4),
        _ => (5, 0),
    };
    if len == 5 {
        return Some((read_u32(program, at.wrapping_add(1))?, at.wrapping_add(5)));
    }
    let bytes = program.read_va(at, len)?;
    let mut v: u32 = 0;
    for (i, b) in bytes.iter().enumerate() {
        v |= u32::from(*b) << (8 * i);
    }
    Some((v >> shift, at.wrapping_add(from_usize(len))))
}

/// Reads the funclets a `FuncInfo4` names.
///
/// The header byte says which maps are present; the unwind map is a count
/// then entries of a type-and-offset word followed by the action's address
/// when the type has one, the try-block map a count then entries whose
/// handler array holds each catch's flags, optional fields, handler
/// address and continuations.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `parent` - The function the record belongs to.
/// * `info` - The `FuncInfo4` address.
///
/// # Returns
///
/// The funclets and continuations, or `None` when the record does not hold
/// together: a funclet outside the code, a count beyond reason, bytes off
/// the image.
fn cxx4(program: &Program, parent: u64, info: u64) -> Option<Cxx4> {
    let base = program.image_base;
    let code =
        |rva: u32| crate::analysis::is_executable_va(program, base.wrapping_add(u64::from(rva)));
    let header = *program.read_va(info, 1)?.first()?;
    let mut at = info.wrapping_add(1);
    if header & 0x04 != 0 {
        at = at.wrapping_add(4);
    }
    let unwind_map = if header & 0x08 != 0 {
        let rva = read_u32(program, at)?;
        at = at.wrapping_add(4);
        Some(base.wrapping_add(u64::from(rva)))
    } else {
        None
    };
    let try_map = if header & 0x10 != 0 {
        let rva = read_u32(program, at)?;
        Some(base.wrapping_add(u64::from(rva)))
    } else {
        None
    };
    let mut out = Vec::new();
    let mut continuations = Vec::new();
    if let Some(map) = unwind_map {
        let (count, mut q) = compact(program, map)?;
        if count > STATES_MAX {
            return None;
        }
        for state in 0..count {
            let (word, next) = compact(program, q)?;
            q = next;
            if word & 3 != 0 {
                let action = read_u32(program, q)?;
                q = q.wrapping_add(4);
                if action == 0 || !code(action) {
                    return None;
                }
                if matches!(word & 3, 1 | 2) {
                    q = compact(program, q)?.1;
                    continue;
                }
                out.push(Funclet {
                    parent,
                    entry: base.wrapping_add(u64::from(action)),
                    role: FuncletRole::Unwind(state),
                });
            }
        }
    }
    if let Some(map) = try_map {
        let (count, mut q) = compact(program, map)?;
        if count > TRY_BLOCKS_MAX {
            return None;
        }
        for block in 0..count {
            for _ in 0..3 {
                q = compact(program, q)?.1;
            }
            let handlers = base.wrapping_add(u64::from(read_u32(program, q)?));
            q = q.wrapping_add(4);
            let (catches, mut h) = compact(program, handlers)?;
            if catches > CATCHES_MAX {
                return None;
            }
            for clause in 0..catches {
                let flags = *program.read_va(h, 1)?.first()?;
                h = h.wrapping_add(1);
                if flags & 0x01 != 0 {
                    h = compact(program, h)?.1;
                }
                if flags & 0x02 != 0 {
                    h = h.wrapping_add(4);
                }
                if flags & 0x04 != 0 {
                    h = compact(program, h)?.1;
                }
                let handler = read_u32(program, h)?;
                h = h.wrapping_add(4);
                for _ in 0..((flags >> 4) & 3) {
                    let at = if flags & 0x08 != 0 {
                        let rva = read_u32(program, h)?;
                        h = h.wrapping_add(4);
                        base.wrapping_add(u64::from(rva))
                    } else {
                        let (offset, next) = compact(program, h)?;
                        h = next;
                        parent.wrapping_add(u64::from(offset))
                    };
                    if crate::analysis::is_executable_va(program, at) {
                        continuations.push(at);
                    }
                }
                if handler == 0 || !code(handler) {
                    return None;
                }
                out.push(Funclet {
                    parent,
                    entry: base.wrapping_add(u64::from(handler)),
                    role: FuncletRole::Catch(block, clause),
                });
            }
        }
    }
    Some(Cxx4 {
        funclets: out,
        continuations,
    })
}

/// Reads the funclets a `FuncInfo` names into `out`.
///
/// The unwind map holds one action per state, the try-block map one
/// handler array per `try`; on x64 a handler entry is twenty bytes and every
/// address is image-relative.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `parent` - The function the record belongs to.
/// * `info` - The `FuncInfo` address.
/// * `out` - Where the funclets go.
fn cxx3(program: &Program, parent: u64, info: u64, out: &mut Vec<Funclet>) {
    let base = program.image_base;
    let rva = |at: u64| {
        read_u32(program, at)
            .filter(|&v| v != 0)
            .map(|v| base.wrapping_add(u64::from(v)))
    };
    let code = |va: u64| crate::analysis::is_executable_va(program, va);
    if let (Some(states), Some(map)) = (
        read_u32(program, info.wrapping_add(4)),
        rva(info.wrapping_add(8)),
    ) {
        for state in 0..states.min(STATES_MAX) {
            let at = map.wrapping_add(u64::from(state) * 8 + 4);
            if let Some(action) = rva(at)
                && code(action)
            {
                out.push(Funclet {
                    parent,
                    entry: action,
                    role: FuncletRole::Unwind(state),
                });
            }
        }
    }
    if let (Some(blocks), Some(tmap)) = (
        read_u32(program, info.wrapping_add(12)),
        rva(info.wrapping_add(16)),
    ) {
        for block in 0..blocks.min(TRY_BLOCKS_MAX) {
            let entry = tmap.wrapping_add(u64::from(block) * 20);
            let (Some(catches), Some(handlers)) = (
                read_u32(program, entry.wrapping_add(12)),
                rva(entry.wrapping_add(16)),
            ) else {
                continue;
            };
            for clause in 0..catches.min(CATCHES_MAX) {
                let at = handlers.wrapping_add(u64::from(clause) * 20 + 12);
                if let Some(handler) = rva(at)
                    && code(handler)
                {
                    out.push(Funclet {
                        parent,
                        entry: handler,
                        role: FuncletRole::Catch(block, clause),
                    });
                }
            }
        }
    }
}

/// Reads a scope table's funclets.
///
/// Each record guards `begin..end` of the parent with a handler and a jump
/// target. A `__finally` names its funclet as the handler and no target;
/// an `__except` names its filter funclet as the handler - or `1` for
/// `EXCEPTION_EXECUTE_HANDLER`, no filter - and its body as the target,
/// which is a label inside the parent nothing else reaches.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `parent` - The function the table belongs to.
/// * `data` - The table's address.
///
/// # Returns
///
/// The funclets, or `None` when the bytes do not hold together as a scope
/// table: a count of zero or beyond reason, a range outside the code, a
/// handler that is neither a funclet nor the constant.
fn seh(program: &Program, parent: u64, data: u64) -> Option<Vec<Funclet>> {
    let count = read_u32(program, data)?;
    if count == 0 || count > SCOPES_MAX {
        return None;
    }
    let base = program.image_base;
    let code =
        |rva: u32| crate::analysis::is_executable_va(program, base.wrapping_add(u64::from(rva)));
    let mut out = Vec::new();
    for i in 0..count {
        let rec = data.wrapping_add(4 + u64::from(i) * 16);
        let begin = read_u32(program, rec)?;
        let end = read_u32(program, rec.wrapping_add(4))?;
        let handler = read_u32(program, rec.wrapping_add(8))?;
        let target = read_u32(program, rec.wrapping_add(12))?;
        if begin >= end || !code(begin) || !code(end - 1) || handler == 0 {
            return None;
        }
        if handler > 1 {
            if !code(handler) {
                return None;
            }
            out.push(Funclet {
                parent,
                entry: base.wrapping_add(u64::from(handler)),
                role: if target == 0 {
                    FuncletRole::Finally(i)
                } else {
                    FuncletRole::Filter(i)
                },
            });
        }
        if target != 0 {
            if !code(target) {
                return None;
            }
            out.push(Funclet {
                parent,
                entry: base.wrapping_add(u64::from(target)),
                role: FuncletRole::Except(i),
            });
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::{Funclet, continuations, funclets, guards};
    use crate::analysis::FuncletRole;
    use crate::analysis::guards::{Clause, ClauseKind, Dialect, Guard};
    use crate::headers::{ExceptionHandler, Headers};
    use crate::program::{Arch, BinaryFormat, FileOff, Program, Section, Symbol, SymbolKind, Va};

    /// Image base of the fixtures.
    const BASE: u64 = 0x1_4000_0000;

    /// Builds an x64 image: `.text` of code at `BASE + 0x1000`, `.rdata`
    /// holding `data` at `BASE + 0x2000`, and one handler registered for the
    /// function at `BASE + 0x1000` with its data at `BASE + 0x2000`.
    ///
    /// # Panics
    ///
    /// Never: the thunk's offset is a constant that fits a `u32`.
    fn image(data: &[u8], handler_name: Option<&str>) -> Program {
        let mut bytes = vec![0u8; 0x3000];
        for at in [0x1000usize, 0x1100, 0x1200, 0x1300] {
            bytes[at] = 0xc3; // ASM: ret
        }
        let thunk = 0x1400usize;
        bytes[thunk..thunk + 6].copy_from_slice(&[0xff, 0x25, 0x00, 0x00, 0x00, 0x00]);
        let rel = (0x2800u32)
            .wrapping_sub(u32::try_from(thunk + 6).expect("the thunk sits inside the image"));
        bytes[thunk + 2..thunk + 6].copy_from_slice(&rel.to_le_bytes());
        bytes[0x2000..0x2000 + data.len()].copy_from_slice(data);
        let section = |name: &str, off: u64, executable: bool| Section {
            name: name.to_owned(),
            va: Va(BASE + off),
            vsize: 0x1000,
            file_off: FileOff(off),
            file_size: 0x1000,
            readable: true,
            writable: false,
            executable,
        };
        let mut symbols = Vec::new();
        if let Some(name) = handler_name {
            symbols.push(Symbol {
                name: format!("vcruntime140.dll!{name}"),
                addr: BASE + 0x2800,
                kind: SymbolKind::Import,
            });
        }
        let headers = Headers {
            exception_handlers: vec![ExceptionHandler {
                function: BASE + 0x1000,
                handler: BASE + 0x1400,
                data: BASE + 0x2000,
            }],
            ..Headers::default()
        };
        let sections = vec![
            section(".text", 0x1000, true),
            section(".rdata", 0x2000, false),
        ];
        let section_index = Program::index_sections(&sections);
        Program {
            path: PathBuf::new(),
            bytes,
            format: BinaryFormat::Pe,
            arch: Arch::X86_64,
            is_64: true,
            entry: Some(BASE + 0x1000),
            image_base: BASE,
            sections,
            section_index,
            symbols,
            function_ranges: Vec::new(),
            headers,
            debug_functions: Vec::new(),
            debug_types: std::collections::BTreeMap::new(),
            debug_typedefs: std::collections::BTreeMap::new(),
            pdb: None,
            pdb_record: None,
            pdb_source: None,
            flat_fallback: false,
            relocs: crate::reloc::Relocs::default(),
            go: None,
            clr: None,
            parent: None,
        }
    }

    /// A scope table with a `__finally` and an `__except` with a filter.
    fn scope_table() -> Vec<u8> {
        let mut d = Vec::new();
        d.extend_from_slice(&2u32.to_le_bytes());
        for v in [0x1000u32, 0x1010, 0x1100, 0] {
            d.extend_from_slice(&v.to_le_bytes());
        }
        for v in [0x1010u32, 0x1020, 0x1200, 0x1300] {
            d.extend_from_slice(&v.to_le_bytes());
        }
        d
    }

    /// A scope table names the `__finally`, the filter and the `__except` body.
    ///
    /// # Panics
    ///
    /// When a funclet is missed or misread.
    #[test]
    fn a_scope_table_names_its_funclets() {
        let p = image(&scope_table(), Some("__C_specific_handler"));
        let found = funclets(&p);
        let parent = BASE + 0x1000;
        assert_eq!(
            found,
            vec![
                Funclet {
                    parent,
                    entry: BASE + 0x1100,
                    role: FuncletRole::Finally(0)
                },
                Funclet {
                    parent,
                    entry: BASE + 0x1200,
                    role: FuncletRole::Filter(1)
                },
                Funclet {
                    parent,
                    entry: BASE + 0x1300,
                    role: FuncletRole::Except(1)
                },
            ]
        );
    }

    /// An `__except` body inside its parent's declared range is where the
    /// parent resumes, not a funclet.
    ///
    /// # Panics
    ///
    /// When the body is listed as a funclet or not as a continuation.
    #[test]
    fn a_near_except_body_resumes_its_parent() {
        let mut p = image(&scope_table(), Some("__C_specific_handler"));
        p.function_ranges = vec![(BASE + 0x1000, BASE + 0x1400)];
        let parent = BASE + 0x1000;
        assert!(
            funclets(&p)
                .iter()
                .all(|f| !matches!(f.role, FuncletRole::Except(_)))
        );
        assert_eq!(funclets(&p).len(), 2);
        assert_eq!(continuations(&p), vec![(parent, BASE + 0x1300)]);
    }

    /// The same table is read without a name for its handler.
    ///
    /// A runtime linked in statically leaves the handler unnamed, and the
    /// records are the same.
    ///
    /// # Panics
    ///
    /// When the unnamed table is not read.
    #[test]
    fn an_unnamed_scope_table_is_told_by_its_shape() {
        let p = image(&scope_table(), None);
        assert_eq!(funclets(&p).len(), 3);
    }

    /// A security-cookie handler's data is not a scope table.
    ///
    /// `__GSHandlerCheck` keeps one word, the cookie's frame offset, and the
    /// bytes after it are whatever follows; read as a count and records they
    /// do not hold together, and nothing is invented.
    ///
    /// # Panics
    ///
    /// When a funclet is invented from a cookie offset.
    #[test]
    fn a_cookie_offset_is_not_a_scope_table() {
        let mut d = 0x20u32.to_le_bytes().to_vec();
        d.extend_from_slice(&[0x11; 64]);
        assert!(funclets(&image(&d, None)).is_empty());
        assert!(funclets(&image(&d, Some("__GSHandlerCheck"))).is_empty());
    }

    /// A compact `FuncInfo4` names the same funclets.
    ///
    /// The record is laid out the way `__CxxFrameHandler4` reads it: a
    /// header byte, the maps' addresses, then counts and states as compact
    /// integers with only the addresses at full width.
    ///
    /// # Panics
    ///
    /// When a funclet is missed or misread.
    #[test]
    fn a_compact_funcinfo_names_its_funclets() {
        let mut d = vec![0u8; 0x100];
        let put =
            |d: &mut Vec<u8>, at: usize, v: u32| d[at..at + 4].copy_from_slice(&v.to_le_bytes());
        put(&mut d, 0x0, 0x2010);
        d[0x10] = 0x08 | 0x10;
        put(&mut d, 0x11, 0x2040);
        put(&mut d, 0x15, 0x2060);
        d[0x40] = 2 << 1;
        d[0x41] = 1 << 1;
        put(&mut d, 0x42, 0x1300);
        d[0x46] = 0x20 << 1;
        d[0x47] = 3 << 1;
        put(&mut d, 0x48, 0x1100);
        d[0x60] = 1 << 1;
        d[0x61] = 0;
        d[0x62] = 0;
        d[0x63] = 0;
        put(&mut d, 0x64, 0x2080);
        d[0x80] = 1 << 1;
        d[0x81] = 0x01 | 0x08 | 0x10;
        d[0x82] = 0x40 << 1;
        put(&mut d, 0x83, 0x1200);
        put(&mut d, 0x87, 0x1000);
        let parent = BASE + 0x1000;
        let expect = vec![
            Funclet {
                parent,
                entry: BASE + 0x1100,
                role: FuncletRole::Unwind(1),
            },
            Funclet {
                parent,
                entry: BASE + 0x1200,
                role: FuncletRole::Catch(0, 0),
            },
        ];
        assert_eq!(funclets(&image(&d, Some("__CxxFrameHandler4"))), expect);
        assert_eq!(funclets(&image(&d, None)), expect);
        assert_eq!(
            continuations(&image(&d, None)),
            vec![(parent, BASE + 0x1000)]
        );
    }

    /// A `FuncInfo` names the unwind actions and the catch handlers.
    ///
    /// The record and its maps are laid out in `.rdata` the way the x64
    /// runtime reads them: image-relative addresses, twenty-byte handler
    /// entries.
    ///
    /// # Panics
    ///
    /// When a funclet is missed or misread.
    #[test]
    fn a_funcinfo_names_its_funclets() {
        let mut d = vec![0u8; 0x100];
        let put =
            |d: &mut Vec<u8>, at: usize, v: u32| d[at..at + 4].copy_from_slice(&v.to_le_bytes());
        put(&mut d, 0x0, 0x2010);
        put(&mut d, 0x10, 0x1993_0522);
        put(&mut d, 0x14, 2);
        put(&mut d, 0x18, 0x2040);
        put(&mut d, 0x1c, 1);
        put(&mut d, 0x20, 0x2060);
        put(&mut d, 0x40, u32::MAX);
        put(&mut d, 0x44, 0);
        put(&mut d, 0x48, 0);
        put(&mut d, 0x4c, 0x1100);
        put(&mut d, 0x60, 0);
        put(&mut d, 0x64, 0);
        put(&mut d, 0x68, 1);
        put(&mut d, 0x6c, 1);
        put(&mut d, 0x70, 0x2080);
        put(&mut d, 0x80, 0);
        put(&mut d, 0x84, 0);
        put(&mut d, 0x88, 0);
        put(&mut d, 0x8c, 0x1200);
        put(&mut d, 0x90, 0);
        let parent = BASE + 0x1000;
        let expect = vec![
            Funclet {
                parent,
                entry: BASE + 0x1100,
                role: FuncletRole::Unwind(1),
            },
            Funclet {
                parent,
                entry: BASE + 0x1200,
                role: FuncletRole::Catch(0, 0),
            },
        ];
        assert_eq!(funclets(&image(&d, Some("__CxxFrameHandler3"))), expect);
        assert_eq!(funclets(&image(&d, None)), expect);
    }

    /// A `FuncInfo`'s try block covers the instructions its IP-to-state map
    /// puts in its states, and its catch names the type its descriptor
    /// spells.
    ///
    /// # Panics
    ///
    /// When the guard is missed or misread.
    #[test]
    fn a_funcinfo_try_block_spans_its_states() {
        let mut d = vec![0u8; 0x100];
        let put =
            |d: &mut Vec<u8>, at: usize, v: u32| d[at..at + 4].copy_from_slice(&v.to_le_bytes());
        put(&mut d, 0x0, 0x2010);
        for (k, v) in [0x1993_0522u32, 1, 0x2040, 1, 0x2060, 3, 0x20a0]
            .iter()
            .enumerate()
        {
            put(&mut d, 0x10 + 4 * k, *v);
        }
        put(&mut d, 0x40, u32::MAX);
        for (k, v) in [0u32, 0, 0, 1, 0x2080].iter().enumerate() {
            put(&mut d, 0x60 + 4 * k, *v);
        }
        for (k, v) in [0x08u32, 0x20c0, 0, 0x1200, 0].iter().enumerate() {
            put(&mut d, 0x80 + 4 * k, *v);
        }
        for (k, v) in [0x1000u32, u32::MAX, 0x1004, 0, 0x1010, u32::MAX]
            .iter()
            .enumerate()
        {
            put(&mut d, 0xa0 + 4 * k, *v);
        }
        d[0xd0..0xdc].copy_from_slice(b".?AVError@@\0");
        let mut p = image(&d, Some("__CxxFrameHandler3"));
        p.function_ranges = vec![(BASE + 0x1000, BASE + 0x1100)];
        let found = guards(&p);
        assert_eq!(
            found.get(&(BASE + 0x1000)),
            Some(&vec![Guard {
                dialect: Dialect::Cxx,
                ranges: vec![(BASE + 0x1004, BASE + 0x1010)],
                clauses: vec![Clause {
                    kind: ClauseKind::Catch("Error &".to_owned()),
                    funclet: Some(BASE + 0x1200),
                    resume: None,
                    selector: None,
                }],
            }]),
            "{found:x?}"
        );
    }

    /// A compact `FuncInfo4`'s IP-to-state map counts each entry from the
    /// one before, its states stored one up, and a catch keeps the
    /// continuation its record names.
    ///
    /// # Panics
    ///
    /// When the guard is missed or misread.
    #[test]
    fn a_compact_funcinfo_try_block_spans_its_states() {
        let mut d = vec![0u8; 0x100];
        let put =
            |d: &mut Vec<u8>, at: usize, v: u32| d[at..at + 4].copy_from_slice(&v.to_le_bytes());
        put(&mut d, 0x0, 0x2010);
        d[0x10] = 0x10;
        put(&mut d, 0x11, 0x2060);
        put(&mut d, 0x15, 0x20a0);
        d[0x60] = 1 << 1;
        put(&mut d, 0x64, 0x2080);
        d[0x80] = 1 << 1;
        d[0x81] = 0x01 | 0x08 | 0x10;
        d[0x82] = 0x40 << 1;
        put(&mut d, 0x83, 0x1200);
        put(&mut d, 0x87, 0x1080);
        d[0xa0..0xa5].copy_from_slice(&[2 << 1, 4 << 1, 1 << 1, 0xc << 1, 0]);
        let mut p = image(&d, Some("__CxxFrameHandler4"));
        p.function_ranges = vec![(BASE + 0x1000, BASE + 0x1100)];
        let found = guards(&p);
        assert_eq!(
            found.get(&(BASE + 0x1000)),
            Some(&vec![Guard {
                dialect: Dialect::Cxx,
                ranges: vec![(BASE + 0x1004, BASE + 0x1010)],
                clauses: vec![Clause {
                    kind: ClauseKind::Catch("...".to_owned()),
                    funclet: Some(BASE + 0x1200),
                    resume: Some(BASE + 0x1080),
                    selector: None,
                }],
            }]),
            "{found:x?}"
        );
    }

    /// Each scope-table record is a `__try` over its range: a `__finally`
    /// names its funclet, an `__except` its filter and the body inside
    /// the function the runtime resumes at.
    ///
    /// # Panics
    ///
    /// When a guard is missed or misread.
    #[test]
    fn a_scope_table_record_is_a_guard() {
        let mut p = image(&scope_table(), Some("__C_specific_handler"));
        p.function_ranges = vec![(BASE + 0x1000, BASE + 0x1400)];
        let found = guards(&p);
        let seh = |ranges, kind, funclet, resume| Guard {
            dialect: Dialect::Seh,
            ranges,
            clauses: vec![Clause {
                kind,
                funclet,
                resume,
                selector: None,
            }],
        };
        assert_eq!(
            found.get(&(BASE + 0x1000)),
            Some(&vec![
                seh(
                    vec![(BASE + 0x1000, BASE + 0x1010)],
                    ClauseKind::Finally,
                    Some(BASE + 0x1100),
                    None
                ),
                seh(
                    vec![(BASE + 0x1010, BASE + 0x1020)],
                    ClauseKind::Except(Some(BASE + 0x1200)),
                    None,
                    Some(BASE + 0x1300)
                ),
            ]),
            "{found:x?}"
        );
    }
}
