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

use crate::analysis::FuncletRole;
use crate::fxmap::FxHashMap;
use crate::headers::ExceptionHandler;
use crate::program::{Program, SymbolKind};

/// Most `__try` scopes read from one table.
const SCOPES_MAX: u32 = 4096;
/// Most unwind states read from one `FuncInfo`.
const STATES_MAX: u32 = 4096;
/// Most try blocks read from one `FuncInfo`.
const TRY_BLOCKS_MAX: u32 = 1024;
/// Most catch clauses read from one try block.
const CATCHES_MAX: u32 = 64;
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
    // SPEC: `__GSHandlerCheck_EH` is `__CxxFrameHandler3` with the cookie
    // check in front, and its data opens the same way; `_EH4` is the
    // compressed record this does not read.
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
    // Unnamed: the shapes with a signature first, then the scope table
    // validated record by record, then the compact record, believed only
    // when everything it names holds together.
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
    Some((v >> shift, at.wrapping_add(len as u64)))
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
            // SPEC: the low two bits are the entry's kind - 0 no action, 1 a
            // destructor the runtime calls on an object at a frame offset,
            // 2 the same through a pointer, 3 a funclet - and every kind but
            // 0 carries an address next. A destructor is a function in its
            // own right, called from wherever the object dies, and only the
            // funclet is a piece of this function.
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
                // SPEC: an image-relative address when the flags say so,
                // an offset from the parent's start otherwise.
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

/// Reads a little-endian `u32`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `at` - The value's address.
fn read_u32(program: &Program, at: u64) -> Option<u32> {
    let bytes = program.read_va(at, 4)?;
    Some(u32::from_le_bytes(bytes.try_into().ok()?))
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::{Funclet, continuations, funclets};
    use crate::analysis::FuncletRole;
    use crate::headers::{ExceptionHandler, Headers};
    use crate::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};

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
        // `.text`: a function at +0x1000, a funclet at +0x1100, a second at
        // +0x1200, an `__except` label at +0x1300, and at +0x1400 the
        // handler's import thunk `jmp [rip + slot]` with the slot at +0x2800.
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
            va: BASE + off,
            vsize: 0x1000,
            file_off: off,
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
        Program {
            path: PathBuf::new(),
            bytes,
            format: BinaryFormat::Pe,
            arch: Arch::X86_64,
            is_64: true,
            entry: Some(BASE + 0x1000),
            image_base: BASE,
            sections: vec![
                section(".text", 0x1000, true),
                section(".rdata", 0x2000, false),
            ],
            symbols,
            function_ranges: Vec::new(),
            headers,
            debug_functions: Vec::new(),
            debug_types: std::collections::BTreeMap::new(),
            pdb: None,
            pdb_record: None,
            pdb_source: None,
            flat_fallback: false,
        }
    }

    /// A scope table with a `__finally` and an `__except` with a filter.
    fn scope_table() -> Vec<u8> {
        let mut d = Vec::new();
        d.extend_from_slice(&2u32.to_le_bytes());
        // scope 0: __try 0x1000..0x1010 { } __finally at 0x1100
        for v in [0x1000u32, 0x1010, 0x1100, 0] {
            d.extend_from_slice(&v.to_le_bytes());
        }
        // scope 1: __try 0x1010..0x1020 { } __except(filter at 0x1200) body at 0x1300
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
        // the data opens with the record's address: +0x2010
        put(&mut d, 0x0, 0x2010);
        // FuncInfo4: header (unwind map + try-block map), then the two maps
        d[0x10] = 0x08 | 0x10;
        put(&mut d, 0x11, 0x2040);
        put(&mut d, 0x15, 0x2060);
        // unwind map: 2 entries; state 0 kind 0; state 1 kind 3 (a plain
        // address) with the action at +0x1100. Compact ints below 128 are
        // the value shifted left one.
        d[0x40] = 2 << 1;
        d[0x41] = 1 << 1; // state 0: kind 1, a destructor called directly
        put(&mut d, 0x42, 0x1300); // ... the destructor: a function, not a funclet
        d[0x46] = 0x20 << 1; // ... at frame offset 0x20
        d[0x47] = 3 << 1; // state 1: kind 3, a funclet
        put(&mut d, 0x48, 0x1100);
        // try-block map: 1 entry; low, high, catch-high 0; handlers at +0x2080
        d[0x60] = 1 << 1;
        d[0x61] = 0;
        d[0x62] = 0;
        d[0x63] = 0;
        put(&mut d, 0x64, 0x2080);
        // handler array: 1 catch; flags: adjectives present, one continuation
        // as an RVA; adjectives 0x40 (`catch (...)`), handler +0x1200, continuation +0x1000
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
        // and by its shape when the handler has no name
        assert_eq!(funclets(&image(&d, None)), expect);
        // the catch resumes its parent at the continuation
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
        // the data opens with the FuncInfo's address: +0x2010
        put(&mut d, 0x0, 0x2010);
        // FuncInfo at +0x2010: magic, 2 states, unwind map at +0x2040,
        // 1 try block, try-block map at +0x2060
        put(&mut d, 0x10, 0x1993_0522);
        put(&mut d, 0x14, 2);
        put(&mut d, 0x18, 0x2040);
        put(&mut d, 0x1c, 1);
        put(&mut d, 0x20, 0x2060);
        // unwind map: state 0 -> no action, state 1 -> action at +0x1100
        put(&mut d, 0x40, u32::MAX);
        put(&mut d, 0x44, 0);
        put(&mut d, 0x48, 0);
        put(&mut d, 0x4c, 0x1100);
        // try block 0: low 0, high 0, catchHigh 1, 1 catch, handlers at +0x2080
        put(&mut d, 0x60, 0);
        put(&mut d, 0x64, 0);
        put(&mut d, 0x68, 1);
        put(&mut d, 0x6c, 1);
        put(&mut d, 0x70, 0x2080);
        // handler 0: adjectives, type, catch object, handler at +0x1200, frame
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
        // and told by its magic when the handler has no name
        assert_eq!(funclets(&image(&d, None)), expect);
    }
}
