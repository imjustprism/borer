//! Library signatures: a static library's functions as the library's own
//! objects describe them, written as a pack that names a program's copies.
//!
//! A program linked with a static library carries the library's functions
//! and none of their names. The library's objects still have them: each
//! function's bytes, the relocations the linker fills in (a call's target,
//! an address the code loads), and the symbol each relocation names.
//! [`read`] takes the functions out of a COFF object or an archive of them
//! (`.obj`, `.lib`) with the relocated bytes masked, and [`pack_text`]
//! writes them as `[names]` `lib` lines:
//!
//! ```text
//! lib 4883EC28E8????????4883C428C3 ?foo@@YAXXZ 5=?bar@@YAXXZ
//! ```
//!
//! the signature, the symbol's name as the object spells it, and each
//! relocation's offset in the function and the symbol it names. The
//! analysis matches them against the program
//! ([`crate::analysis::libnames`]): a signature long enough names the one
//! function it matches, and a short one, a thunk or a wrapper, names a
//! function when what it calls or reads is known by the name the library
//! gives it. Where the masking comes from the relocations themselves, no
//! byte is guessed: what the linker did not touch matches exactly.

use std::fmt::Write as _;

use crate::analysis::sigs::{SIG_MAX, format_signature, parse_signature};
use crate::text::one_line;

/// The 32-bit x86 COFF machine.
const I386: u16 = 0x14c;
/// The x64 COFF machine.
const AMD64: u16 = 0x8664;
/// `IMAGE_SCN_CNT_CODE`: the section holds code.
const SCN_CODE: u32 = 0x20;
/// `IMAGE_SYM_CLASS_EXTERNAL`.
const CLASS_EXTERNAL: u8 = 2;
/// `IMAGE_SYM_CLASS_STATIC`.
const CLASS_STATIC: u8 = 3;
/// `IMAGE_SYM_DTYPE_FUNCTION`, the derived type of a function symbol.
const DTYPE_FUNCTION: u16 = 2;

/// One function a library defines.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LibFunction {
    /// The symbol's name as the object spells it, decorations and all.
    pub name: String,
    /// Its first bytes, up to [`SIG_MAX`], the relocated ones masked and
    /// the padding after its end left out.
    pub sig: Vec<Option<u8>>,
    /// Each relocation inside the signature that names a symbol another
    /// object can name too (an external or a function): its offset from
    /// the entry and the symbol's name.
    pub refs: Vec<(u32, String)>,
}

impl LibFunction {
    /// How many of the signature's bytes are fixed.
    #[must_use]
    pub fn fixed(&self) -> usize {
        self.sig.iter().filter(|b| b.is_some()).count()
    }
}

/// Reads the functions a COFF object or an archive of objects defines.
///
/// Only x86 and x64 objects are read; an archive's import members and
/// objects of other machines are passed over. A damaged member is said so:
/// a header that does not parse, or a member (the linker's own included)
/// running past the end of the file, ends the walk there, and a member
/// holding no COFF object is skipped. A damaged archive read as one with
/// no functions, which wrote an empty pack and succeeded.
///
/// # Arguments
///
/// * `bytes` - The file: an archive (`!<arch>`) or one object.
///
/// # Returns
///
/// Every function with a name, in file order, and one line per damaged
/// member saying what was wrong with it.
///
/// # Errors
///
/// When the bytes are neither an archive nor a COFF object.
pub fn read(bytes: &[u8]) -> anyhow::Result<(Vec<LibFunction>, Vec<String>)> {
    let mut out = Vec::new();
    let mut damaged = Vec::new();
    if bytes.starts_with(b"!<arch>\n") {
        let mut offset = 8usize;
        while offset + goblin::archive::SIZEOF_HEADER <= bytes.len() {
            if offset % 2 == 1 {
                offset += 1;
            }
            let at = offset;
            let Some((start, member)) = goblin::archive::Member::parse(bytes, &mut offset)
                .ok()
                .and_then(|m| Some((usize::try_from(m.offset).ok()?, m)))
            else {
                damaged.push(format!(
                    "the member header at {at:#x} does not read; the rest of the archive is not read"
                ));
                break;
            };
            let size = member.size();
            offset = start.saturating_add(size);
            let name = member.header.name;
            let Some(data) = bytes.get(start..offset) else {
                damaged.push(format!(
                    "member {} at {at:#x} runs past the end of the file; the rest of the archive is not read",
                    one_line(name)
                ));
                break;
            };
            // SPEC: the linker members (`/`) and the long-name table (`//`)
            // are not objects.
            if name.starts_with('/')
                && name
                    .get(1..)
                    .is_none_or(|rest| !rest.starts_with(|c: char| c.is_ascii_digit()))
            {
                continue;
            }
            if let Err(why) = object_functions(data, &mut out) {
                damaged.push(format!("member {} at {at:#x}: {why}", one_line(name)));
            }
        }
        return Ok((out, damaged));
    }
    if goblin::pe::Coff::parse(bytes).is_err() {
        anyhow::bail!("neither an archive (.lib) nor a COFF object (.obj)");
    }
    object_functions(bytes, &mut out).map_err(anyhow::Error::msg)?;
    Ok((out, damaged))
}

/// How many bytes a relocation of `kind` rewrites.
///
/// # Arguments
///
/// * `machine` - The object's machine.
/// * `kind` - The relocation type.
fn reloc_width(machine: u16, kind: u16) -> usize {
    match (machine, kind) {
        // ABSOLUTE is padding in the table and rewrites nothing.
        (_, 0) => 0,
        (AMD64, 0x1) => 8,               // ADDR64
        (AMD64 | I386, 0xA) => 2,        // SECTION
        (AMD64, 0xC) | (I386, 0xD) => 1, // SECREL7
        (I386, 0x1 | 0x2) => 2,          // DIR16, REL16
        _ => 4,
    }
}

/// Adds the functions one object defines to `out`.
///
/// A function runs from its symbol to the next function symbol in its
/// section, or the section's end; `int3` padding after it is not its.
///
/// # Arguments
///
/// * `bytes` - The object.
/// * `out` - Where the functions go.
///
/// # Errors
///
/// When the bytes are not a COFF object; an import object, a big object
/// and an object of another machine are passed over without one.
fn object_functions(bytes: &[u8], out: &mut Vec<LibFunction>) -> Result<(), &'static str> {
    // SPEC: an import object and a big object both open `0000 FFFF`.
    if bytes.get(..4) == Some(&[0, 0, 0xff, 0xff][..]) {
        return Ok(());
    }
    let coff = goblin::pe::Coff::parse(bytes).map_err(|_| "not a COFF object")?;
    let machine = coff.header.machine;
    if !matches!(machine, I386 | AMD64) {
        return Ok(());
    }
    let (Some(symbols), Some(strings)) = (&coff.symbols, &coff.strings) else {
        return Ok(());
    };
    // Names by symbol index, and whether a reference to it says anything
    // another object could say too.
    let mut names: Vec<(usize, String, bool)> = Vec::new();
    let mut functions: Vec<(usize, u32, String)> = Vec::new();
    for (index, _, sym) in symbols.iter() {
        let Ok(name) = sym.name(strings) else {
            continue;
        };
        let function = (sym.typ >> 4) & 3 == DTYPE_FUNCTION;
        names.push((
            index,
            name.to_owned(),
            sym.storage_class == CLASS_EXTERNAL || function,
        ));
        if function
            && matches!(sym.storage_class, CLASS_EXTERNAL | CLASS_STATIC)
            && let Ok(section) = usize::try_from(sym.section_number)
            && section > 0
        {
            functions.push((section, sym.value, name.to_owned()));
        }
    }
    functions.sort_unstable();
    functions.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1);
    let mut at = 0;
    while at < functions.len() {
        let section = functions[at].0;
        let end = functions[at..]
            .iter()
            .position(|f| f.0 != section)
            .map_or(functions.len(), |n| at + n);
        section_functions(bytes, &coff, machine, &names, &functions[at..end], out);
        at = end;
    }
    Ok(())
}

/// Adds the functions of one section to `out`.
///
/// # Arguments
///
/// * `bytes` - The object.
/// * `coff` - The object parsed.
/// * `machine` - Its machine.
/// * `names` - Symbol names by index, with whether a reference to each is
///   worth keeping.
/// * `functions` - The section's function symbols: section, offset, name,
///   sorted by offset.
/// * `out` - Where the functions go.
fn section_functions(
    bytes: &[u8],
    coff: &goblin::pe::Coff<'_>,
    machine: u16,
    names: &[(usize, String, bool)],
    functions: &[(usize, u32, String)],
    out: &mut Vec<LibFunction>,
) {
    let Some(section) = functions
        .first()
        .and_then(|f| f.0.checked_sub(1))
        .and_then(|i| coff.sections.get(i))
    else {
        return;
    };
    if section.characteristics & SCN_CODE == 0 || section.pointer_to_raw_data == 0 {
        return;
    }
    let start = section.pointer_to_raw_data as usize;
    let size = section.size_of_raw_data as usize;
    let Some(data) = bytes.get(start..start.saturating_add(size)) else {
        return;
    };
    let mut masked: Vec<Option<u8>> = data.iter().copied().map(Some).collect();
    let mut refs: Vec<(usize, &str)> = Vec::new();
    if let Ok(relocations) = section.relocations(bytes) {
        for r in relocations.take(usize::from(section.number_of_relocations)) {
            let at = r.virtual_address as usize;
            let width = reloc_width(machine, r.typ);
            for b in masked.iter_mut().skip(at).take(width) {
                *b = None;
            }
            let index = r.symbol_table_index as usize;
            if let Ok(i) = names.binary_search_by_key(&index, |n| n.0)
                && let Some((_, name, true)) = names.get(i)
            {
                refs.push((at, name));
            }
        }
    }
    for (i, (_, offset, name)) in functions.iter().enumerate() {
        let from = *offset as usize;
        let to = functions
            .get(i + 1)
            .map_or(size, |f| f.1 as usize)
            .min(size);
        let Some(body) = masked.get(from..to) else {
            continue;
        };
        let len = body.len() - body.iter().rev().take_while(|b| **b == Some(0xcc)).count();
        if len == 0 {
            continue;
        }
        let cut = len.min(SIG_MAX);
        out.push(LibFunction {
            name: name.clone(),
            sig: body[..cut].to_vec(),
            refs: refs
                .iter()
                .filter(|(at, _)| *at >= from && *at < from + cut)
                .filter_map(|(at, n)| Some((u32::try_from(at - from).ok()?, (*n).to_owned())))
                .collect(),
        });
    }
}

/// Writes library functions as a pack: `pack`, `about`, then a `[names]`
/// `lib` line for each distinct function.
///
/// # Arguments
///
/// * `name` - The pack's name, one word.
/// * `about` - What the pack is for, one line.
/// * `functions` - The functions, from [`read`].
#[must_use]
pub fn pack_text(name: &str, about: &str, functions: &[LibFunction]) -> String {
    let mut distinct: Vec<&LibFunction> = functions.iter().collect();
    distinct.sort_unstable();
    distinct.dedup();
    let mut out = format!(
        "# library signatures: {} functions; borer sigmake writes these\npack {name} 1\nabout {about}\n\n[names]\n",
        distinct.len()
    );
    for f in distinct {
        let _ = write!(out, "lib {} {}", format_signature(&f.sig), f.name);
        for (at, target) in &f.refs {
            let _ = write!(out, " {at:x}={target}");
        }
        out.push('\n');
    }
    out
}

/// Reads a `lib` line's value back: the signature, the name and the
/// references.
///
/// # Arguments
///
/// * `value` - The line after its `lib` key.
///
/// # Returns
///
/// The function, or `None` when a field does not read.
#[must_use]
pub fn parse_line(value: &str) -> Option<LibFunction> {
    let mut words = value.split_whitespace();
    let sig = parse_signature(words.next()?)?;
    let name = words.next()?.to_owned();
    let refs = words
        .map(|w| {
            let (at, target) = w.split_once('=')?;
            Some((u32::from_str_radix(at, 16).ok()?, target.to_owned()))
        })
        .collect::<Option<Vec<_>>>()?;
    Some(LibFunction { name, sig, refs })
}

#[cfg(test)]
mod tests {
    use super::{LibFunction, pack_text, parse_line, read};

    /// A test object's offset or count as the little-endian 32-bit field COFF stores.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    ///
    /// # Panics
    ///
    /// When `v` does not fit 32 bits, which no test object approaches.
    fn le32(v: usize) -> [u8; 4] {
        u32::try_from(v)
            .expect("a test object is smaller than 4 GiB")
            .to_le_bytes()
    }

    /// A test object's count as the little-endian 16-bit field COFF stores.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    ///
    /// # Panics
    ///
    /// When `v` does not fit 16 bits, which no test object approaches.
    fn le16(v: usize) -> [u8; 2] {
        u16::try_from(v)
            .expect("a test object has fewer than 65536 relocations")
            .to_le_bytes()
    }

    /// Builds a COFF object: one `.text` section holding `code` with
    /// `relocs` `(offset, symbol index, type)`, and `symbols` `(name,
    /// section, value, type, class)` in order.
    fn object(
        machine: u16,
        code: &[u8],
        relocs: &[(u32, u32, u16)],
        symbols: &[(&str, i16, u32, u16, u8)],
    ) -> Vec<u8> {
        let mut o = Vec::new();
        let text_at = 20 + 40;
        let relocs_at = text_at + code.len();
        let symtab_at = relocs_at + relocs.len() * 10;
        o.extend_from_slice(&machine.to_le_bytes());
        o.extend_from_slice(&1u16.to_le_bytes()); // sections
        o.extend_from_slice(&0u32.to_le_bytes()); // time stamp
        o.extend_from_slice(&le32(symtab_at));
        o.extend_from_slice(&le32(symbols.len()));
        o.extend_from_slice(&0u16.to_le_bytes()); // optional header
        o.extend_from_slice(&0u16.to_le_bytes()); // characteristics
        o.extend_from_slice(b".text\0\0\0");
        o.extend_from_slice(&0u32.to_le_bytes()); // virtual size
        o.extend_from_slice(&0u32.to_le_bytes()); // virtual address
        o.extend_from_slice(&le32(code.len()));
        o.extend_from_slice(&le32(text_at));
        o.extend_from_slice(&le32(relocs_at));
        o.extend_from_slice(&0u32.to_le_bytes()); // line numbers
        o.extend_from_slice(&le16(relocs.len()));
        o.extend_from_slice(&0u16.to_le_bytes());
        o.extend_from_slice(&0x6000_0020u32.to_le_bytes()); // code, execute, read
        o.extend_from_slice(code);
        for (at, sym, kind) in relocs {
            o.extend_from_slice(&at.to_le_bytes());
            o.extend_from_slice(&sym.to_le_bytes());
            o.extend_from_slice(&kind.to_le_bytes());
        }
        let mut strings: Vec<u8> = Vec::new();
        for (name, section, value, typ, class) in symbols {
            if name.len() <= 8 {
                let mut short = [0u8; 8];
                short[..name.len()].copy_from_slice(name.as_bytes());
                o.extend_from_slice(&short);
            } else {
                o.extend_from_slice(&0u32.to_le_bytes());
                o.extend_from_slice(&le32(4 + strings.len()));
                strings.extend_from_slice(name.as_bytes());
                strings.push(0);
            }
            o.extend_from_slice(&value.to_le_bytes());
            o.extend_from_slice(&section.to_le_bytes());
            o.extend_from_slice(&typ.to_le_bytes());
            o.push(*class);
            o.push(0); // aux symbols
        }
        o.extend_from_slice(&le32(4 + strings.len()));
        o.extend_from_slice(&strings);
        o
    }

    /// An object's functions come out with the relocated bytes masked and
    /// each relocation naming its symbol, and a pack line reads back.
    ///
    /// # Panics
    ///
    /// When a function, a mask or a reference is misread.
    #[test]
    fn an_object_gives_its_functions_masked() {
        let code = [
            0x48, 0x83, 0xec, 0x28, // sub rsp,0x28
            0xe8, 0, 0, 0, 0, // call helper
            0x48, 0x83, 0xc4, 0x28, // add rsp,0x28
            0xc3, // ret
            0xcc, 0xcc, // padding
            0xe9, 0, 0, 0, 0, // helper: jmp __imp_Sleep's thunk
        ];
        let obj = object(
            0x8664,
            &code,
            &[(5, 1, 4), (17, 2, 4)],
            &[
                ("?caller@@YAXXZ", 1, 0, 0x20, 2),
                ("helper_function", 1, 16, 0x20, 3),
                ("Sleep", 0, 0, 0x20, 2),
            ],
        );
        let (found, damaged) = read(&obj).expect("reads");
        assert!(damaged.is_empty(), "{damaged:?}");
        assert_eq!(found.len(), 2);
        let caller = &found[0];
        assert_eq!(caller.name, "?caller@@YAXXZ");
        assert_eq!(caller.sig.len(), 14, "the padding is not the function's");
        assert!(caller.sig[5..9].iter().all(Option::is_none));
        assert_eq!(caller.sig[4], Some(0xe8));
        assert_eq!(caller.refs, vec![(5, "helper_function".to_owned())]);
        assert_eq!(found[1].refs, vec![(1, "Sleep".to_owned())]);
        let text = pack_text("crt", "a test", &found);
        let line = text
            .lines()
            .find_map(|l| l.strip_prefix("lib ").filter(|l| l.contains("caller")))
            .expect("a lib line");
        assert_eq!(parse_line(line), Some(caller.clone()));
    }

    /// An archive's damaged members are named, not read as members with no
    /// functions: a member that holds no object is skipped and said so, and
    /// a header that does not read ends the walk and says so.
    ///
    /// # Panics
    ///
    /// When a damaged member goes unreported or a sound one is lost.
    #[test]
    fn an_archive_names_its_damaged_members() {
        /// An archive member: its 60-byte header, then its bytes, padded
        /// to an even length.
        fn member(name: &str, data: &[u8]) -> Vec<u8> {
            let mut m = format!("{name:<16}{:<12}{:<6}{:<6}{:<8}", 0, 0, 0, 644).into_bytes();
            m.extend_from_slice(format!("{:<10}`\n", data.len()).as_bytes());
            m.extend_from_slice(data);
            if data.len() % 2 == 1 {
                m.push(b'\n');
            }
            m
        }
        let obj = object(0x8664, &[0xc3], &[], &[("f", 1, 0, 0x20, 2)]);
        let mut lib = b"!<arch>\n".to_vec();
        lib.extend(member("good.obj/", &obj));
        lib.extend(member("bad.obj/", b"not an object at all"));
        let (found, damaged) = read(&lib).expect("reads");
        assert_eq!(found.len(), 1, "the sound member is read");
        assert_eq!(damaged.len(), 1, "{damaged:?}");
        assert!(
            damaged[0].starts_with("member bad.obj") && damaged[0].ends_with(": not a COFF object"),
            "{damaged:?}"
        );
        let mut short = b"!<arch>\n".to_vec();
        short.extend(member("/", &[0; 64]));
        short.truncate(short.len() - 32);
        let (found, damaged) = read(&short).expect("reads");
        assert!(found.is_empty());
        assert_eq!(damaged.len(), 1, "{damaged:?}");
        assert!(
            damaged[0].ends_with(
                " at 0x8 runs past the end of the file; the rest of the archive is not read"
            ),
            "a cut linker member is named: {damaged:?}"
        );
        let mut cut = b"!<arch>\n".to_vec();
        cut.extend_from_slice(&[b'#'; 60]);
        let (found, damaged) = read(&cut).expect("reads");
        assert!(found.is_empty());
        assert_eq!(
            damaged,
            vec!["the member header at 0x8 does not read; the rest of the archive is not read"]
        );
    }

    /// Bytes that are neither an archive nor an object are refused.
    ///
    /// # Panics
    ///
    /// When they are read as something.
    #[test]
    fn other_bytes_are_refused() {
        assert!(read(b"MZ not an object").is_err());
        assert!(
            parse_line("4883 name").is_some_and(|f: LibFunction| f.refs.is_empty()),
            "a line without references reads"
        );
        assert!(parse_line("zz name").is_none());
    }
}
