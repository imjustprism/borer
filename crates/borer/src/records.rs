//! The records `export --c --records` writes beside the C file.
//!
//! One JSON line per written definition says what the engine states of it
//! ([`borer_engine::analysis::decompile::export::records`]). The format is
//! documented for readers in `docs/records.md`.
//!
//! The lines stream to a `.part` file while the export runs, each with its
//! head's line among the definitions, so memory never holds the file. Once
//! the C file is written, the records are written beside their target and
//! moved over it. The first line names the C file's length and FNV-1a hash
//! ([`Content`]), so a reader tells a records file from another export (a
//! write that failed between the two files, or an export without
//! `--records` that left an older one) from one that matches its C file.

use std::io::{BufRead as _, Read, Write};
use std::path::{Path, PathBuf};

use anyhow::{Context as _, bail};
use borer_engine::analysis::decompile::export::Records;
use borer_engine::analysis::decompile::export::records::{Home, Record, Role, SinkLine};
use borer_engine::text::short_path;
use serde_json::{Value, json};

use crate::output::{Existing, create};

/// The records format's name, on the file's first line.
pub const FORMAT: &str = "borer-records";

/// The records format's version, raised only by a change that breaks a
/// reader of the one before.
pub const VERSION: u32 = 1;

/// A line of the C file, from 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FileLine(usize);

/// The records being written for one export: their `.part` file.
#[derive(Debug)]
pub struct Part {
    /// Where the lines go while the export runs.
    file: std::io::BufWriter<std::fs::File>,
    /// The `.part` file's path.
    path: PathBuf,
    /// The records file.
    out: PathBuf,
    /// The C file's bare name, for the first line.
    c: String,
}

/// The C file's length and its 64-bit FNV-1a hash, counted as it is
/// written, which the records' first line names.
#[derive(Debug, Clone, Copy)]
pub struct Content {
    /// Bytes written.
    pub len: u64,
    /// FNV-1a over them, 64 bits.
    pub fnv: u64,
}

impl Default for Content {
    fn default() -> Self {
        Self {
            len: 0,
            fnv: 0xcbf2_9ce4_8422_2325,
        }
    }
}

impl Content {
    /// Copies `from` into `to`, counting every byte.
    ///
    /// # Arguments
    ///
    /// * `from` - What to copy.
    /// * `to` - Where it goes.
    ///
    /// # Errors
    ///
    /// When a read or a write fails.
    pub fn copy(&mut self, from: &mut impl Read, to: &mut impl Write) -> std::io::Result<()> {
        let mut buf = vec![0u8; 1 << 16];
        loop {
            let n = from.read(&mut buf)?;
            let Some(chunk) = buf.get(..n).filter(|c| !c.is_empty()) else {
                return Ok(());
            };
            self.add(chunk);
            to.write_all(chunk)?;
        }
    }

    /// Counts more bytes of the C file.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The next bytes written.
    pub fn add(&mut self, bytes: &[u8]) {
        self.len = self.len.saturating_add(from_len(bytes.len()));
        for &b in bytes {
            self.fnv = (self.fnv ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
    }
}

/// Returns a length in bytes as a `u64`.
///
/// # Arguments
///
/// * `n` - The length.
fn from_len(n: usize) -> u64 {
    u64::try_from(n).unwrap_or(u64::MAX)
}

/// Returns the records file that goes beside a C file.
///
/// # Arguments
///
/// * `c` - The C file's path.
#[must_use]
pub fn path_beside(c: &str) -> PathBuf {
    Path::new(c).with_extension("records.jsonl")
}

/// Returns `path` with `suffix` after its last component.
///
/// # Arguments
///
/// * `path` - A path.
/// * `suffix` - What to append, `.part` or `.new`.
fn suffixed(path: &Path, suffix: &str) -> PathBuf {
    let mut p = path.as_os_str().to_owned();
    p.push(suffix);
    PathBuf::from(p)
}

/// Returns a path as a message shows it.
///
/// # Arguments
///
/// * `path` - The path.
fn shown(path: &Path) -> String {
    short_path(&path.display().to_string())
}

impl Part {
    /// Starts the records of an export to `c`, if they were asked for,
    /// refusing before anything is written when the records file cannot
    /// be written or is there and `existing` keeps it.
    ///
    /// # Arguments
    ///
    /// * `c` - The C file's path.
    /// * `records` - Whether to write them.
    /// * `existing` - Whether a file already at the records' path is
    ///   replaced.
    ///
    /// # Returns
    ///
    /// The part being written, `None` under [`Records::Skip`].
    ///
    /// # Errors
    ///
    /// When the records' path is unusable, a file is there under
    /// [`Existing::Keep`], or the `.part` file cannot be created.
    pub fn new(c: &str, records: Records, existing: Existing) -> anyhow::Result<Option<Self>> {
        if records == Records::Skip {
            return Ok(None);
        }
        let out = path_beside(c);
        if let Some(why) = borer_engine::program::unusable_path(&out) {
            bail!("{why}; nothing was written");
        }
        #[expect(clippy::disallowed_methods, reason = "unusable_path cleared out")]
        let occupied = existing == Existing::Keep && std::fs::symlink_metadata(&out).is_ok();
        if occupied {
            bail!("{} exists; nothing was written", shown(&out));
        }
        let path = suffixed(&out, ".part");
        let file = create(&path, Existing::Replace)
            .with_context(|| format!("creating {}", shown(&path)))?;
        let c = Path::new(c)
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        Ok(Some(Self {
            file: std::io::BufWriter::new(file),
            path,
            out,
            c,
        }))
    }

    /// Writes one definition's record, its head line still counted among
    /// the definitions.
    ///
    /// # Arguments
    ///
    /// * `line` - The head's line among the definitions.
    /// * `record` - The record.
    ///
    /// # Errors
    ///
    /// When the write fails.
    pub fn add(&mut self, line: SinkLine, record: &Record) -> anyhow::Result<()> {
        writeln!(self.file, "{}\t{}", line.0, to_json(record))
            .with_context(|| format!("writing {}", shown(&self.path)))
    }

    /// Removes the `.part` file, for an export that wrote nothing.
    ///
    /// # Errors
    ///
    /// When it cannot be removed.
    pub fn drop_part(self) -> anyhow::Result<()> {
        let Self { file, path, .. } = self;
        drop(file);
        std::fs::remove_file(&path).with_context(|| format!("removing {}", shown(&path)))
    }

    /// Writes the finished records from the `.part` file, each head line
    /// moved past the C file's `head` lines and the first line naming the C
    /// file's content, beside their target, then moves them over it and
    /// removes the part.
    ///
    /// # Arguments
    ///
    /// * `head` - How many lines the C file holds above its first
    ///   definition.
    /// * `c` - The C file's length and hash.
    ///
    /// # Errors
    ///
    /// When a file cannot be read, written, moved or removed, or a part line
    /// is not one [`Part::add`] wrote; the records written beside their
    /// target are removed, and a file already there is left as it was.
    pub fn finish(mut self, head: usize, c: Content) -> anyhow::Result<()> {
        self.file
            .flush()
            .with_context(|| format!("writing {}", shown(&self.path)))?;
        let Self {
            file,
            path,
            out,
            c: name,
        } = self;
        drop(file);
        let staged = suffixed(&out, ".new");
        let wrote = write_finished(&path, &staged, head, &name, c).and_then(|()| {
            std::fs::rename(&staged, &out).with_context(|| format!("replacing {}", shown(&out)))
        });
        if wrote.is_err() {
            #[expect(clippy::disallowed_methods, reason = "the file this export just wrote")]
            let left = std::fs::symlink_metadata(&staged).is_ok();
            if left {
                std::fs::remove_file(&staged)
                    .with_context(|| format!("removing {}", shown(&staged)))?;
            }
        }
        wrote?;
        std::fs::remove_file(&path).with_context(|| format!("removing {}", shown(&path)))
    }
}

/// Writes the finished records at `staged` from the `.part` at `path`.
///
/// # Arguments
///
/// * `path` - The `.part` file.
/// * `staged` - Where the finished records go.
/// * `head` - How many lines the C file holds above its first definition.
/// * `name` - The C file's bare name.
/// * `c` - Its length and hash.
///
/// # Errors
///
/// When a file cannot be read or written, or a part line is not one
/// [`Part::add`] wrote.
fn write_finished(
    path: &Path,
    staged: &Path,
    head: usize,
    name: &str,
    c: Content,
) -> anyhow::Result<()> {
    let mut to = std::io::BufWriter::new(
        create(staged, Existing::Replace).with_context(|| format!("creating {}", shown(staged)))?,
    );
    let first = json!({
        "c": name,
        "c_bytes": c.len,
        "c_fnv1a64": format!("{:016x}", c.fnv),
        "format": FORMAT,
        "version": VERSION,
    });
    writeln!(to, "{first}").with_context(|| format!("writing {}", shown(staged)))?;
    #[expect(clippy::disallowed_methods, reason = "the part this export just wrote")]
    let from = std::fs::File::open(path).with_context(|| format!("reading {}", shown(path)))?;
    for row in std::io::BufReader::new(from).lines() {
        let row = row.with_context(|| format!("reading {}", shown(path)))?;
        let v = placed(&row, head).with_context(|| format!("reading {}", shown(path)))?;
        writeln!(to, "{v}").with_context(|| format!("writing {}", shown(staged)))?;
    }
    to.flush()
        .with_context(|| format!("writing {}", shown(staged)))
}

/// Returns one part line's record with its C file line set.
///
/// # Arguments
///
/// * `row` - A line [`Part::add`] wrote: the head's line among the
///   definitions, a tab, the record's JSON object.
/// * `head` - How many lines the C file holds above its first definition.
///
/// # Errors
///
/// When the row has no tab, its line is no number or its record is no
/// JSON object.
fn placed(row: &str, head: usize) -> anyhow::Result<Value> {
    let (at, rest) = row
        .split_once('\t')
        .with_context(|| format!("a record line without its head line: {row:.80}"))?;
    let at: usize = at.parse().context("a record's head line is no number")?;
    let mut v: Value = serde_json::from_str(rest).context("a record is no JSON")?;
    let Value::Object(m) = &mut v else {
        bail!("a record is no JSON object");
    };
    let line = FileLine(at.saturating_add(head).saturating_add(1));
    m.insert("line".to_owned(), json!(line.0));
    Ok(v)
}

/// Returns an address as borer writes one, `0x` and lowercase hex.
///
/// # Arguments
///
/// * `va` - The address.
fn hex(va: u64) -> String {
    format!("{va:#x}")
}

/// Returns one record as the JSON object of its line, without its C file
/// line.
///
/// # Arguments
///
/// * `r` - The record.
fn to_json(r: &Record) -> Value {
    let variables: Vec<Value> = r
        .variables
        .iter()
        .map(|v| {
            let home = match &v.home {
                Home::Register(name) => json!({"kind": "register", "name": name}),
                Home::Cfa(off) => json!({"kind": "frame", "base": "cfa", "offset": off}),
                Home::Unknown => json!({"kind": "unknown"}),
            };
            let param = match v.role {
                Role::Param(i) => json!(i),
                Role::Local => Value::Null,
            };
            let lines: Vec<usize> = v.lines.iter().map(|l| l.0).collect();
            json!({"name": v.name, "type": v.ty, "param": param, "home": home, "lines": lines})
        })
        .collect();
    let lines: Vec<Value> = r
        .lines
        .iter()
        .map(|(n, b)| json!({"line": n.0, "block": hex(*b)}))
        .collect();
    let blocks: Vec<Value> = r
        .blocks
        .iter()
        .map(|(start, b)| {
            let starts: Vec<String> = b.starts.iter().map(|&s| hex(s)).collect();
            json!({"start": hex(*start), "starts": starts, "cut": b.cut})
        })
        .collect();
    json!({"name": r.name, "entry": hex(r.entry), "variables": variables, "lines": lines, "blocks": blocks})
}

/// Returns `err` after removing an export's `.part` files, with any removal
/// that failed added as context over it, so the agent reads both and
/// neither hides the other.
///
/// # Arguments
///
/// * `err` - Why the export stopped.
/// * `part` - The C file's `.part`; one already gone is no failure.
/// * `recs` - The records' `.part`, `None` under [`Records::Skip`].
pub fn discard(err: anyhow::Error, part: &Path, recs: Option<Part>) -> anyhow::Error {
    let c = match std::fs::remove_file(part) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => Some(format!(
            "removing {}: {e}",
            short_path(&part.display().to_string())
        )),
        _ => None,
    };
    let r = recs
        .and_then(|r| r.drop_part().err())
        .map(|e| format!("{e:#}"));
    let failed: Vec<String> = c.into_iter().chain(r).collect();
    if failed.is_empty() {
        err
    } else {
        err.context(format!("cleaning up also failed ({})", failed.join("; ")))
    }
}

#[cfg(test)]
mod tests {
    use super::{Content, FORMAT, path_beside, placed};
    use crate::export::write_entries;
    use crate::output::Existing;
    use borer_engine::analysis::decompile::export::{Library, Records};
    use borer_engine::analysis::{Analysis, Overlay};
    use borer_engine::program::{Arch, Program, Section};

    /// Returns a caller and its leaf in a raw image, entered at the caller.
    fn pair() -> Program {
        let mut code = vec![0xccu8; 0x20];
        code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 1; ret
        code[0x10..0x15].copy_from_slice(&[0xe8, 0xeb, 0xff, 0xff, 0xff]); // ASM: call 0x1000
        code[0x15] = 0xc3; // ASM: ret
        let text = Section::mapped(".text", 0x1000, 0, 0x20, false, true);
        Program::raw(code, Arch::X86_64, 0, Some(0x1010), vec![text])
    }

    /// An export whose C file cannot be made removes both `.part` files and
    /// answers why the C file failed.
    ///
    /// A directory stands where the C file goes, so creating it fails after
    /// both parts were written.
    ///
    /// # Panics
    ///
    /// When the export succeeds, a `.part` is left or the error does not
    /// name the C file.
    #[test]
    #[expect(clippy::disallowed_methods, reason = "a temp dir this test made")]
    fn an_export_that_cannot_make_its_c_file_leaves_no_part() {
        let p = pair();
        let mut a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-noc-{}", std::process::id()));
        let out = dir.join("c.c");
        std::fs::create_dir_all(&out).expect("a directory where the C file goes");
        let out = out.display().to_string();
        let failed = write_entries(
            &p,
            &mut a,
            &Overlay::default(),
            (Library::Skip, Records::Write),
            None,
            &out,
            Existing::Replace,
        );
        let left: Vec<String> = std::fs::read_dir(&dir)
            .expect("reads the temp dir")
            .filter_map(|e| e.ok())
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .filter(|n| n.ends_with(".part"))
            .collect();
        std::fs::remove_dir_all(&dir).expect("cleans up");
        let why = format!("{:#}", failed.expect_err("no C file can be made"));
        assert!(why.contains("c.c"), "{why}");
        assert!(left.is_empty(), "{left:?}");
    }

    /// The records file starts with its format line, each further line's
    /// `line` is the C file's line of that definition's head, addresses
    /// are hex strings, and no `.part` or staged file stays behind.
    ///
    /// # Panics
    ///
    /// When a file is missing, a line does not parse, or a head line is
    /// not the definition's signature.
    #[test]
    #[expect(clippy::disallowed_methods, reason = "a temp dir this test made")]
    fn each_record_points_at_its_head_in_the_c_file() {
        let p = pair();
        let mut a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-records-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let out = dir.join("o.c").display().to_string();
        let both = (Library::Include, Records::Write);
        let o = Overlay::default();
        write_entries(&p, &mut a, &o, both, None, &out, Existing::Replace).expect("writes");
        let c = std::fs::read_to_string(&out).expect("the C file");
        let records = std::fs::read_to_string(path_beside(&out)).expect("the records");
        let left: Vec<_> = std::fs::read_dir(&dir).expect("lists").flatten().collect();
        let keep = write_entries(&p, &mut a, &o, both, None, &out, Existing::Keep);
        std::fs::remove_dir_all(&dir).expect("cleans up");
        assert!(keep.is_err());
        assert_eq!(left.len(), 2, "{left:?}");
        let mut rows = records.lines();
        let first: serde_json::Value =
            serde_json::from_str(rows.next().expect("a first line")).expect("JSON");
        let mut content = Content::default();
        content.add(c.as_bytes());
        let fnv = format!("{:016x}", content.fnv);
        assert_eq!(first["c"], "o.c");
        assert_eq!(
            (first["format"].as_str(), first["version"].as_u64()),
            (Some(FORMAT), Some(1))
        );
        assert_eq!(first["c_bytes"].as_u64(), Some(content.len));
        assert_eq!(first["c_fnv1a64"].as_str(), Some(fnv.as_str()));
        let c_lines: Vec<&str> = c.lines().collect();
        let mut names = Vec::new();
        for row in rows {
            let v: serde_json::Value = serde_json::from_str(row).expect("a JSON line");
            let name = v["name"].as_str().expect("a name").to_owned();
            let line = v["line"].as_u64().and_then(|l| usize::try_from(l).ok());
            let line = line.expect("a line");
            let head = c_lines.get(line - 1).expect("inside the file");
            assert!(head.contains(&format!("{name}(")), "{line}: {head}\n{c}");
            let comment = format!("// {name} @ ");
            assert!(
                c_lines
                    .get(line - 2)
                    .is_some_and(|l| l.starts_with(&comment))
            );
            assert!(
                v["entry"].as_str().is_some_and(|e| e.starts_with("0x")),
                "{row}"
            );
            names.push(name);
        }
        assert_eq!(names, ["sub_1000", "sub_1010"]);
    }

    /// An export without `--records` leaves an older records file as it
    /// was, and its content check no longer matches the new C file.
    ///
    /// # Panics
    ///
    /// When the stale file was removed or still matches.
    #[test]
    #[expect(clippy::disallowed_methods, reason = "a temp dir this test made")]
    fn a_records_file_from_another_export_no_longer_matches() {
        let p = pair();
        let mut a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-stale-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let out = dir.join("o.c").display().to_string();
        let mut o = Overlay::default();
        let with = (Library::Include, Records::Write);
        write_entries(&p, &mut a, &o, with, None, &out, Existing::Replace).expect("writes");
        o.names.insert(0x1000, "renamed".to_owned());
        let without = (Library::Include, Records::Skip);
        write_entries(&p, &mut a, &o, without, None, &out, Existing::Replace).expect("writes");
        let c = std::fs::read(&out).expect("the C file");
        let records = std::fs::read_to_string(path_beside(&out)).expect("the old records");
        std::fs::remove_dir_all(&dir).expect("cleans up");
        let first: serde_json::Value =
            serde_json::from_str(records.lines().next().unwrap_or_default()).expect("JSON");
        let mut content = Content::default();
        content.add(&c);
        let fnv = format!("{:016x}", content.fnv);
        assert_ne!(first["c_fnv1a64"].as_str(), Some(fnv.as_str()));
    }

    /// A part line without its head line, with no number before the tab,
    /// or with no JSON object after it is an error, never a dropped row.
    ///
    /// # Panics
    ///
    /// When a malformed row is taken.
    #[test]
    fn a_malformed_part_line_is_an_error() {
        assert!(placed(r#"{"name":"f"}"#, 3).is_err());
        assert!(placed(r#"x	{"name":"f"}"#, 3).is_err());
        assert!(placed("4\t[1]", 3).is_err());
        let v = placed("4\t{\"name\":\"f\"}", 3).expect("a row");
        assert_eq!(v["line"], 8);
    }
}
