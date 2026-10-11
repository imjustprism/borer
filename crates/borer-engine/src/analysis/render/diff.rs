//! Build-to-build comparison: fingerprints, program and function diffs, and
//! names carried to another build.

use super::*;

/// Most functions listed per diff section before the rest are summarized.
pub(super) const DIFF_LIST_MAX: usize = 200;

/// A function's identity for diffing, free of where it sits.
///
/// The name (when known), the address-independent body fingerprint
/// ([`Function::body_hash`]) and the shape fingerprint
/// ([`Function::shape_hash`]), with the entry only for labelling. Built from an
/// analysis or read back from a saved manifest, so a new build can be diffed
/// against a fingerprint sidecar of the old one without the old binary.
#[derive(Debug, Clone)]
pub struct FuncPrint {
    /// The function's name, when it has one.
    pub name: Option<String>,
    /// Address-independent fingerprint of the body.
    pub body: u64,
    /// Fingerprint of the instruction shape alone.
    pub shape: u64,
    /// Entry address, for labelling only.
    pub entry: u64,
}

impl From<&Function> for FuncPrint {
    fn from(f: &Function) -> Self {
        Self {
            name: f.name.clone(),
            body: f.body_hash,
            shape: f.shape_hash,
            entry: f.entry,
        }
    }
}

/// The fingerprint of every function in an analysis, in its order.
#[must_use]
pub fn prints_of(a: &Analysis) -> Vec<FuncPrint> {
    a.functions.iter().map(FuncPrint::from).collect()
}

/// Renders the fingerprint manifest of a binary, one line per function.
///
/// Saved next to a build, it is the sidecar a later diff reads to tell what an
/// update changed from the new file alone: `entry`, body and shape
/// fingerprints, and the name, tab-separated.
///
/// # Arguments
///
/// * `a` - The analysis to fingerprint.
///
/// # Returns
///
/// The manifest text.
#[must_use]
pub fn fingerprint_tsv(a: &Analysis) -> String {
    let mut out = format!(
        "# borer fingerprint v1\n# {} functions\n",
        a.functions.len()
    );
    out.push_str("# entry\tbody\tshape\tname\n");
    for f in &a.functions {
        let _ = writeln!(
            out,
            "{:#x}\t{:016x}\t{:016x}\t{}",
            f.entry,
            f.body_hash,
            f.shape_hash,
            f.name.as_deref().unwrap_or("")
        );
    }
    out
}

/// The manifest's identity and size, without the manifest.
///
/// The full manifest is one line per function: on a ninety-thousand function client that is
/// six megabytes, which is a file to put beside a build and not an answer to read. Handed to
/// a reader whose context it fills, it is six megabytes saying nothing a digest does not.
///
/// So the answer is the digest and the counts, and the file is written by the command that
/// exists to write files. Two builds whose digests agree carry the same functions with the
/// same bodies, which is the question the manifest is usually opened to settle. The digest
/// is FNV-1a over the fields the manifest carries, in the order it carries them, so it moves
/// exactly when a line of the manifest would.
///
/// # Arguments
///
/// * `a` - The analysis.
///
/// # Returns
///
/// The version and digest line, the counts, and where the manifest itself comes from.
pub fn fingerprint_digest(a: &Analysis) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut fold = |v: u64| {
        for b in v.to_le_bytes() {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x1000_0000_01b3);
        }
    };
    let mut named = 0usize;
    for f in &a.functions {
        fold(f.entry);
        fold(f.body_hash);
        fold(f.shape_hash);
        if f.name.is_some() {
            named += 1;
        }
    }
    let mut out = format!("# borer fingerprint v1 digest {h:016x}\n");
    let _ = writeln!(out, "# {} functions, {named} named", a.functions.len());
    out.push_str("# the manifest is a sidecar file rather than an answer: `borer fingerprint <binary> <out>` writes it, and borer://diff/<that path> reads it\n");
    out
}

/// Parses a fingerprint manifest produced by [`fingerprint_tsv`].
///
/// Comment and blank lines are skipped; a line needs at least the entry, body
/// and shape columns, with the name optional.
///
/// # Arguments
///
/// * `text` - The manifest text.
///
/// # Returns
///
/// The fingerprints it holds, in file order.
#[must_use]
pub fn parse_prints(text: &str) -> Vec<FuncPrint> {
    let mut out = Vec::new();
    for line in text.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let mut cols = line.split('\t');
        let (Some(e), Some(b), Some(s)) = (cols.next(), cols.next(), cols.next()) else {
            continue;
        };
        let entry = e
            .trim()
            .strip_prefix("0x")
            .and_then(|h| u64::from_str_radix(h, 16).ok())
            .unwrap_or(0);
        let (Ok(body), Ok(shape)) = (
            u64::from_str_radix(b.trim(), 16),
            u64::from_str_radix(s.trim(), 16),
        ) else {
            continue;
        };
        let name = cols.next().unwrap_or("").trim();
        out.push(FuncPrint {
            name: (!name.is_empty()).then(|| name.to_owned()),
            body,
            shape,
            entry,
        });
    }
    out
}

/// One version's fingerprints indexed by name, body and shape, for pairing
/// the other version's against.
pub(super) struct PrintIndex<'a> {
    /// The first function of each name.
    by_name: BTreeMap<&'a str, usize>,
    /// The functions of each body fingerprint.
    by_body: BTreeMap<u64, Vec<usize>>,
    /// The functions of each shape fingerprint.
    by_shape: BTreeMap<u64, Vec<usize>>,
}

/// A pairing of a baseline function with one of the other version's.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Match {
    /// Index of the counterpart in the other version's fingerprints.
    pub(super) index: usize,
    /// Whether the two bodies are identical.
    pub(super) identical: bool,
    /// How the pair was made, as the report says it.
    pub(super) why: &'static str,
}

impl<'a> PrintIndex<'a> {
    /// Indexes one version's fingerprints.
    ///
    /// # Arguments
    ///
    /// * `fs` - The fingerprints, in the version's order.
    pub(super) fn new(fs: &'a [FuncPrint]) -> Self {
        let mut by_name: BTreeMap<&str, usize> = BTreeMap::new();
        let mut by_body: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
        let mut by_shape: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
        for (i, f) in fs.iter().enumerate() {
            if let Some(n) = &f.name {
                by_name.entry(n.as_str()).or_insert(i);
            }
            by_body.entry(f.body).or_default().push(i);
            by_shape.entry(f.shape).or_default().push(i);
        }
        Self {
            by_name,
            by_body,
            by_shape,
        }
    }

    /// Finds the unused function that best matches `old_f`.
    ///
    /// Most specific first: same name, then an identical body (moved but
    /// unchanged), then a lone matching shape (the body differs only in
    /// constants or registers).
    ///
    /// # Arguments
    ///
    /// * `old_f` - The baseline fingerprint to match.
    /// * `new` - The fingerprints this indexes.
    /// * `taken` - Which of them are already paired.
    ///
    /// # Returns
    ///
    /// The match, or `None` when nothing is left.
    pub(super) fn matching(
        &self,
        old_f: &FuncPrint,
        new: &[FuncPrint],
        taken: &[bool],
    ) -> Option<Match> {
        if let Some(n) = &old_f.name
            && let Some(&i) = self.by_name.get(n.as_str())
            && !taken[i]
        {
            return Some(Match {
                index: i,
                identical: new[i].body == old_f.body,
                why: "by name",
            });
        }
        if let Some(i) = self
            .by_body
            .get(&old_f.body)
            .and_then(|v| v.iter().copied().find(|&i| !taken[i]))
        {
            return Some(Match {
                index: i,
                identical: true,
                why: "identical body",
            });
        }
        let free: Vec<usize> = self
            .by_shape
            .get(&old_f.shape)
            .map(|v| v.iter().copied().filter(|&i| !taken[i]).collect())
            .unwrap_or_default();
        if let [i] = free.as_slice() {
            return Some(Match {
                index: *i,
                identical: false,
                why: "same shape, body differs",
            });
        }
        None
    }
}

/// A readable label for a function: its name, or `sub_<addr>` when unnamed.
///
/// # Arguments
///
/// * `f` - The fingerprint.
pub(super) fn fn_label(f: &FuncPrint) -> String {
    f.name
        .clone()
        .unwrap_or_else(|| format!("sub_{:x}", f.entry))
}

/// One function that changed between two versions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Changed {
    /// Its label in the baseline.
    pub(super) old: String,
    /// Its label in the other version.
    pub(super) new: String,
    /// How the two were paired.
    pub(super) why: &'static str,
}

/// Compares two versions of a binary and reports what changed between them.
///
/// An update ships a new build; most of it is the old code moved to new
/// addresses, and the point is to find the few functions that actually
/// changed.
///
/// Borer fingerprints each function independently of the addresses and globals
/// it names ([`Function::body_hash`]), so a function that only moved matches
/// exactly and is not noise. Functions are paired across the two versions by
/// name first, then by that body fingerprint (unchanged code, even relocated),
/// then by shape alone ([`Function::shape_hash`], a body that differs only in
/// its constants, registers or offsets); what pairs with a different body is a
/// real change, what is left over on one side is added or removed. The result
/// is the update's actual diff, not the fact that everything moved.
///
/// # Arguments
///
/// * `old` - Analysis of the baseline (the loaded binary).
/// * `new` - Analysis of the other version.
/// * `old_name` - A label for the baseline, for the header.
/// * `new_name` - A label for the other version.
///
/// # Returns
///
/// The change report as text.
#[must_use]
pub fn diff_tsv(old: &Analysis, new: &Analysis, old_name: &str, new_name: &str) -> String {
    diff_prints_tsv(&prints_of(old), &prints_of(new), old_name, new_name)
}

/// Compares two versions from their fingerprints, for [`diff_tsv`] and for a
/// diff against a saved manifest ([`parse_prints`]).
///
/// # Arguments
///
/// * `old` / `new` - The two versions' fingerprints.
/// * `old_name` / `new_name` - Labels for the header.
///
/// # Returns
///
/// The change report as text.
#[must_use]
pub fn diff_prints_tsv(
    old: &[FuncPrint],
    new: &[FuncPrint],
    old_name: &str,
    new_name: &str,
) -> String {
    let index = PrintIndex::new(new);
    let mut taken = vec![false; new.len()];
    let mut unchanged = 0usize;
    let mut changed: Vec<Changed> = Vec::new();
    let mut removed: Vec<&FuncPrint> = Vec::new();

    for f in old {
        match index.matching(f, new, &taken) {
            Some(found) => {
                taken[found.index] = true;
                if found.identical {
                    unchanged += 1;
                } else {
                    changed.push(Changed {
                        old: fn_label(f),
                        new: fn_label(&new[found.index]),
                        why: found.why,
                    });
                }
            }
            None => removed.push(f),
        }
    }
    let added: Vec<&FuncPrint> = new
        .iter()
        .enumerate()
        .filter(|(i, _)| !taken[*i])
        .map(|(_, f)| f)
        .collect();

    let mut out = format!("# diff: {old_name} (baseline) vs {new_name}\n");
    let _ = writeln!(out, "# {} functions -> {} functions", old.len(), new.len());
    if changed.is_empty() && added.is_empty() && removed.is_empty() {
        let _ = writeln!(
            out,
            "# identical: every function matched with the same code ({unchanged} functions)"
        );
        return out;
    }
    let _ = writeln!(
        out,
        "# unchanged {unchanged}, changed {}, added {}, removed {}",
        changed.len(),
        added.len(),
        removed.len()
    );
    if !changed.is_empty() {
        out.push_str("# changed (same function, different code):\n");
        for c in changed.iter().take(DIFF_LIST_MAX) {
            if c.old == c.new {
                let _ = writeln!(out, "  {}  ({})", c.old, c.why);
            } else {
                let _ = writeln!(out, "  {} -> {}  ({})", c.old, c.new, c.why);
            }
        }
        elided_line(&mut out, changed.len(), DIFF_LIST_MAX, "");
    }
    if !added.is_empty() {
        let _ = writeln!(out, "# added (only in {new_name}):");
        for f in added.iter().take(DIFF_LIST_MAX) {
            let _ = writeln!(out, "  {}  {:#x}", fn_label(f), f.entry);
        }
        elided_line(&mut out, added.len(), DIFF_LIST_MAX, "");
    }
    if !removed.is_empty() {
        let _ = writeln!(out, "# removed (only in {old_name}):");
        for f in removed.iter().take(DIFF_LIST_MAX) {
            let _ = writeln!(out, "  {}  {:#x}", fn_label(f), f.entry);
        }
        elided_line(&mut out, removed.len(), DIFF_LIST_MAX, "");
    }
    out
}

/// Most lines one side of a per-function diff compares before it is truncated.
pub(super) const DIFF_FN_MAX_LINES: usize = 1500;

/// Unchanged lines kept around a change before a longer run is collapsed.
pub(super) const DIFF_FN_CONTEXT: usize = 3;

/// A baseline function paired with its counterpart in the other version.
pub(super) struct Paired<'a> {
    /// The baseline function's entry.
    pub(super) entry: u64,
    /// The baseline function's fingerprint.
    pub(super) old_print: FuncPrint,
    /// The other version's fingerprints, in its order.
    pub(super) new_prints: Vec<FuncPrint>,
    /// The counterpart.
    pub(super) new: &'a Function,
    /// How the two were paired.
    pub(super) found: Match,
}

/// Pairs a baseline function with its counterpart in the other version, the
/// way the whole-binary diff does.
///
/// # Arguments
///
/// * `old_a` / `old_o` - Analysis and names of the baseline.
/// * `new_a` - The other version's analysis.
/// * `target` - The baseline function, by address or name.
/// * `old_name` / `new_name` - Labels for the two versions.
///
/// # Returns
///
/// The pair.
///
/// # Errors
///
/// The report line to return: the target is not a baseline function, or it
/// has no counterpart.
pub(super) fn pair<'a>(
    old_a: &Analysis,
    old_o: &Overlay,
    new_a: &'a Analysis,
    target: &str,
    old_name: &str,
    new_name: &str,
) -> Result<Paired<'a>, String> {
    let entry = resolve(old_a, old_o, target)
        .ok_or_else(|| format!("# no function {target} in {old_name}\n"))?;
    let old_f = old_a
        .function(entry)
        .ok_or_else(|| format!("# {target} is not a function in {old_name}\n"))?;
    let new_prints = prints_of(new_a);
    let taken = vec![false; new_prints.len()];
    let old_print = FuncPrint::from(old_f);
    let found = PrintIndex::new(&new_prints)
        .matching(&old_print, &new_prints, &taken)
        .ok_or_else(|| {
            format!(
                "# {}: no match in {new_name} (removed, or changed past recognition)\n",
                fn_label(&old_print)
            )
        })?;
    Ok(Paired {
        entry,
        old_print,
        new_prints,
        new: &new_a.functions[found.index],
        found,
    })
}

/// Shows how one function changed between two versions, as a diff of its C.
///
/// Where [`diff_tsv`] lists which functions changed, this shows the change
/// itself: it finds the baseline function (by address or name), pairs it with
/// its counterpart in the other version the same way the whole-binary diff
/// does, decompiles both, and renders a line diff of the pseudo-C, `-` for a
/// line only in the baseline and `+` for one only in the other. Long runs of
/// unchanged lines collapse so the edit stands out.
///
/// # Arguments
///
/// * `old_p` / `old_a` / `old_o` - Image, analysis and names of the baseline.
/// * `new_p` / `new_a` / `new_o` - The other version's image, analysis, names.
/// * `target` - The baseline function, by address or name.
/// * `old_name` / `new_name` - Labels for the two versions.
///
/// # Returns
///
/// The per-function diff as text.
#[must_use]
#[expect(
    clippy::too_many_arguments,
    reason = "two builds, each as image, analysis and names, and the target between them"
)]
pub fn diff_function_tsv(
    old_p: &Program,
    old_a: &Analysis,
    old_o: &Overlay,
    new_p: &Program,
    new_a: &Analysis,
    new_o: &Overlay,
    target: &str,
    old_name: &str,
    new_name: &str,
) -> String {
    let Paired {
        entry,
        old_print,
        new_prints,
        new: new_f,
        found,
    } = match pair(old_a, old_o, new_a, target, old_name, new_name) {
        Ok(paired) => paired,
        Err(report) => return report,
    };
    let mut out = format!(
        "# difffn: {} ({old_name}) vs {} ({new_name})  [{}]\n",
        fn_label(&old_print),
        fn_label(&new_prints[found.index]),
        found.why
    );
    if found.identical {
        out.push_str("# identical body: the code did not change\n");
        return out;
    }
    let (Some(old_c), Some(new_c)) = (
        crate::analysis::decompile::decompile(old_p, old_a, old_o, entry),
        crate::analysis::decompile::decompile(new_p, new_a, new_o, new_f.entry),
    ) else {
        out.push_str("# one side did not decompile; bodies differ\n");
        return out;
    };
    let old_lines: Vec<&str> = old_c.lines().take(DIFF_FN_MAX_LINES).collect();
    let new_lines: Vec<&str> = new_c.lines().take(DIFF_FN_MAX_LINES).collect();
    let diff = line_diff(&old_lines, &new_lines);
    let (adds, dels) = diff
        .iter()
        .fold((0usize, 0usize), |(a, d), (m, _)| match m {
            '+' => (a + 1, d),
            '-' => (a, d + 1),
            _ => (a, d),
        });
    let _ = writeln!(out, "# {dels} line(s) removed, {adds} added");
    render_collapsed(&mut out, &diff);
    out
}

/// A field access aggregated over every base a function reads it through: the
/// widths seen and whether it was read and written.
#[derive(Default, Clone)]
pub(super) struct OffsetUse {
    /// Access widths seen at this offset, in bits.
    pub(super) widths: BTreeSet<u8>,
    /// The offset was loaded from at least once.
    pub(super) read: bool,
    /// The offset was stored to at least once.
    pub(super) write: bool,
}

impl OffsetUse {
    /// The widest access in bytes, `0` when every width was unknown.
    pub(super) fn width(&self) -> u16 {
        self.widths.iter().max().map_or(0, |b| u16::from(*b) / 8)
    }

    /// `r`, `w`, `rw`, or `-` for the direction seen.
    pub(super) fn dir(&self) -> &'static str {
        match (self.read, self.write) {
            (true, true) => "rw",
            (false, true) => "w",
            (true, false) => "r",
            (false, false) => "-",
        }
    }

    /// The `dir/width` cell, e.g. `r/8`.
    pub(super) fn cell(&self) -> String {
        format!("{}/{}", self.dir(), self.width())
    }
}

/// Folds a function's `(base, offset)` accesses down to one row per offset.
///
/// A field offset is the same field whichever register happens to hold the
/// pointer, and register allocation is not stable across builds, so the base is
/// dropped and the widths and directions are unioned by offset.
///
/// # Arguments
///
/// * `sites` - The per-`(base, offset)` accesses.
pub(super) fn offsets_of(
    sites: &BTreeMap<(String, u64), crate::analysis::classes::AccessSite>,
) -> BTreeMap<u64, OffsetUse> {
    let mut out: BTreeMap<u64, OffsetUse> = BTreeMap::new();
    for ((_, off), site) in sites {
        let e = out.entry(*off).or_default();
        e.widths.extend(site.widths.iter().copied());
        e.read |= site.reads > 0;
        e.write |= site.writes > 0;
    }
    out
}

/// One name carried from the baseline to the other build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Carried<'o> {
    /// Where the name was set in the baseline.
    pub(super) old_entry: u64,
    /// Where its function sits in the other build.
    pub(super) new_entry: u64,
    /// The name.
    pub(super) name: &'o str,
    /// How the function was paired, as the report says it.
    pub(super) how: &'static str,
}

/// Carries the names from one build's project to the next build.
///
/// The work of reversing a program is the names, and an update throws the
/// addresses away: every function moved, so a project keyed on addresses is
/// worth nothing against the new build. The functions themselves did not
/// change, and borer fingerprints each one independently of the addresses it
/// mentions, so the pairing that the diff uses to find real changes is
/// exactly the pairing that carries a name across. A body fingerprint is
/// unique enough to pair on only when one function has it, since a build is
/// full of identical one-line thunks, and a name on something that is not a
/// function entry, a global or a string, has no counterpart to pair with.
///
/// Each name is reported with how its function was matched, because the
/// three ways do not deserve equal trust: an identical body is the same
/// function, the same shape is the same function with different constants,
/// and nothing else is a guess this refuses to make. A name the new build
/// already has is left alone, and said so, since overwriting someone's work
/// is worse than reporting a conflict.
///
/// # Arguments
///
/// * `old_a` - Analysis of the build the names belong to.
/// * `old_o` - That build's names.
/// * `new_a` - Analysis of the build to carry them to.
/// * `new_o` - The new build's names, so one already set is not overwritten.
///
/// # Returns
///
/// One row per name that can be carried, with the new address and the
/// evidence, then a count of the ones that cannot.
pub fn carry_names_tsv(
    old_a: &Analysis,
    old_o: &Overlay,
    new_a: &Analysis,
    new_o: &Overlay,
) -> String {
    /// Rows listed before the rest are counted.
    const ROWS_MAX: usize = 400;
    let mut by_body: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    let mut by_shape: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for f in &new_a.functions {
        by_body.entry(f.body_hash).or_default().push(f.entry);
        by_shape.entry(f.shape_hash).or_default().push(f.entry);
    }
    let mut carried: Vec<Carried<'_>> = Vec::new();
    let mut ambiguous = 0usize;
    let mut gone = 0usize;
    for (old_entry, name) in &old_o.names {
        let Some(f) = old_a.function(*old_entry) else {
            gone += 1;
            continue;
        };
        let unique = |index: &BTreeMap<u64, Vec<u64>>, key: u64| -> Option<u64> {
            index.get(&key).filter(|v| v.len() == 1)?.first().copied()
        };
        let paired = unique(&by_body, f.body_hash)
            .map(|e| (e, "the same body"))
            .or_else(|| unique(&by_shape, f.shape_hash).map(|e| (e, "the same shape")));
        match paired {
            Some((new_entry, how)) => carried.push(Carried {
                old_entry: *old_entry,
                new_entry,
                name,
                how,
            }),
            None => {
                if by_body.contains_key(&f.body_hash) || by_shape.contains_key(&f.shape_hash) {
                    ambiguous += 1;
                } else {
                    gone += 1;
                }
            }
        }
    }
    carried.sort_by_key(|c| c.new_entry);
    let mut out = format!(
        "# {} of {} name(s) carry across; {ambiguous} match more than one function, {gone} have no match\n",
        carried.len(),
        old_o.names.len()
    );
    if carried.is_empty() {
        out.push_str(
            "# nothing to carry: annotate the baseline first, then diff against the update\n",
        );
        return out;
    }
    out.push_str("# new address   was           name                          paired by\n");
    for c in carried.iter().take(ROWS_MAX) {
        let note = match new_o.names.get(&c.new_entry) {
            Some(existing) if existing == c.name => "  (already set)",
            Some(_) => "  (conflicts with a name already set)",
            None => "",
        };
        let _ = writeln!(
            out,
            "{:<#14x} {:<#13x} {:<29} {}{note}",
            c.new_entry, c.old_entry, c.name, c.how
        );
    }
    more_line(&mut out, carried.len(), ROWS_MAX, "not listed");
    out.push_str("# apply them with set_name(dry_run=false), then save_project\n");
    out
}

/// Migrates a function's field offsets from one build to another.
///
/// The problem it answers is an SDK's on every game update: a field offset was
/// derived from one engine function on the stamped build, and the new build may
/// have moved it. This finds the anchor function in the baseline, pairs it with
/// its counterpart in the other build the same way the diff does (by name, then
/// by body or shape fingerprint when a stripped build renamed it), reads the
/// field offsets each dereferences, and lines them up: an offset present in both
/// is unchanged, one only in the baseline was removed, one only in the other was
/// added, and when exactly one removed offset and one added offset share a width
/// and direction the field almost certainly moved between them — the answer a
/// byte search for the old displacement can never give.
///
/// # Arguments
///
/// * `old_p` / `old_a` / `old_o` - Image, analysis and names of the baseline.
/// * `new_p` / `new_a` / `new_o` - The other build's image, analysis, names.
/// * `target` - The anchor function, by address or name.
/// * `old_name` / `new_name` - Labels for the two builds.
///
/// # Returns
///
/// The offset migration as text.
#[must_use]
#[expect(
    clippy::too_many_arguments,
    reason = "two builds, each as image, analysis and names, and the target between them"
)]
pub fn migrate_function_tsv(
    old_p: &Program,
    old_a: &Analysis,
    old_o: &Overlay,
    new_p: &Program,
    new_a: &Analysis,
    new_o: &Overlay,
    target: &str,
    old_name: &str,
    new_name: &str,
) -> String {
    let Paired {
        entry,
        old_print,
        new_prints,
        new: new_f,
        found,
    } = match pair(old_a, old_o, new_a, target, old_name, new_name) {
        Ok(paired) => paired,
        Err(report) => return report,
    };
    let (Some(old_sites), Some(new_sites)) = (
        crate::analysis::classes::field_accesses(old_p, old_a, old_o, entry),
        crate::analysis::classes::field_accesses(new_p, new_a, new_o, new_f.entry),
    ) else {
        return format!("# {}: one side did not decompile\n", fn_label(&old_print));
    };
    let old_off = offsets_of(&old_sites);
    let new_off = offsets_of(&new_sites);
    let removed: Vec<u64> = old_off
        .keys()
        .filter(|o| !new_off.contains_key(o))
        .copied()
        .collect();
    let added: Vec<u64> = new_off
        .keys()
        .filter(|o| !old_off.contains_key(o))
        .copied()
        .collect();
    let class = |off: u64, m: &BTreeMap<u64, OffsetUse>| -> (u16, &'static str) {
        m.get(&off).map_or((0, "-"), |u| (u.width(), u.dir()))
    };
    let mut moved_to: BTreeMap<u64, u64> = BTreeMap::new();
    let mut moved_from: BTreeMap<u64, u64> = BTreeMap::new();
    for &r in &removed {
        let rc = class(r, &old_off);
        let cands: Vec<u64> = added
            .iter()
            .copied()
            .filter(|&a| class(a, &new_off) == rc && !moved_to.values().any(|&v| v == a))
            .collect();
        let lone_r = removed
            .iter()
            .filter(|&&x| class(x, &old_off) == rc)
            .count()
            == 1;
        if lone_r && let [a] = cands.as_slice() {
            moved_to.insert(r, *a);
            moved_from.insert(*a, r);
        }
    }
    let mut out = format!(
        "# migrate {} ({old_name}) -> {} ({new_name})  [matched by {}]\n",
        fn_label(&old_print),
        fn_label(&new_prints[found.index]),
        found.why
    );
    let _ = writeln!(
        out,
        "# {} offsets in {old_name}, {} in {new_name}; {} moved",
        old_off.len(),
        new_off.len(),
        moved_to.len()
    );
    let _ = writeln!(out, "offset\told\tnew\tstatus");
    let all: BTreeSet<u64> = old_off.keys().chain(new_off.keys()).copied().collect();
    for off in all {
        let o = old_off.get(&off);
        let n = new_off.get(&off);
        let old_cell = o.map_or_else(|| "-".to_owned(), OffsetUse::cell);
        let new_cell = n.map_or_else(|| "-".to_owned(), OffsetUse::cell);
        let status = match (o.is_some(), n.is_some()) {
            (true, true) => "same".to_owned(),
            (true, false) => moved_to
                .get(&off)
                .map_or_else(|| "removed".to_owned(), |to| format!("moved -> {to:#x}")),
            (false, true) => moved_from
                .get(&off)
                .map_or_else(|| "added".to_owned(), |from| format!("moved <- {from:#x}")),
            (false, false) => continue,
        };
        let _ = writeln!(out, "{off:#x}\t{old_cell}\t{new_cell}\t{status}");
    }
    out
}

/// A line-level diff of `old` to `new` via a longest-common-subsequence walk.
///
/// Returns one entry per line with a marker: `' '` kept, `'-'` only in `old`,
/// `'+'` only in `new`. The subsequence is found with an `O(n*m)` table, which
/// is bounded because the callers cap each side at [`DIFF_FN_MAX_LINES`].
///
/// # Arguments
///
/// * `old` - The baseline lines.
/// * `new` - The other version's lines.
pub(super) fn line_diff(old: &[&str], new: &[&str]) -> Vec<(char, String)> {
    let (n, m) = (old.len(), new.len());
    let mut dp = vec![vec![0u32; m + 1]; n + 1];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            dp[i][j] = if old[i] == new[j] {
                dp[i + 1][j + 1] + 1
            } else {
                dp[i + 1][j].max(dp[i][j + 1])
            };
        }
    }
    let mut out = Vec::new();
    let (mut i, mut j) = (0usize, 0usize);
    while i < n && j < m {
        if old[i] == new[j] {
            out.push((' ', old[i].to_owned()));
            i += 1;
            j += 1;
        } else if dp[i + 1][j] >= dp[i][j + 1] {
            out.push(('-', old[i].to_owned()));
            i += 1;
        } else {
            out.push(('+', new[j].to_owned()));
            j += 1;
        }
    }
    while i < n {
        out.push(('-', old[i].to_owned()));
        i += 1;
    }
    while j < m {
        out.push(('+', new[j].to_owned()));
        j += 1;
    }
    out
}

/// Writes a diff, collapsing runs of unchanged lines longer than twice the
/// context so only the changed regions and their surroundings show.
///
/// # Arguments
///
/// * `out` - The string to append to.
/// * `diff` - The diff from [`line_diff`].
pub(super) fn render_collapsed(out: &mut String, diff: &[(char, String)]) {
    let changed: Vec<bool> = diff.iter().map(|(m, _)| *m != ' ').collect();
    let near_change = |k: usize| {
        let lo = k.saturating_sub(DIFF_FN_CONTEXT);
        let hi = (k + DIFF_FN_CONTEXT + 1).min(diff.len());
        changed[lo..hi].iter().any(|c| *c)
    };
    let mut hidden = 0usize;
    for (k, (marker, line)) in diff.iter().enumerate() {
        if *marker == ' ' && !near_change(k) {
            hidden += 1;
            continue;
        }
        if hidden > 0 {
            let _ = writeln!(out, "       ... {hidden} unchanged");
            hidden = 0;
        }
        let _ = writeln!(out, "  {marker} {line}");
    }
    if hidden > 0 {
        let _ = writeln!(out, "       ... {hidden} unchanged");
    }
}
