//! The oracle the `dogfood` origins sweep holds each line's origin to.
//!
//! It is which block's lifted code spells the line ([`Spelled`]), recorded
//! as the emitter lifted every block, apart from the label above the line.

use std::collections::BTreeMap;

use borer_engine::analysis::decompile::{Origins, Spelled, declarations_end};

/// What the sweep counted over every function.
#[derive(Debug, Default)]
pub(super) struct Tally {
    /// Final body lines that stand for code: not blank, braces alone or a
    /// label.
    pub(super) lines: usize,
    /// Those whose origin is known.
    pub(super) known: usize,
    /// Final lines one block's lifted code spells, which the final body
    /// spells once.
    pub(super) anchors: usize,
    /// Anchors whose known origin is another block, at most ten, each with
    /// its function.
    pub(super) contradictions: Vec<String>,
    /// How many anchors contradict their origin in all.
    pub(super) contradicted: usize,
}

/// Returns the line a function's body starts on: past its header comments
/// and its declarations.
///
/// # Arguments
///
/// * `text` - The function's text.
fn body_start(text: &str) -> usize {
    declarations_end(text)
        .unwrap_or_else(|| text.lines().take_while(|l| l.starts_with("//")).count())
}

/// Tells whether a trimmed line stands for code: not blank, not braces
/// alone, not a label.
///
/// # Arguments
///
/// * `t` - The line without indentation.
fn stands_for_code(t: &str) -> bool {
    let braces = t.chars().all(|c| matches!(c, '{' | '}' | ';' | ' ')) || t == "} else {";
    let label = t.starts_with("L_") && t.ends_with(':');
    !braces && !label
}

impl Tally {
    /// Holds one function's final text and its origins to the blocks whose
    /// lifted code spells its lines.
    ///
    /// # Arguments
    ///
    /// * `entry` - The function's entry, for the report.
    /// * `text` - The final text.
    /// * `origins` - The block each of its lines stands for.
    /// * `spelled` - Which block's lifted code spells each statement.
    pub(super) fn add(&mut self, entry: u64, text: &str, origins: &Origins, spelled: &Spelled) {
        let lines: Vec<&str> = text.lines().collect();
        let from = body_start(text);
        let mut counted: BTreeMap<&str, usize> = BTreeMap::new();
        for line in lines.iter().skip(from) {
            *counted.entry(line.trim()).or_default() += 1;
        }
        for (i, line) in lines.iter().enumerate().skip(from) {
            let t = line.trim();
            if !stands_for_code(t) {
                continue;
            }
            self.lines += 1;
            let origin = origins.line(i);
            self.known += usize::from(origin.is_some());
            let Some(Some(block)) = spelled.get(t).copied() else {
                continue;
            };
            if counted.get(t) != Some(&1) {
                continue;
            }
            self.anchors += 1;
            if origin.is_some_and(|b| b != block) {
                self.contradicted += 1;
                if self.contradictions.len() < 10 {
                    self.contradictions.push(format!(
                        "{entry:#x} line {}: {t:?} stands for {origin:x?}, spelled by {block:#x}",
                        i + 1
                    ));
                }
            }
        }
    }

    /// Returns the share of the code lines whose origin is known, in
    /// tenths of a percent.
    pub(super) fn coverage(&self) -> usize {
        (self.known * 1000).checked_div(self.lines).unwrap_or(1000)
    }
}
