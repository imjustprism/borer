//! The text passes a decompile runs, by name, and a set of them to leave out.
//!
//! Every rewrite of the text after the emitter (the cleanup passes run to a
//! fixpoint, the folds after them, the field names, the polish and the
//! finishing declarations) is one [`Pass`], listed in [`Pass::ALL`] in the
//! order the pipeline first runs it. [`Passes`] is a set of passes left
//! out, carried by [`super::super::Overlay::passes`] so a text built without
//! some passes is memoized apart from the full one. The full pipeline
//! leaves nothing out; a bisection over the list
//! ([`crate::analysis::render::bisect_iso`]) leaves out a suffix of it to
//! find the first pass whose text the ISO check rejects.

/// One text pass of the decompile pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Pass {
    /// Drops the values a function returning nothing returns.
    DropReturnedValues,
    /// Chains duplicate spills.
    MergeChains,
    /// Folds a temporary that copies a value into its one read.
    FoldTempCopies,
    /// Merges an assignment into the `return` that reads it.
    MergeReturnAssignments,
    /// Drops a `goto` whose label follows it.
    DropFallthroughGotos,
    /// Drops labels no `goto` names, and blank lines.
    UnnamedLabels,
    /// Flattens `else { if ... }` into `else if`.
    FlattenElseIf,
    /// Writes an `if` around one `goto` on one line.
    CollapseLoneGotos,
    /// Moves a statement both arms end with after the `if`.
    HoistCommonTails,
    /// Sends a jump to a jump to that jump's label.
    ThreadJumps,
    /// Orders a pair of jumps as the test before their label.
    FlipJumpPairs,
    /// Writes a jump out of a loop as `break`.
    LoopExits,
    /// Writes a conditional `goto` over a label-free run as an `if`.
    FoldConditionalGotos,
    /// Turns a long `if` that never falls out into an early exit.
    FlattenEarlyExits,
    /// Absorbs an `else` arm after an arm that never falls out.
    AbsorbElse,
    /// Folds an unordered float compare and its parity test.
    FoldUnorderedCompares,
    /// Drops assignments nothing reads.
    DropDeadAssignments,
    /// Reads a byte-scanning loop as `strlen`.
    StrlenLoops,
    /// Folds a conditional `goto` over a run whose labels stay inside it.
    FoldContainedGotos,
    /// Copies a short returning tail to the jumps that reach it.
    InlineTerminalTails,
    /// Moves a block one `goto` reaches to that `goto`.
    MoveSingleUseBlocks,
    /// Drops text after a transfer that no label enters.
    UnreachableRuns,
    /// Reads inverted and counted loops as `while` and `for`.
    RecoverLoops,
    /// Folds the stack canary's check.
    Canary,
    /// Folds rust's overflow and bounds checks.
    PanicChecks,
    /// Drops the writes of a result register no one reads.
    DropDeadResults,
    /// Spells constants by the members of the tables they are compared with.
    ApplyEnums,
    /// Binds call results to their groups.
    ApplyResults,
    /// Renames globals and pointers by the types a user applied.
    RenameTyped,
    /// Spells constants by the enums a user applied.
    UserEnums,
    /// Names the fields of class-typed objects.
    NameFields,
    /// Names the fields of the function's own object.
    NameOwnFields,
    /// Writes the source file a function cites.
    SourceFile,
    /// Reads a stream class's calls as a wire format.
    WireFormat,
    /// Splits a register into one variable per web.
    SplitWebs,
    /// Applies the layouts of the pointers the text indexes.
    ApplyLayouts,
    /// Types a float register by the lanes it is read as.
    FloatLanes,
    /// Types locals by the lanes they hold.
    LaneLocals,
    /// Types the parameters.
    TypeParameters,
    /// Types the locals.
    TypeLocals,
    /// Undoes the byte arithmetic the types scale.
    ByteArithmetic,
    /// Names variables by the evidence of their uses.
    NameVars,
    /// Renumbers temporaries.
    NormalizeTemps,
    /// Drops the `!= 0` of a test that reads a truth value.
    QuietZeroTests,
    /// Drops an assignment an `if` block repeats.
    DropRepeatedAssignments,
    /// Writes `x = x op y` as `x op= y`.
    CompoundAssign,
    /// Writes `x != 0 ? x : y` as `x ?: y`.
    Elvis,
    /// Writes pointer arithmetic as indexing.
    SpellIndex,
    /// Spells the function's own enum constants.
    SpellOwnEnum,
    /// Writes a pointer compared with zero against `nullptr`.
    SpellNullptr,
    /// Reads runs of constant stores that spell a string as a copy of it.
    StoreStrings,
    /// Writes stack buffers as arrays.
    StackArrays,
    /// Calls through a pointer as a function pointer.
    CallablePointers,
    /// Reads a float stored as bits as a float.
    FloatBitReads,
    /// Folds the jumps the typing passes leave foldable.
    RefoldJumps,
    /// Spells float relations as C operators.
    SpellFloatRelations,
    /// Writes the read-only tables the text indexes.
    InlineTables,
    /// Declares the functions and function tables the text uses
    /// ([`super::unit::close`]).
    UnitClosure,
    /// Declares the vector variables.
    VectorDeclare,
    /// Defines the helpers the text calls.
    HelperDeclare,
    /// Defines the structs and declares the tables the text names
    /// ([`super::defs::declare`]).
    TypeDeclare,
}

impl Pass {
    /// Every pass, in the order the pipeline first runs it.
    pub const ALL: [Self; 61] = [
        Self::DropReturnedValues,
        Self::MergeChains,
        Self::FoldTempCopies,
        Self::MergeReturnAssignments,
        Self::DropFallthroughGotos,
        Self::UnnamedLabels,
        Self::FlattenElseIf,
        Self::CollapseLoneGotos,
        Self::HoistCommonTails,
        Self::ThreadJumps,
        Self::FlipJumpPairs,
        Self::LoopExits,
        Self::FoldConditionalGotos,
        Self::FlattenEarlyExits,
        Self::AbsorbElse,
        Self::FoldUnorderedCompares,
        Self::DropDeadAssignments,
        Self::StrlenLoops,
        Self::FoldContainedGotos,
        Self::InlineTerminalTails,
        Self::MoveSingleUseBlocks,
        Self::UnreachableRuns,
        Self::RecoverLoops,
        Self::Canary,
        Self::PanicChecks,
        Self::DropDeadResults,
        Self::ApplyEnums,
        Self::ApplyResults,
        Self::RenameTyped,
        Self::UserEnums,
        Self::NameFields,
        Self::NameOwnFields,
        Self::SourceFile,
        Self::WireFormat,
        Self::SplitWebs,
        Self::ApplyLayouts,
        Self::FloatLanes,
        Self::LaneLocals,
        Self::TypeParameters,
        Self::TypeLocals,
        Self::ByteArithmetic,
        Self::NameVars,
        Self::NormalizeTemps,
        Self::QuietZeroTests,
        Self::DropRepeatedAssignments,
        Self::CompoundAssign,
        Self::Elvis,
        Self::SpellIndex,
        Self::SpellOwnEnum,
        Self::SpellNullptr,
        Self::StoreStrings,
        Self::StackArrays,
        Self::CallablePointers,
        Self::FloatBitReads,
        Self::RefoldJumps,
        Self::SpellFloatRelations,
        Self::InlineTables,
        Self::UnitClosure,
        Self::VectorDeclare,
        Self::HelperDeclare,
        Self::TypeDeclare,
    ];

    /// The pass's name: the function that runs it.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::DropReturnedValues => "drop_returned_values",
            Self::MergeChains => "merge_chains",
            Self::FoldTempCopies => "fold_temp_copies",
            Self::MergeReturnAssignments => "merge_return_assignments",
            Self::DropFallthroughGotos => "drop_fallthrough_gotos",
            Self::UnnamedLabels => "unnamed labels",
            Self::FlattenElseIf => "flatten_else_if",
            Self::CollapseLoneGotos => "collapse_lone_gotos",
            Self::HoistCommonTails => "hoist_common_tails",
            Self::ThreadJumps => "thread_jumps",
            Self::FlipJumpPairs => "flip_jump_pairs",
            Self::LoopExits => "loop_exits",
            Self::FoldConditionalGotos => "fold_conditional_gotos",
            Self::FlattenEarlyExits => "flatten_early_exits",
            Self::AbsorbElse => "absorb_else",
            Self::FoldUnorderedCompares => "fold_unordered_compares",
            Self::DropDeadAssignments => "drop_dead_assignments",
            Self::StrlenLoops => "strlen_loops",
            Self::FoldContainedGotos => "fold_conditional_gotos (contained)",
            Self::InlineTerminalTails => "inline_terminal_tails",
            Self::MoveSingleUseBlocks => "move_single_use_blocks",
            Self::UnreachableRuns => "unreachable runs",
            Self::RecoverLoops => "recover_loops",
            Self::Canary => "canary::fold",
            Self::PanicChecks => "panics::fold_checks",
            Self::DropDeadResults => "drop_dead_results",
            Self::ApplyEnums => "apply_enums",
            Self::ApplyResults => "apply_results",
            Self::RenameTyped => "rename_typed",
            Self::UserEnums => "apply_user_enums",
            Self::NameFields => "name_fields",
            Self::NameOwnFields => "name_own_fields",
            Self::SourceFile => "source_file",
            Self::WireFormat => "wire_format",
            Self::SplitWebs => "split_webs",
            Self::ApplyLayouts => "apply_layouts",
            Self::FloatLanes => "float_lanes",
            Self::LaneLocals => "lane_locals",
            Self::TypeParameters => "type_parameters",
            Self::TypeLocals => "type_locals",
            Self::ByteArithmetic => "byte_arithmetic",
            Self::NameVars => "name_vars",
            Self::NormalizeTemps => "normalize_temps",
            Self::QuietZeroTests => "quiet_zero_tests",
            Self::DropRepeatedAssignments => "drop_repeated_assignments",
            Self::CompoundAssign => "compound_assign",
            Self::Elvis => "elvis",
            Self::SpellIndex => "spell_index",
            Self::SpellOwnEnum => "spell_own_enum",
            Self::SpellNullptr => "spell_nullptr",
            Self::StoreStrings => "store_strings",
            Self::StackArrays => "stack_arrays",
            Self::CallablePointers => "callable_pointers",
            Self::FloatBitReads => "float_bit_reads",
            Self::RefoldJumps => "refold_jumps",
            Self::SpellFloatRelations => "spell_float_relations",
            Self::InlineTables => "inline_tables",
            Self::UnitClosure => "unit::close",
            Self::VectorDeclare => "vector::declare",
            Self::HelperDeclare => "helper::declare",
            Self::TypeDeclare => "defs::declare",
        }
    }

    /// The pass's bit in a [`Passes`] set: its position in [`Pass::ALL`].
    fn bit(self) -> u64 {
        Self::ALL
            .iter()
            .position(|p| *p == self)
            .and_then(|k| u32::try_from(k).ok())
            .and_then(|k| 1u64.checked_shl(k))
            .unwrap_or(0)
    }
}

/// A set of passes a decompile leaves out; empty for the full pipeline.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct Passes(u64);

impl Passes {
    /// Leaves nothing out: the full pipeline.
    pub const NONE: Self = Self(0);

    /// Tells whether the set is empty.
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The set's bits, one per [`Pass`], for a fingerprint.
    #[must_use]
    pub const fn bits(self) -> u64 {
        self.0
    }

    /// The set with one more pass left out.
    ///
    /// # Arguments
    ///
    /// * `pass` - The pass to leave out.
    ///
    /// # Returns
    ///
    /// The set with `pass` in it.
    #[must_use]
    pub fn without(self, pass: Pass) -> Self {
        Self(self.0 | pass.bit())
    }

    /// Leaves out every pass of [`Pass::ALL`] from position `k` on, so the
    /// first `k` run.
    ///
    /// # Arguments
    ///
    /// * `k` - How many passes, from the start of [`Pass::ALL`], run.
    ///
    /// # Returns
    ///
    /// The set of the rest.
    #[must_use]
    pub fn after(k: usize) -> Self {
        Pass::ALL
            .iter()
            .skip(k)
            .fold(Self::NONE, |s, p| s.without(*p))
    }

    /// Tells whether a pass runs: it is not left out.
    ///
    /// # Arguments
    ///
    /// * `pass` - The pass.
    #[must_use]
    pub fn runs(self, pass: Pass) -> bool {
        self.0 & pass.bit() == 0
    }

    /// Runs a rewrite of a text when its pass is not left out.
    ///
    /// # Arguments
    ///
    /// * `pass` - The rewrite's pass.
    /// * `text` - The text.
    /// * `rewrite` - The rewrite.
    ///
    /// # Returns
    ///
    /// The rewritten text, or the text as it was when the pass is left out.
    pub fn apply(self, pass: Pass, text: String, rewrite: impl FnOnce(&str) -> String) -> String {
        if self.runs(pass) {
            rewrite(&text)
        } else {
            text
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Pass, Passes};

    /// Every pass is listed once in [`Pass::ALL`] and fits a set's bits.
    ///
    /// # Panics
    ///
    /// When a pass repeats, or the list outgrows a set.
    #[test]
    fn every_pass_is_listed_once() {
        let mut seen = Passes::NONE;
        for p in Pass::ALL {
            assert!(seen.runs(p), "{} is listed twice", p.name());
            seen = seen.without(p);
        }
        assert!(Pass::ALL.len() <= 64);
        assert_eq!(Passes::after(0), seen);
        assert!(Passes::after(Pass::ALL.len()).is_empty());
    }
}
