//! The commands that read a wire protocol: the record a decoder reads and
//! an encoder writes per message class, and who sends each.

use anyhow::Context as _;
use borer_engine::analysis::{Analysis, Overlay, encode, protocol, schema, senders};
use borer_engine::program::{Feature, Program};
use borer_engine::text::{one_line, quoted};

use super::args::{SlotQuery, arg, entry_at};
use super::session::Session;

/// A command [`run`] answers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Wire {
    /// `schema <function|class>`: the record a deserializer reads off its stream.
    Schema,
    /// `schemas <slot> [filter] [limit]`: every class with a constant at a slot and the record it decodes.
    Schemas,
    /// `encode <function|class>`: what a serializer writes onto its stream.
    Encode,
    /// `encodes <slot> [filter] [limit]`: every class with a constant at a slot and what it encodes.
    Encodes,
    /// `senders <slot> [filter] [limit]`: every class with a constant at a slot and the functions constructing it.
    Senders,
    /// `protocol <slot> [filter] [limit]`: every class with a constant at a slot with its senders, handler, encoding and decoding.
    Protocol,
    /// `hooks <slot> [filter] [limit]`: every class with a constant at a slot with the addresses a binding hooks.
    Hooks,
}

impl Wire {
    /// Parses a command word.
    ///
    /// # Arguments
    ///
    /// * `word` - The command word.
    ///
    /// # Returns
    ///
    /// The command, or `None` when none of these has that word.
    pub(super) fn parse(word: &str) -> Option<Self> {
        Some(match word {
            "schema" => Self::Schema,
            "schemas" => Self::Schemas,
            "encode" => Self::Encode,
            "encodes" => Self::Encodes,
            "senders" => Self::Senders,
            "protocol" => Self::Protocol,
            "hooks" => Self::Hooks,
            _ => return None,
        })
    }

    /// Returns the most arguments the command reads after the binary.
    pub(super) fn most_args(self) -> usize {
        match self {
            Self::Schema | Self::Encode => 1,
            Self::Schemas | Self::Encodes | Self::Senders | Self::Protocol | Self::Hooks => 3,
        }
    }
}

/// The tables a vtable slot keys: `(program, analysis, overlay, slot,
/// filter, limit)` to the rendered table.
type SlotTable = fn(&Program, &Analysis, &Overlay, usize, &str, usize) -> String;

/// Returns a table keyed by a vtable slot for the arguments `<slot>
/// [filter] [limit]`.
///
/// # Arguments
///
/// * `args` - The command line, the binary at index 1.
/// * `s` - The open session.
/// * `a` - Its analysis.
/// * `missing` - The error when the slot is missing.
/// * `table` - The renderer.
///
/// # Errors
///
/// When the slot is missing or not a number, or the limit is malformed.
fn slot_table(
    args: &[String],
    s: &Session,
    a: &Analysis,
    missing: &'static str,
    table: SlotTable,
) -> anyhow::Result<String> {
    let q = SlotQuery::parse(args, missing)?;
    Ok(table(&s.program, a, &s.overlay, q.slot, q.filter, q.limit))
}

/// Runs one of the wire commands and prints its table.
///
/// # Arguments
///
/// * `cmd` - The command.
/// * `args` - The command line, the binary at index 1.
/// * `s` - The open session.
///
/// # Errors
///
/// When an argument is missing or malformed, or names nothing the command
/// can read.
pub(super) fn run(cmd: Wire, args: &[String], s: &Session) -> anyhow::Result<()> {
    let a = s.analysis(Feature::Decompile)?;
    let (p, o) = (&s.program, &s.overlay);
    let text = match cmd {
        Wire::Schema => {
            let what = arg(
                args,
                2,
                "schema needs a function (address or name) or a class name",
            )?;
            match s.resolve(&a, what) {
                Ok(va) => schema::schema_tsv(p, &a, o, entry_at(p, &a, va)?)
                    .with_context(|| format!("{} hands no stream to its calls", one_line(what)))?,
                Err(_) => schema::class_schema_tsv(p, &a, o, what).with_context(|| {
                    format!(
                        "{} is neither a function nor a class whose virtuals read a stream",
                        quoted(what)
                    )
                })?,
            }
        }
        Wire::Encode => {
            let what = arg(
                args,
                2,
                "encode needs a function (address or name) or a class name",
            )?;
            match s.resolve(&a, what) {
                Ok(va) => encode::encoding_tsv(p, &a, o, entry_at(p, &a, va)?)
                    .with_context(|| format!("{} hands its stream nothing", one_line(what)))?,
                Err(_) => encode::class_encoding_tsv(p, &a, o, what).with_context(|| {
                    format!(
                        "{} is neither a function nor a class whose virtuals write a stream",
                        quoted(what)
                    )
                })?,
            }
        }
        Wire::Schemas => slot_table(
            args,
            s,
            &a,
            "schemas needs the vtable slot the id sits in",
            schema::schemas_tsv,
        )?,
        Wire::Encodes => slot_table(
            args,
            s,
            &a,
            "encodes needs the vtable slot the id sits in",
            encode::encodings_tsv,
        )?,
        Wire::Senders => slot_table(
            args,
            s,
            &a,
            "senders needs the vtable slot the id sits in",
            senders::senders_tsv,
        )?,
        Wire::Protocol => slot_table(
            args,
            s,
            &a,
            "protocol needs the vtable slot the id sits in",
            protocol::protocol_tsv,
        )?,
        Wire::Hooks => slot_table(
            args,
            s,
            &a,
            "hooks needs the vtable slot the id sits in",
            protocol::hooks_tsv,
        )?,
    };
    print!("{text}");
    Ok(())
}
