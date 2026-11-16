//! The answers to the `borer://` resources the engine gives on its own, from
//! a program, its analysis and an overlay.
//!
//! A front end reads a resource by its URI: the MCP server for
//! `resources/read` and its `query` tool, a script's `query(uri)` wherever
//! the engine runs ([`crate::script`]), and the app. Each asks [`need`] what
//! to prepare and [`read`] for the text, so every front end answers a URI
//! with the same bytes. The resources that read what a front end holds (the
//! session and its evidence, a live process, the answer memory, a file the
//! URI names, the packs on disk, the resource catalog) stay with it.

use crate::analysis::{
    Analysis, EnumSource, Overlay, about, attributes, classes, decompile, encode, fieldrefs,
    function_entry, hex_prefixed, map, messages, name_of, objc, opcodes, parse_addr, ports,
    protocol, render, resolve_suggesting, schema, senders, sigs, vtables,
};
use crate::program::{Feature, Program};
use crate::table::Window;
use Feature::{Decompile, Disasm, Discover, Emulate};
use Need::{Best, Code, File};
use Takes::{Argument, Either, Nothing};

/// The refusal of an `about` given no name, the resource's and the CLI's.
pub const ABOUT_NEEDS_A_NAME: &str = "about needs a name: an attribute, a class, or a function";

/// Most rows one listing keyed by a vtable slot, one list of dispatchers
/// or opcode senders, or one list of a function's lookalikes returns.
const SLOT_PAGE: usize = 2000;

/// Most rows one read of a listing that pages itself by a window returns.
const WINDOW_PAGE: usize = 200;

/// Most rows one read of the namespace map or the message ports returns.
const MAP_PAGE: usize = 5000;

/// What a resource reads of the program before it answers, so a front end
/// prepares it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Need {
    /// The file alone, on any architecture; the analysis serves only as a
    /// memo of the file's facts, an empty one as well as any.
    File,
    /// The analysis of a program that does the stage; refused otherwise
    /// with the sentence [`Program::refuses`] gives.
    Code(Feature),
    /// The analysis where the program does the stage, the file alone where
    /// it does not.
    Best(Feature),
}

/// Whether a resource takes an argument after its name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Takes {
    /// Never: `borer://triage`.
    Nothing,
    /// Always: `borer://emulate/<address>`.
    Argument,
    /// Either: `borer://encoded` or `borer://encoded/<filter>`.
    Either,
}

impl Takes {
    /// Tells whether a URI with or without an argument names the resource.
    ///
    /// # Arguments
    ///
    /// * `given` - Whether the URI carries an argument.
    fn fits(self, given: bool) -> bool {
        match self {
            Nothing => !given,
            Argument => given,
            Either => true,
        }
    }
}

/// Who pages a listing a reader asks a page of.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Paged {
    /// [`read`] pages its rows ([`crate::table::page`]).
    Rows,
    /// The renderer pages itself, from the window or the words it is given.
    Itself,
}

/// The page a reader asked of a listing: `!offset=<n>` and `!limit=<n>` on
/// the URI.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Page<'a> {
    /// Rows to skip, when the reader asked.
    pub offset: Option<usize>,
    /// Most rows to show, when the reader asked.
    pub limit: Option<usize>,
    /// The URI the line naming the next page appends its offset to: the
    /// resource and the limit asked for.
    pub again: &'a str,
}

impl<'a> Page<'a> {
    /// The whole of a listing, no page asked.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI read, for the line naming the next page.
    #[must_use]
    pub fn whole(uri: &'a str) -> Page<'a> {
        Page {
            offset: None,
            limit: None,
            again: uri,
        }
    }

    /// Whether a page was asked for.
    #[must_use]
    pub fn paged(&self) -> bool {
        self.offset.is_some() || self.limit.is_some()
    }

    /// The window a listing that pages itself shows: from the offset asked,
    /// at most `page` rows, fewer when the limit asks for fewer.
    ///
    /// # Arguments
    ///
    /// * `page` - The most rows the listing shows in one answer.
    #[must_use]
    pub fn window(&self, page: usize) -> Window<'a> {
        Window {
            skip: self.offset.unwrap_or(0),
            limit: self.limit.map_or(page, |n| n.min(page)),
            again: Some(self.again),
        }
    }

    /// A spec that pages itself by `offset=` and `limit=` words, with the
    /// page asked for added: `borer://iocs` and `borer://calls` read these.
    ///
    /// # Arguments
    ///
    /// * `spec` - The resource's argument, empty for none.
    #[must_use]
    pub fn spec_words(&self, spec: &str) -> String {
        let mut words: Vec<String> = Some(spec.to_owned())
            .filter(|s| !s.is_empty())
            .into_iter()
            .collect();
        words.extend(self.offset.map(|n| format!("offset={n}")));
        words.extend(self.limit.map(|n| format!("limit={n}")));
        words.join(",")
    }
}

/// What one answer reads.
struct Ask<'a> {
    /// The loaded program.
    p: &'a Program,
    /// Its analysis, as [`Need`] asked.
    a: &'a Analysis,
    /// The names, comments and types in force.
    o: &'a Overlay,
    /// The URI's argument, decoded; empty for none.
    arg: &'a str,
    /// The page the reader asked.
    page: Page<'a>,
}

/// Renders one resource; its `Err` is the refusal's message.
type Answerer = fn(&Ask<'_>) -> Result<String, String>;

/// A listing keyed by a vtable slot, as the protocol surfaces render one:
/// program, analysis, overlay, slot, class filter and most rows.
type SlotList = fn(&Program, &Analysis, &Overlay, usize, &str, usize) -> String;

/// A filtered list with a row cap: program, analysis, overlay, filter and
/// most rows.
type Capped = fn(&Program, &Analysis, &Overlay, &str, usize) -> String;

/// A filtered list that pages itself by a window.
type Windowed = fn(&Program, &Analysis, &Overlay, &str, Window<'_>) -> String;

/// One resource the engine answers.
struct Answer {
    /// Its name, the URI's first segment after `borer://`.
    name: &'static str,
    /// Whether it takes an argument.
    takes: Takes,
    /// What it reads of the program.
    need: Need,
    /// Who pages it.
    paged: Paged,
    /// The renderer.
    answer: Answerer,
}

/// Returns a resource whose rows [`read`] pages.
///
/// # Arguments
///
/// * `name` - The resource's name.
/// * `takes` - Whether it takes an argument.
/// * `need` - What it reads of the program.
/// * `answer` - The renderer.
const fn rows(name: &'static str, takes: Takes, need: Need, answer: Answerer) -> Answer {
    Answer {
        name,
        takes,
        need,
        paged: Paged::Rows,
        answer,
    }
}

/// Returns a resource whose renderer pages itself.
///
/// # Arguments
///
/// * `name` - The resource's name.
/// * `takes` - Whether it takes an argument.
/// * `need` - What it reads of the program.
/// * `answer` - The renderer.
const fn itself(name: &'static str, takes: Takes, need: Need, answer: Answerer) -> Answer {
    Answer {
        name,
        takes,
        need,
        paged: Paged::Itself,
        answer,
    }
}

/// Every resource the engine answers.
const ANSWERS: &[Answer] = &[
    rows("triage", Nothing, Best(Decompile), |q| {
        Ok(if q.p.refuses(Decompile).is_some() {
            render::file_triage_tsv(q.p)
        } else {
            render::triage_tsv(q.p, q.a, q.o)
        })
    }),
    rows("capabilities", Nothing, Best(Discover), |q| {
        let a = q.p.refuses(Discover).is_none().then_some(q.a);
        Ok(render::capability_map_tsv(q.p, a))
    }),
    rows("hashes", Nothing, File, |q| {
        let made = || crate::hashing::hashes_tsv(q.p);
        Ok(String::clone(&q.a.derived.get_or_build(
            "file_hashes",
            (),
            made,
        )))
    }),
    rows("children", Nothing, File, |q| {
        let made = || crate::carve::children_tsv(q.p);
        Ok(String::clone(&q.a.derived.get_or_build(
            "file_children",
            (),
            made,
        )))
    }),
    rows("encoded", Either, File, |q| {
        let made = || render::encoded_strings(q.p);
        let found = q.a.derived.get_or_build("file_encoded", (), made);
        Ok(render::encoded_strings_tsv(&found, q.arg))
    }),
    itself("injection", Either, File, |q| {
        crate::strings::injection_tsv(q.p, &q.page.spec_words(q.arg))
    }),
    itself("clr", Either, File, clr_text),
    rows("protection", Nothing, Code(Discover), |q| {
        Ok(render::protection_tsv(q.p, q.a))
    }),
    rows("fingerprint", Nothing, Code(Discover), |q| {
        Ok(render::fingerprint_digest(q.a))
    }),
    itself("objc", Either, Code(Discover), |q| {
        Ok(objc::objc_tsv(
            q.a,
            q.arg.trim(),
            q.page.window(WINDOW_PAGE),
        ))
    }),
    rows("sig", Argument, Code(Discover), |q| {
        let va = resolve_suggesting(q.p, q.a, q.o, q.arg)?;
        render::signature_tsv(q.p, q.a, q.o, va)
    }),
    rows("yara", Argument, Code(Discover), yara_text),
    rows("names", Argument, Code(Discover), |q| {
        Ok(render::names_export(q.p, q.a, q.o, tool(q.arg)?))
    }),
    rows("addr", Argument, Code(Discover), |q| {
        crate::fileinfo::locate(q.p, Some(q.a), q.o, q.arg)
    }),
    rows("shape", Argument, Code(Discover), |q| {
        render::shape_siblings_tsv(q.p, q.a, q.o, entry(q, q.arg)?, SLOT_PAGE)
            .ok_or_else(|| format!("no function at {}", q.arg))
    }),
    rows("patch", Argument, Code(Disasm), |q| {
        crate::patch::plan_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("emulate", Argument, Code(Emulate), |q| {
        render::emulate_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("oracle", Argument, Code(Emulate), |q| {
        render::oracle_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("run", Argument, Code(Emulate), |q| {
        render::run_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("diverge", Argument, Code(Emulate), |q| {
        render::run_diff_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("vectors", Argument, Code(Emulate), |q| {
        render::vectors_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("blame", Argument, Code(Emulate), |q| {
        render::blame_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("certify", Argument, Code(Emulate), |q| {
        render::certify_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("solve", Argument, Code(Emulate), |q| {
        render::solve_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("devirt", Argument, Code(Emulate), |q| {
        render::devirtualize_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("unpack", Argument, Code(Emulate), |q| {
        render::unpack_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("hidden", Either, Code(Emulate), |q| {
        Ok(render::hidden_strings_tsv(q.p, q.a, q.o, q.arg))
    }),
    itself("decoded", Either, Code(Emulate), |q| {
        render::decoded_tsv(q.p, q.a, q.o, &q.page.spec_words(q.arg))
    }),
    rows("enums", Nothing, Code(Decompile), |q| Ok(enums_text(q))),
    rows("dynimports", Nothing, Code(Decompile), |q| {
        Ok(render::dynamic_imports_tsv(q.p, q.a, q.o))
    }),
    rows("checks", Nothing, Code(Decompile), |q| {
        Ok(render::license_checks_tsv(q.p, q.a, q.o))
    }),
    rows("antianalysis", Nothing, Code(Decompile), |q| {
        Ok(render::anti_analysis_tsv(q.p, q.a, q.o))
    }),
    rows("qt", Nothing, Code(Decompile), |q| Ok(render::qt_tsv(q.a))),
    itself("iocs", Either, Code(Decompile), |q| {
        render::iocs_tsv(q.p, q.a, q.o, &q.page.spec_words(q.arg))
    }),
    itself("calls", Argument, Code(Decompile), |q| {
        render::calls_tsv(q.p, q.a, q.o, &q.page.spec_words(q.arg))
    }),
    rows("stackstrings", Either, Code(Decompile), |q| {
        Ok(render::stack_strings_tsv(q.p, q.a, q.o, q.arg))
    }),
    rows("taint", Argument, Code(Decompile), |q| {
        render::taint_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("layout", Argument, Code(Decompile), layout_text),
    rows("why", Argument, Code(Decompile), |q| {
        render::why_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("partial", Argument, Code(Decompile), |q| {
        render::partial_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("flat", Either, Code(Decompile), |q| {
        render::flattening_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("vm", Either, Code(Decompile), |q| {
        render::vm_dispatch_tsv(q.p, q.a, q.o, q.arg)
    }),
    rows("asserts", Either, Code(Decompile), |q| {
        Ok(render::asserted_fields_tsv(q.p, q.a, q.o, q.arg))
    }),
    rows("sources", Either, Code(Decompile), |q| {
        Ok(render::source_tree_tsv(q.p, q.a, q.arg))
    }),
    rows("classes", Either, Code(Decompile), |q| {
        Ok(render::class_ids_tsv(q.a, q.arg))
    }),
    rows("singletons", Either, Code(Decompile), |q| {
        Ok(render::singletons_tsv(q.a, q.o, q.arg))
    }),
    rows("fields", Argument, Code(Decompile), |q| {
        classes::fields_tsv(q.p, q.a, q.o, entry(q, q.arg)?)
            .ok_or_else(|| format!("{} did not decompile", q.arg))
    }),
    itself("fieldrefs", Argument, Code(Decompile), fieldrefs_text),
    rows("vslot", Argument, Code(Decompile), |q| {
        let SlotSpec { slot, filter } = SlotSpec::parse(q.arg)?;
        Ok(vtables::slot_constants_tsv(
            q.p, q.a, slot, filter, SLOT_PAGE,
        ))
    }),
    rows("exportpack", Argument, Code(Decompile), |q| {
        let (name, all) = pack_spec(q.arg)?;
        Ok(sigs::export_pack(q.p, q.a, q.o, name, all))
    }),
    rows("scenario", Argument, Code(Decompile), scenario_text),
    rows("scenarios", Argument, Code(Decompile), scenarios_text),
    rows("schema", Argument, Code(Decompile), schema_text),
    rows("encode", Argument, Code(Decompile), encode_text),
    rows("schemas", Argument, Code(Decompile), |q| {
        slotted(q, schema::schemas_tsv)
    }),
    rows("encodes", Argument, Code(Decompile), |q| {
        slotted(q, encode::encodings_tsv)
    }),
    rows("senders", Argument, Code(Decompile), |q| {
        slotted(q, senders::senders_tsv)
    }),
    rows("protocol", Argument, Code(Decompile), |q| {
        slotted(q, protocol::protocol_tsv)
    }),
    rows("hooks", Argument, Code(Decompile), |q| {
        slotted(q, protocol::hooks_tsv)
    }),
    rows("dispatchers", Either, Code(Decompile), |q| {
        Ok(capped(q, opcodes::dispatchers_tsv, SLOT_PAGE))
    }),
    rows("opsends", Either, Code(Decompile), |q| {
        Ok(capped(q, opcodes::sends_tsv, SLOT_PAGE))
    }),
    rows("ports", Either, Code(Decompile), |q| {
        Ok(capped(q, ports::routes_tsv, MAP_PAGE))
    }),
    rows("opcodes", Argument, Code(Decompile), opcodes_text),
    itself("messages", Either, Code(Decompile), |q| {
        Ok(windowed(q, messages::catalog_tsv))
    }),
    itself("attrs", Either, Code(Decompile), |q| {
        Ok(windowed(q, attributes::catalog_tsv))
    }),
    rows("map", Either, Code(Decompile), |q| {
        Ok(map::map_tsv(q.a, q.o, q.arg.trim(), MAP_PAGE))
    }),
    rows("about", Argument, Code(Decompile), |q| {
        Ok(about::about_tsv(q.p, q.a, q.o, q.arg))
    }),
];

/// Lists the names of the resources the engine answers, in no promised
/// order.
pub fn names() -> impl Iterator<Item = &'static str> {
    ANSWERS.iter().map(|r| r.name)
}

/// Splits a `borer://` URI into the resource's name and its argument,
/// percent-decoded once.
///
/// # Arguments
///
/// * `uri` - The URI with its page suffixes taken off.
///
/// # Returns
///
/// The name and the argument, `None` for an argument when the URI has no
/// `/` after the name; `None` when the URI does not start with `borer://`.
#[must_use]
pub fn split(uri: &str) -> Option<(&str, Option<String>)> {
    let path = uri.strip_prefix("borer://")?;
    Some(
        path.split_once('/')
            .map_or((path, None), |(k, a)| (k, Some(percent_decode(a)))),
    )
}

/// Says what a resource reads of the program before it answers.
///
/// An argument that does not read is refused here, before a front end
/// looks for a loaded program, so the refusal says what is wrong with it
/// whether or not a binary is loaded.
///
/// # Arguments
///
/// * `name` - The resource's name ([`split`]).
/// * `arg` - Its decoded argument, `None` for none.
///
/// # Returns
///
/// What to prepare, `Err` with the refusal when the argument does not read,
/// `None` when the engine does not answer the resource.
#[must_use]
pub fn need(name: &str, arg: Option<&str>) -> Option<Result<Need, String>> {
    let found = find(name, arg.is_some())?;
    let arg = arg.unwrap_or("");
    Some(refused(name, arg).map_or_else(|| Ok(need_of(found, arg)), Err))
}

/// Answers a resource from the program, its analysis and an overlay.
///
/// The analysis is the one [`need`] asked for: computed for a [`Need::Code`]
/// resource, and for a [`Need::Best`] one where the program does the stage;
/// any, an empty one too, elsewhere.
///
/// # Arguments
///
/// * `program` - The loaded program.
/// * `analysis` - Its analysis.
/// * `overlay` - The names, comments and types in force, with the binary's
///   name tables as decompilations read them.
/// * `uri` - The URI with its page suffixes taken off.
/// * `page` - The page asked.
///
/// # Returns
///
/// The text, `Err` with the refusal of an argument the resource cannot
/// answer or a stage the program's architecture lacks, `None` when the
/// engine does not answer the resource.
#[must_use]
pub fn read(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    uri: &str,
    page: Page<'_>,
) -> Option<Result<String, String>> {
    let (name, arg) = split(uri)?;
    let found = find(name, arg.is_some())?;
    let arg = arg.unwrap_or_default();
    if let Some(why) = refused(name, &arg) {
        return Some(Err(why));
    }
    if let Code(stage) = need_of(found, &arg)
        && let Some(why) = program.refuses(stage)
    {
        return Some(Err(why));
    }
    let ask = Ask {
        p: program,
        a: analysis,
        o: overlay,
        arg: &arg,
        page,
    };
    Some((found.answer)(&ask).map(|text| match found.paged {
        Paged::Rows if page.paged() => crate::table::page(
            &text,
            page.offset.unwrap_or(0),
            page.limit.unwrap_or(usize::MAX),
            page.again,
        ),
        Paged::Rows | Paged::Itself => text,
    }))
}

/// Returns the resource a name and the presence of an argument name.
///
/// # Arguments
///
/// * `name` - The resource's name.
/// * `given` - Whether the URI carries an argument.
fn find(name: &str, given: bool) -> Option<&'static Answer> {
    ANSWERS
        .iter()
        .find(|r| r.name == name && r.takes.fits(given))
}

/// Returns what one read of a resource reads.
///
/// That is its own [`Answer::need`], but the analysis where the program
/// does discovery for a `.NET` methods or markers listing, which reads the
/// native callers too.
///
/// # Arguments
///
/// * `found` - The resource.
/// * `arg` - Its argument.
fn need_of(found: &Answer, arg: &str) -> Need {
    if found.name == "clr" && matches!(clr_head(arg).0, "methods" | "markers") {
        return Best(Discover);
    }
    found.need
}

/// Refuses an argument that does not read, before anything is read of the
/// program.
///
/// # Arguments
///
/// * `name` - The resource's name.
/// * `arg` - Its argument, empty for none.
///
/// # Returns
///
/// The refusal, `None` when the argument reads or the resource checks it
/// only against the program.
fn refused(name: &str, arg: &str) -> Option<String> {
    match name {
        "vslot" | "schemas" | "encodes" | "hooks" | "protocol" | "senders" => {
            SlotSpec::parse(arg).err()
        }
        "fieldrefs" => field_offset(arg).err(),
        "exportpack" => pack_spec(arg).err(),
        "scenario" => scenario_spec(arg).err(),
        "scenarios" => scenarios_spec(arg).err(),
        "names" => tool(arg).err(),
        "about" => arg.trim().is_empty().then(|| ABOUT_NEEDS_A_NAME.to_owned()),
        _ => None,
    }
}

/// Returns the entry of the function an argument names: a `0x` address,
/// or a name, or decimal digits, as [`resolve_suggesting`] reads them.
///
/// # Arguments
///
/// * `q` - The read.
/// * `text` - The function as the agent wrote it.
///
/// # Errors
///
/// When the text names nothing, or no function contains the address.
fn entry(q: &Ask<'_>, text: &str) -> Result<u64, String> {
    let va = match parse_addr(text).filter(|_| hex_prefixed(text)) {
        Some(va) => va,
        None => resolve_suggesting(q.p, q.a, q.o, text)?,
    };
    entry_of(q.p, q.a, va, text)
}

/// Returns the entry of the function containing an address an agent
/// wrote, saying how to write hex when bare digits read as decimal miss a
/// function their hex reading would hit.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies the functions.
/// * `va` - The address the text resolved to.
/// * `text` - The text as written.
///
/// # Errors
///
/// As [`function_entry`], with the hint when it applies.
pub fn entry_of(
    program: &Program,
    analysis: &Analysis,
    va: u64,
    text: &str,
) -> Result<u64, String> {
    function_entry(program, analysis, va).map_err(|e| {
        let digits = text.trim();
        let hint = u64::from_str_radix(digits, 16)
            .ok()
            .filter(|hex| {
                digits.bytes().all(|b| b.is_ascii_digit()) && analysis.function_at(*hex).is_some()
            })
            .map_or_else(String::new, |hex| {
                format!("; bare digits are decimal, write {hex:#x} for the hex address")
            });
        format!("{e}{hint}")
    })
}

/// A listing keyed by a vtable slot: `<slot>[,<class-filter>]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SlotSpec<'a> {
    /// The zero-based vtable index.
    slot: usize,
    /// A case-insensitive substring of the class name, empty for every class.
    filter: &'a str,
}

impl<'a> SlotSpec<'a> {
    /// Reads a spec as the URI carries it.
    ///
    /// # Arguments
    ///
    /// * `spec` - The URI argument.
    ///
    /// # Errors
    ///
    /// When the slot is not a number.
    fn parse(spec: &'a str) -> Result<SlotSpec<'a>, String> {
        let (slot_text, filter) = spec.split_once(',').unwrap_or((spec, ""));
        let slot = slot_text.trim().parse().map_err(|_| {
            format!(
                "bad slot {}: a zero-based index",
                crate::text::quoted(slot_text)
            )
        })?;
        Ok(SlotSpec {
            slot,
            filter: filter.trim(),
        })
    }
}

/// Renders a listing keyed by a vtable slot.
///
/// # Arguments
///
/// * `q` - The read, its argument `<slot>[,<class-filter>]`.
/// * `list` - The listing.
///
/// # Errors
///
/// When the slot is not a number.
fn slotted(q: &Ask<'_>, list: SlotList) -> Result<String, String> {
    let SlotSpec { slot, filter } = SlotSpec::parse(q.arg)?;
    Ok(list(q.p, q.a, q.o, slot, filter, SLOT_PAGE))
}

/// Renders a filtered list with a row cap.
///
/// # Arguments
///
/// * `q` - The read, its argument the filter.
/// * `list` - The listing.
/// * `page` - Most rows one read returns.
fn capped(q: &Ask<'_>, list: Capped, page: usize) -> String {
    list(q.p, q.a, q.o, q.arg.trim(), page)
}

/// Renders a filtered list that pages itself by a window of
/// [`WINDOW_PAGE`] rows.
///
/// # Arguments
///
/// * `q` - The read, its argument the filter.
/// * `list` - The listing.
fn windowed(q: &Ask<'_>, list: Windowed) -> String {
    list(q.p, q.a, q.o, q.arg.trim(), q.page.window(WINDOW_PAGE))
}

/// Reads the tool a `borer://names` export is for.
///
/// # Arguments
///
/// * `text` - `ida`, `ghidra`, `binja` or `x64dbg`.
///
/// # Errors
///
/// When the text names none of them.
fn tool(text: &str) -> Result<render::Tool, String> {
    render::Tool::parse(text).ok_or_else(|| {
        format!(
            "unknown tool {}; use one of: {}",
            crate::text::quoted(text),
            render::Tool::NAMES
        )
    })
}

/// Reads a `borer://fieldrefs` offset: the part before any comma.
///
/// # Arguments
///
/// * `spec` - `<offset>[,<name-filter>]`.
///
/// # Errors
///
/// When the offset does not parse ([`fieldrefs::parse_field_offset`]).
fn field_offset(spec: &str) -> Result<i64, String> {
    let offset = spec.split_once(',').map_or(spec, |(o, _)| o);
    fieldrefs::parse_field_offset(offset.trim()).map_err(|e| e.to_string())
}

/// Lists every instruction in the program that touches `[reg + offset]`,
/// each with the function it belongs to, a page of [`WINDOW_PAGE`] sites.
///
/// # Arguments
///
/// * `q` - The read, its argument `<offset>[,<name-filter>]`.
///
/// # Errors
///
/// When the offset does not parse.
fn fieldrefs_text(q: &Ask<'_>) -> Result<String, String> {
    let offset = field_offset(q.arg)?;
    let filter = q.arg.split_once(',').map_or("", |(_, f)| f);
    Ok(fieldrefs::field_refs_tsv(
        q.p,
        q.a,
        q.o,
        offset,
        filter.trim(),
        q.page.window(WINDOW_PAGE),
    ))
}

/// Reads a `borer://exportpack` spec: the pack's name, then `,all` to add
/// the names the analysis recovered to the user's.
///
/// # Arguments
///
/// * `spec` - The URI argument.
///
/// # Errors
///
/// When the name is empty or has a space, or what follows a comma is not
/// `all`: `x,y` named a pack `x,y`.
fn pack_spec(spec: &str) -> Result<(&str, bool), String> {
    let (name, all) = match spec.split_once(',') {
        None => (spec, false),
        Some((name, "all")) => (name, true),
        Some((_, other)) => {
            return Err(format!(
                "after the pack name comes ,all or nothing, not {}",
                crate::text::quoted(other)
            ));
        }
    };
    if name.is_empty() || name.contains(char::is_whitespace) {
        return Err(format!(
            "a pack name is one word, not {}",
            crate::text::quoted(name)
        ));
    }
    Ok((name, all))
}

/// Returns a YARA rule from functions' signatures and the strings they
/// reference ([`render::yara_rule`]).
///
/// # Arguments
///
/// * `q` - The read, its argument functions by name or entry,
///   comma-separated.
///
/// # Errors
///
/// When a function names nothing, or nothing is left to match on.
fn yara_text(q: &Ask<'_>) -> Result<String, String> {
    let entries = q
        .arg
        .split(',')
        .map(str::trim)
        .filter(|f| !f.is_empty())
        .map(|f| resolve_suggesting(q.p, q.a, q.o, f))
        .collect::<Result<Vec<u64>, String>>()?;
    render::yara_rule(q.p, q.a, q.o, &entries)
}

/// Splits a `.NET` listing's spec into its first word and the rest.
///
/// # Arguments
///
/// * `spec` - The spec, its page words added.
fn clr_head(spec: &str) -> (&str, &str) {
    let (head, rest) = spec.split_once([',', '/']).unwrap_or((spec, ""));
    (head.trim(), rest)
}

/// Lists a `.NET` assembly's metadata, or its IL methods or obfuscator
/// markers.
///
/// The metadata is its types, methods, P/Invokes, external members,
/// references and user strings; with `methods` first the IL methods by the
/// APIs they call and the strings they load, with `markers` the markers.
///
/// # Arguments
///
/// * `q` - The read, its argument kinds and texts to keep, comma-separated;
///   or `methods` or `markers` and their words.
///
/// # Errors
///
/// When the metadata was refused or the page does not read.
fn clr_text(q: &Ask<'_>) -> Result<String, String> {
    let spec = q.page.spec_words(q.arg);
    match clr_head(&spec) {
        ("methods", rest) => crate::clr::managed::methods_tsv(q.p, q.a, rest),
        ("markers", rest) => crate::clr::markers::markers_tsv(q.p, q.a, rest),
        _ => crate::clr::clr_tsv(q.p, &spec).map_err(|e| e.to_string()),
    }
}

/// Proposes a structure from a pointer's accesses, or with `apply=Name`
/// plans it as a user struct typing the parameter the pointer arrives in
/// ([`crate::analysis::apply::from_pointer`]).
///
/// A read applies nothing, whatever `dry_run` the spec says: the plan names
/// the `set_type` calls that state it ([`plan_calls`]).
///
/// # Arguments
///
/// * `q` - The read, its argument `<address>[,<register>][,apply=<Name>]`.
///
/// # Errors
///
/// When the spec or the struct to plan is refused.
fn layout_text(q: &Ask<'_>) -> Result<String, String> {
    let mut apply: Option<&str> = None;
    let mut kept: Vec<&str> = Vec::new();
    for part in q.arg.split(',') {
        match part.trim() {
            "dry_run=false" | "dry_run=true" => {}
            t => match t.strip_prefix("apply=") {
                Some(name) => apply = Some(name),
                None => kept.push(part),
            },
        }
    }
    let spec = kept.join(",");
    let Some(name) = apply else {
        return render::layout_tsv(q.p, q.a, q.o, &spec);
    };
    let plan = crate::analysis::apply::from_pointer(q.p, q.a, q.o, &spec, name)?;
    let mut out = format!(
        "plan: struct {} and {} prototype(s), nothing applied by a read; send the set_type calls below and decompile names the fields:\n",
        plan.name,
        plan.prototypes.len()
    );
    for line in plan.describe(q.a, q.o).into_iter().chain(plan_calls(&plan)) {
        out.push_str(&line);
        out.push('\n');
    }
    Ok(out)
}

/// Spells the `set_type` calls that state a layout's plan, ready to send.
///
/// # Arguments
///
/// * `plan` - The plan a `borer://layout/...,apply=<Name>` read made.
///
/// # Returns
///
/// One line per call, `set_type` and its arguments as JSON with
/// `dry_run` false: the struct first, then each prototype.
fn plan_calls(plan: &crate::analysis::apply::Plan) -> Vec<String> {
    let mut calls = Vec::new();
    if let crate::analysis::utypes::UserType::Struct(s) = &plan.ty {
        let fields: Vec<String> = s
            .fields
            .iter()
            .map(|(off, f)| format!("{off:#x}:{}:{}", f.name, f.ty.spell()))
            .collect();
        calls.push(serde_json::json!({
            "name": plan.name, "fields": fields, "size": s.size, "dry_run": false,
        }));
    }
    calls.extend(plan.prototypes.iter().map(|(entry, proto)| {
        serde_json::json!({
            "address": format!("{entry:#x}"), "type": proto.spell(), "dry_run": false,
        })
    }));
    calls.iter().map(|c| format!("set_type {c}")).collect()
}

/// Parameters a scenario fixes: the argument's number and its value.
type Assumed = Vec<(u8, u64)>;

/// Reads a `borer://scenario` spec: the function, then the parameters.
///
/// # Arguments
///
/// * `spec` - `<function>/<a2=5,...>`.
///
/// # Errors
///
/// When the spec lacks the `/` or the parameters do not read.
fn scenario_spec(spec: &str) -> Result<(&str, Assumed), String> {
    let (target, assume) = spec
        .rsplit_once('/')
        .ok_or("borer://scenario/<function>/<a2=5,...>")?;
    Ok((target, decompile::parse_scenario(assume)?))
}

/// Reads a `borer://scenarios` spec: the function, then the values of one
/// parameter.
///
/// # Arguments
///
/// * `spec` - `<function>/<a2=0..32>`.
///
/// # Errors
///
/// When the spec lacks the `/` or the values do not read.
fn scenarios_spec(spec: &str) -> Result<(&str, (u8, Vec<u64>)), String> {
    let (target, values) = spec
        .rsplit_once('/')
        .ok_or("borer://scenarios/<function>/<a2=0..32>")?;
    Ok((target, decompile::parse_explosion(values)?))
}

/// Decompiles a function under a scenario, the CLI's `scenario`.
///
/// # Arguments
///
/// * `q` - The read, its argument `<function>/<a2=5,...>`.
///
/// # Errors
///
/// When the spec does not read, or the function does not decompile.
fn scenario_text(q: &Ask<'_>) -> Result<String, String> {
    let (target, assume) = scenario_spec(q.arg)?;
    let entry = entry(q, target)?;
    decompile::decompile_scenario(q.p, q.a, q.o, entry, &assume)
        .ok_or_else(|| "the function does not decompile".to_owned())
}

/// Runs a scenario for each value of one parameter and groups the ones
/// that behave alike, the CLI's `scenarios`.
///
/// # Arguments
///
/// * `q` - The read, its argument `<function>/<a2=0..32>`.
///
/// # Errors
///
/// When the spec does not read, or the function does not resolve.
fn scenarios_text(q: &Ask<'_>) -> Result<String, String> {
    let (target, (slot, values)) = scenarios_spec(q.arg)?;
    let entry = entry(q, target)?;
    let cases = decompile::explode(q.p, q.a, q.o, entry, slot, &values);
    Ok(decompile::explode_tsv(&cases, slot, values.len()))
}

/// Renders the record a deserializer reads off its stream; a function that
/// reads no stream is an answer, not a fault.
///
/// # Arguments
///
/// * `q` - The read, its argument a function by address or name, or a
///   class name whose reading virtual is picked.
///
/// # Errors
///
/// When the name is neither a function nor a class whose virtuals read a
/// stream.
fn schema_text(q: &Ask<'_>) -> Result<String, String> {
    let Ok(entry) = entry(q, q.arg) else {
        return schema::class_schema_tsv(q.p, q.a, q.o, q.arg).ok_or_else(|| {
            format!(
                "{} is neither a function nor a class whose virtuals read a stream",
                crate::text::quoted(q.arg)
            )
        });
    };
    Ok(schema::schema_tsv(q.p, q.a, q.o, entry).unwrap_or_else(|| {
        format!(
            "# {} hands no stream to its calls: not a deserializer\n",
            name_of(q.a, q.o, entry)
        )
    }))
}

/// Renders what a serializer writes onto its stream; a function that
/// writes no stream is an answer, not a fault.
///
/// # Arguments
///
/// * `q` - The read, its argument a function by address or name, or a
///   class name whose writing virtual is picked.
///
/// # Errors
///
/// When the name is neither a function nor a class whose virtuals write a
/// stream.
fn encode_text(q: &Ask<'_>) -> Result<String, String> {
    let Ok(entry) = entry(q, q.arg) else {
        return encode::class_encoding_tsv(q.p, q.a, q.o, q.arg).ok_or_else(|| {
            format!(
                "{} is neither a function nor a class whose virtuals write a stream",
                crate::text::quoted(q.arg)
            )
        });
    };
    Ok(
        encode::encoding_tsv(q.p, q.a, q.o, entry).unwrap_or_else(|| {
            format!(
                "# {} hands its stream nothing: not a serializer\n",
                name_of(q.a, q.o, entry)
            )
        }),
    )
}

/// Renders one dispatcher's opcodes with their handlers and records; a
/// function that switches on no opcode is an answer, not a fault.
///
/// # Arguments
///
/// * `q` - The read, its argument `<function>[,<filter>]`.
///
/// # Errors
///
/// When the function does not resolve.
fn opcodes_text(q: &Ask<'_>) -> Result<String, String> {
    let (what, filter) = q.arg.split_once(',').unwrap_or((q.arg, ""));
    let entry = entry(q, what.trim())?;
    Ok(
        opcodes::dispatch_tsv(q.p, q.a, q.o, entry, filter.trim(), SLOT_PAGE).unwrap_or_else(
            || {
                format!(
                    "# {} switches on no value read off a stream that its cases read on from: not a dispatcher\n",
                    name_of(q.a, q.o, entry)
                )
            },
        ),
    )
}

/// Lists every name table the binary encodes, one line per function.
///
/// The listing reads every table-shaped function of the binary, under the
/// names as the user left them rather than the binary's tables, so a table
/// is listed under its function's own name.
///
/// # Arguments
///
/// * `q` - The read.
fn enums_text(q: &Ask<'_>) -> String {
    let o = Overlay {
        enum_source: EnumSource::Given,
        ..q.o.clone()
    };
    let tables = decompile::enum_tables(q.p, q.a, &o);
    let mut out = format!("# {} name tables\n", tables.len());
    for (entry, table) in &tables {
        out.push_str(&enum_row(&name_of(q.a, &o, *entry), *entry, table));
    }
    out
}

/// Returns one `borer://enums` row: the function, its entry, `enum` and
/// the table's name, then its members.
///
/// A table named by an enum type is written `enum <type>` once, where the
/// type's own `enum` made it `enum enum <type>`.
///
/// # Arguments
///
/// * `function` - The function's name.
/// * `entry` - Its entry.
/// * `table` - The name table it encodes.
fn enum_row(function: &str, entry: u64, table: &decompile::EnumTable) -> String {
    let members: Vec<String> = table
        .members
        .iter()
        .map(|(k, lit)| format!("{lit} = {k}"))
        .collect();
    let name = match table.name.strip_prefix("enum ").unwrap_or(&table.name) {
        "" => String::new(),
        bare => format!(" {bare}"),
    };
    format!(
        "{function} @ {entry:#x}: enum{name}: {}\n",
        members.join(", ")
    )
}

/// Percent-decodes a resource URI argument.
///
/// A URI carries an argument in a path segment, where `,`, `=` and `:` are
/// reserved, so a correct client may send them escaped: an experiment spec
/// like `0x1400,rax=1` can arrive as `0x1400%2Crax%3D1`. The escaped form is
/// canonical, so decoding it is what makes those URIs resolve. A `%` that
/// does not begin a valid escape is left alone, so a name containing one
/// still resolves, and bytes that are not UTF-8 leave the text as it came.
///
/// # Arguments
///
/// * `text` - The raw path segment.
///
/// # Returns
///
/// The decoded argument.
#[must_use]
pub fn percent_decode(text: &str) -> String {
    if !text.contains('%') {
        return text.to_owned();
    }
    let raw = text.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(raw.len());
    let mut i = 0;
    while i < raw.len() {
        let escape = if raw[i] == b'%' {
            let hex = |k: usize| {
                raw.get(k)
                    .copied()
                    .map(char::from)
                    .and_then(|c| c.to_digit(16))
            };
            hex(i + 1).zip(hex(i + 2))
        } else {
            None
        };
        if let Some((high, low)) = escape {
            out.push(u8::try_from(high * 16 + low).unwrap_or(b'%'));
            i += 3;
        } else {
            out.push(raw[i]);
            i += 1;
        }
    }
    String::from_utf8(out).unwrap_or_else(|_| text.to_owned())
}

#[cfg(test)]
mod tests {
    use super::{Page, decompile, enum_row, need, read};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::Program;

    /// An enum table's row says `enum` once, whether or not the table's
    /// name carries its own.
    ///
    /// # Panics
    ///
    /// When a row repeats `enum` or drops the name.
    #[test]
    fn an_enum_row_says_enum_once() {
        let table = |name: &str| decompile::EnumTable {
            name: name.to_owned(),
            members: vec![(0, "S".to_owned()), (1, "X".to_owned())],
            param: Some(0),
        };
        assert_eq!(
            enum_row("f", 0x10, &table("enum mi_chunkbin_e")),
            "f @ 0x10: enum mi_chunkbin_e: S = 0, X = 1\n"
        );
        assert_eq!(
            enum_row("f", 0x10, &table("")),
            "f @ 0x10: enum: S = 0, X = 1\n"
        );
    }

    /// An argument that does not read is refused before any program is
    /// read, a name the engine does not answer is left to the front end,
    /// and a page asked of a listing is cut from its rows.
    ///
    /// # Panics
    ///
    /// When a refusal, a hand-off or a page differs.
    #[test]
    fn a_resource_is_refused_handed_on_or_paged() {
        assert_eq!(
            need("vslot", Some("x")),
            Some(Err("bad slot 'x': a zero-based index".to_owned()))
        );
        assert_eq!(need("session", None), None);
        assert_eq!(need("triage", Some("x")), None);
        let p = Program::raw_x64(&[0xc3; 0x10]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let uri = "borer://encoded";
        let whole = read(&p, &a, &o, uri, Page::whole(uri));
        let page = Page {
            offset: Some(0),
            limit: Some(1),
            again: uri,
        };
        let paged = read(&p, &a, &o, uri, page).and_then(Result::ok);
        assert!(
            paged.is_some_and(|text| text.starts_with("# showing ")),
            "{whole:?}"
        );
        assert_eq!(
            read(&p, &a, &o, "borer://about/%20", Page::whole(uri)),
            Some(Err(super::ABOUT_NEEDS_A_NAME.to_owned()))
        );
    }
}
