//! The tools that read bytes: disassembly, typed reads, hex dumps and
//! entropy.

use borer_engine::analysis::{parse_off, render};
use borer_engine::program::Feature;
use borer_engine::{disasm, entropy, hexdump as hexfmt, memory, num};
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::errors::err_params;
use crate::params::{
    DisassembleFunctionParams, DisassembleParams, EntropyParams, HexdumpParams, Page, ReadParams,
    count_param, to_usize,
};
use crate::state::read_lock;

#[tool_router(router = bytes_tools, vis = "pub(crate)")]
impl BorerServer {
    /// Disassembles a run of instructions at an address or name.
    ///
    /// # Arguments
    ///
    /// * `DisassembleParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address does not resolve or is unmapped, or
    /// the architecture has no decoder.
    #[tool(
        description = "Disassemble `count` instructions (default 32, max 256) at an address or name as `va text` rows (bytes=true adds bytes); whole functions: disassemble_function.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn disassemble(
        &self,
        Parameters(DisassembleParams {
            address,
            count,
            bytes,
        }): Parameters<DisassembleParams>,
    ) -> Result<String, ErrorData> {
        let count = count_param(count, 32, 256, "count")?;
        let n = count.n;
        let with_bytes = bytes.unwrap_or(false);
        self.with_program(|p| {
            let asked = self.addr(p, &address)?;
            let isa = p.isa_for(Feature::Disasm)?;
            let a = self.analysis_or_empty();
            let va = render::instruction_at_or_before(p, &a, asked).unwrap_or(asked);
            let snapped = if va == asked {
                String::new()
            } else {
                format!("; {asked:#x} is inside an instruction, listing from {va:#x}")
            };
            let code = p.read_va_upto(va, 16 * 1024).ok_or_else(|| {
                format!(
                    "address {va:#x} is not mapped to file bytes; sections: {}",
                    p.section_list()
                )
            })?;
            let limit = render::sweep_limit(p, &a, va);
            let window = limit
                .and_then(|end| usize::try_from(end - va).ok())
                .and_then(|n| code.get(..n.min(code.len())))
                .unwrap_or(code);
            let lines = disasm::disassemble_program(p, window, va, isa, n);
            let o = self.overlay();
            let ends = limit.map_or(String::new(), |end| {
                format!("; code ends at {end:#x}, what follows is data")
            });
            let caveat = Some(render::listing_caveat(p, &a, va))
                .filter(|c| !c.is_empty())
                .map_or(String::new(), |c| format!("; {c}"));
            let mut out = format!(
                "# {} instructions at {:#x}{snapped}{ends}{caveat}\n",
                lines.len(),
                va
            );
            for l in &lines {
                if let Some(n) = o.names.get(&l.va) {
                    out.push_str(&format!("            ; = {n} =\n"));
                }
                let mut text = l.text.clone();
                if let Some(c) = o.comments.get(&l.va) {
                    text.push_str(&format!("  // {c}"));
                }
                if with_bytes {
                    let mut hexb = String::new();
                    for b in &l.bytes {
                        hexb.push_str(&format!("{b:02x} "));
                    }
                    out.push_str(&format!("{:#x}  {:<24} {text}\n", l.va, hexb.trim_end()));
                } else {
                    out.push_str(&format!("{:#x}  {text}\n", l.va));
                }
            }
            Ok(out)
        })
        .map(|text| count.noted(text))
    }

    /// Disassembles a whole function block by block.
    ///
    /// # Arguments
    ///
    /// * `DisassembleFunctionParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "Disassemble a whole function block by block with `L_<addr>:` labels and named call/jmp targets (max_instrs default 400, max 2000).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn disassemble_function(
        &self,
        Parameters(DisassembleFunctionParams {
            address,
            max_instrs,
            bytes,
        }): Parameters<DisassembleFunctionParams>,
    ) -> Result<String, ErrorData> {
        let max = count_param(max_instrs, 400, 2000, "max_instrs")?;
        self.with_analysis(Feature::Discover, |p, a, o| {
            let entry = self.function_entry(p, a, &address)?;
            render::disasm_function(p, a, o, entry, max.n, bytes.unwrap_or(false))
                .ok_or_else(|| format!("no function at {entry:#x}"))
        })
        .map(|text| max.noted(text))
    }

    /// Reads typed values at an address or name.
    ///
    /// Reading stops at the first address that is not there, and the header
    /// says so: returning fewer values than were asked for without a word
    /// would leave the caller to notice the shortfall by counting rows.
    /// With `type`, a user type is laid over the bytes instead
    /// ([`render::typed_tsv`]): `count` records of it, or as many as the
    /// type's own array states.
    ///
    /// # Arguments
    ///
    /// * `ReadParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// Invalid params for an unknown kind, a type that does not parse, or
    /// both a kind and a type; internal error when the address does not
    /// resolve or the bytes are not mapped.
    #[tool(
        description = "Read `count` values of `kind` (default one u64) as `va value` rows; pointers are named. `type` reads a user type instead: one row per field.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn read(
        &self,
        Parameters(ReadParams {
            address,
            kind,
            r#type: ty,
            count,
        }): Parameters<ReadParams>,
    ) -> Result<String, ErrorData> {
        let count = count_param(count, 1, 256, "count")?;
        let n = count.n;
        if let Some(spelled) = ty {
            if kind.is_some() {
                return Err(err_params(
                    "`kind` and `type` both say what the bytes are; give one",
                ));
            }
            let parsed = borer_engine::analysis::utypes::parse_type(&spelled)
                .map_err(|e| err_params(e.to_string()))?;
            let parsed = if n > 1 {
                borer_engine::analysis::utypes::TypeExpr::Array(
                    Box::new(parsed),
                    num::from_usize(n),
                )
            } else {
                parsed
            };
            return self
                .with_program(|p| {
                    if parse_off(&address).is_some() {
                        return Err(
                            "a typed read takes an address; off: reads by `kind`".to_owned()
                        );
                    }
                    let va = self.addr(p, &address)?;
                    let analysis = read_lock(&self.analysis).clone();
                    render::typed_tsv(p, analysis.as_deref(), &self.overlay(), va, &parsed)
                })
                .map(|text| count.noted(text));
        }
        let kind_text = kind.unwrap_or_default();
        let kind: memory::Kind = kind_text.into();
        self.with_program(|p| {
            let (start, values, place) = match parse_off(&address) {
                Some(off) => (off, memory::read_values_at_offset(p, off, kind, n)?, "off:"),
                None => {
                    let va = self.addr(p, &address)?;
                    (va, memory::read_values(p, va, kind, n)?, "")
                }
            };
            let analysis = read_lock(&self.analysis).clone();
            let o = self.overlay();
            let sec = if place.is_empty() {
                p.section_at(start)
                    .map_or_else(String::new, |s| format!(" in {}", s.name))
            } else {
                String::from(", rows by file offset")
            };
            let mut out = format!("# {} x {kind_text} at {place}{start:#x}{sec}", values.len());
            if values.len() < n {
                let next = values
                    .last()
                    .map_or(start, |v| v.at.wrapping_add(num::from_usize(v.size)));
                out.push_str(&format!(
                    "; asked for {n}, nothing readable at {place}{next:#x}"
                ));
            }
            out.push('\n');
            for v in &values {
                let mut text = v.text.clone();
                if let Some(name) = v
                    .target
                    .and_then(|t| render::pointee_name(p, analysis.as_deref(), &o, t))
                {
                    text.push_str(&format!(" -> {name}"));
                }
                out.push_str(&format!("{:<12} {text}\n", format!("{:#x}", v.at)));
            }
            Ok(out)
        })
        .map(|text| count.noted(text))
    }

    /// Lists high-entropy regions over every byte of the file.
    ///
    /// # Arguments
    ///
    /// * `EntropyParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the threshold is outside 0..8 or the
    /// limit is zero.
    #[tool(
        description = "High-entropy regions (packed/encrypted data) as `off va len entropy` rows at or above threshold bits/byte under a `# showing N of M` header; the scan stops at 200 regions.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn entropy(
        &self,
        Parameters(EntropyParams {
            window,
            threshold,
            offset,
            limit,
        }): Parameters<EntropyParams>,
    ) -> Result<String, ErrorData> {
        let window = to_usize(window.unwrap_or(1024));
        let threshold = entropy_threshold(threshold.unwrap_or(7.2)).map_err(err_params)?;
        let page = Page::new(
            offset,
            limit,
            None,
            entropy::REGIONS_MAX,
            entropy::REGIONS_MAX,
        )?;
        self.with_program(|p| {
            Ok(entropy::report(
                p,
                window,
                threshold,
                page.offset,
                page.limit.n,
            ))
        })
        .map(|text| page.limit.noted(text))
    }

    /// Hexdumps a byte range at an address or name.
    ///
    /// A hexdump is a "show me what is there" tool, so a length that runs
    /// off the end of the section gives back the bytes that are there rather
    /// than nothing: the header states the range it actually covers, so the
    /// short answer says so itself. Only an address with nothing at all
    /// behind it is refused, and then the message blames the address rather
    /// than the length, which is what was actually wrong.
    ///
    /// # Arguments
    ///
    /// * `HexdumpParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the range is not entirely mapped.
    #[tool(
        description = "Hexdump `length` bytes (default 64, max 4096) at `address`.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn hexdump(
        &self,
        Parameters(HexdumpParams { address, length }): Parameters<HexdumpParams>,
    ) -> Result<String, ErrorData> {
        let length = count_param(length, 64, 4096, "length")?;
        self.with_program(|p| {
            if let Some(off) = parse_off(&address) {
                return hexfmt::file_hexdump(p, off, length.n);
            }
            let va = self.addr(p, &address)?;
            let code = p.read_va_upto(va, length.n).ok_or_else(|| {
                format!(
                    "address {va:#x} not mapped; sections: {}{}",
                    p.section_list(),
                    memory::by_offset_hint(p)
                )
            })?;
            let sec = p
                .section_at(va)
                .map_or_else(String::new, |s| format!(" {}", s.name));
            Ok(format!(
                "# {va:#x}..{:#x}{sec}\n{}",
                va + num::from_usize(code.len()),
                hexfmt::hexdump(code, va)
            ))
        })
        .map(|text| length.noted(text))
    }
}

/// Reads an entropy threshold, the same for `entropy` and the command line.
///
/// # Arguments
///
/// * `threshold` - Minimum bits per byte, as given.
///
/// # Errors
///
/// When the threshold is outside `0..=8` bits per byte: no window holds
/// more than eight, and a negative one would report every window
/// ([`entropy::threshold_error`]).
pub(crate) fn entropy_threshold(threshold: f64) -> Result<f64, String> {
    entropy::threshold_error(threshold).map_or(Ok(threshold), Err)
}
