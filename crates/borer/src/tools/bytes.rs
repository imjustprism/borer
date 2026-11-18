//! The byte tools' tests; the tools that read bytes (disassembly, typed
//! reads, hex dumps and entropy) are the catalog's ([`borer_front::tools`]).

pub(crate) use borer_front::tools::entropy_threshold;

#[cfg(test)]
mod tests {
    use borer_engine::program::{Arch, Program, Section};
    use rmcp::handler::server::wrapper::Parameters;

    use crate::params::{ReadKind, ReadParams};

    /// Every string longer than a read prints says where the rest of it
    /// reads from, and the read from there is whole.
    ///
    /// A template's `__PRETTY_FUNCTION__` spells its arguments last, past
    /// the cut, so the rest must be one read away.
    ///
    /// # Panics
    ///
    /// When a read fails, or the header does not say where the rest is.
    #[test]
    fn a_cut_string_says_where_its_rest_reads_from() {
        let mut bytes = vec![b'A'; 300];
        bytes.push(0);
        bytes.extend([b'B'; 300]);
        bytes.resize(0x1000, 0);
        let sections = vec![Section::mapped(".rdata", 0x2000, 0, 0x1000, false, false)];
        let server =
            crate::testing::server_with(Program::raw(bytes, Arch::X86_64, 0, None, sections));
        let read = |address: &str, count: u32| {
            server
                .read(Parameters(ReadParams {
                    address: address.to_owned(),
                    kind: Some(ReadKind::CStr),
                    r#type: None,
                    count: Some(count),
                }))
                .expect("reads")
        };
        let first = read("0x2000", 1);
        assert!(
            first.contains("...\" (len 300), cut: the rest reads from 0x20c8\n"),
            "{first}"
        );
        let rest = read("0x20c8", 1);
        assert!(
            rest.contains("(len 100)") && !rest.contains("cut:"),
            "{rest}"
        );
        let both = read("0x2000", 2);
        assert!(
            both.contains("cut: the rest reads from 0x20c8\n")
                && both.contains("cut: the rest reads from 0x21f5\n"),
            "{both}"
        );
    }

    /// A hexdump, a disassembly and a read in a section the file holds no
    /// bytes for name the section and say the loader zero-fills it.
    ///
    /// # Panics
    ///
    /// When a tool answers, or its refusal calls the address not mapped.
    #[test]
    fn reads_in_a_section_without_file_bytes_name_it() {
        use crate::params::{DisassembleParams, HexdumpParams};
        let mut bss = Section::mapped(".bss", 0x2000, 0, 0x100, true, false);
        bss.file_size = 0;
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let program = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, None, vec![text, bss]);
        let server = crate::testing::server_with(program);
        let want =
            "address 0x2010 is in .bss, which holds no file bytes (the loader zero-fills it)";
        let dump = server.hexdump(Parameters(HexdumpParams {
            address: "0x2010".to_owned(),
            length: None,
        }));
        assert_eq!(dump.expect_err("refused").message, want);
        let code = server.disassemble(Parameters(DisassembleParams {
            address: "0x2010".to_owned(),
            count: None,
            bytes: None,
        }));
        assert_eq!(code.expect_err("refused").message, want);
        let read = server.read(Parameters(ReadParams {
            address: "0x2010".to_owned(),
            kind: Some(ReadKind::U8),
            r#type: None,
            count: None,
        }));
        assert_eq!(read.expect_err("refused").message, want);
    }
}
