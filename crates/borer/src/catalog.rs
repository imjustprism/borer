//! What the server lists of the resource catalog
//! ([`borer_engine::answer::catalog`]): their MIME type and the names
//! `binary_info` gives.

#[cfg(test)]
use borer_engine::answer::catalog::RESOURCES;
use borer_engine::answer::catalog::{RESOURCE_TEMPLATES, resource_name};

/// The MIME type of every resource: plain text tables, as the tools answer.
pub(crate) const TEXT_PLAIN: &str = "text/plain";

/// The `# more:` line of `binary_info`: every resource template by name,
/// from [`RESOURCE_TEMPLATES`] itself.
///
/// The line was written by hand and named 14 of 45 templates, so an agent
/// reading it never learned of the rest.
pub(crate) fn template_names() -> String {
    let names: Vec<&str> = RESOURCE_TEMPLATES
        .iter()
        .map(|&(uri, _, _)| resource_name(uri))
        .collect();
    format!(
        "{} templated resources read by URI through resources/read or the query tool, each described by resources/templates/list or read without its argument: {}",
        names.len(),
        names.join(", ")
    )
}

#[cfg(test)]
mod tests {
    use crate::testing::raw_server;

    /// The resource documentation says what the resources do.
    ///
    /// Every template the dispatcher answers is listed, `binary_info`
    /// names every template, no description carries a run of spaces from a
    /// broken line, and `emulate` and `devirt` describe every setting they
    /// read, `trace=` as the last steps it keeps.
    ///
    /// # Panics
    ///
    /// When a template is unlisted or unnamed, or a description misleads.
    #[test]
    fn the_resource_docs_say_what_the_resources_do() {
        let info = raw_server().binary_info().expect("info");
        let more = info
            .lines()
            .find_map(|l| l.strip_prefix("# more: "))
            .expect("a more line");
        for &(uri, _, _) in super::RESOURCE_TEMPLATES {
            let name = super::resource_name(uri);
            assert!(more.split([' ', ',']).any(|w| w == name), "{name}: {more}");
        }
        for uri in ["borer://map/{namespace}", "borer://ports/{filter}"] {
            assert!(
                super::RESOURCE_TEMPLATES.iter().any(|&(u, _, _)| u == uri),
                "{uri} is answered but not listed"
            );
        }
        let described_all = super::RESOURCES
            .iter()
            .copied()
            .chain(super::RESOURCE_TEMPLATES.iter().map(|&(u, d, _)| (u, d)));
        for (uri, text) in described_all {
            assert!(!text.contains("  "), "{uri}: {text}");
        }
        let described = |uri: &str| {
            super::RESOURCE_TEMPLATES
                .iter()
                .find(|&&(u, _, _)| u == uri)
                .map(|&(_, text, _)| text)
                .expect("listed")
        };
        let emulate = described("borer://emulate/{address}");
        assert!(
            emulate.contains("each of the last n instructions"),
            "{emulate}"
        );
        assert!(
            emulate.contains("origin=") && emulate.contains("profile="),
            "{emulate}"
        );
        let devirt = described("borer://devirt/{address}");
        for setting in ["budget=", "strict", "reg="] {
            assert!(devirt.contains(setting), "{setting}: {devirt}");
        }
    }

    /// The `borer://asserts` description names every tier its pairing rows
    /// spell.
    ///
    /// # Panics
    ///
    /// When a tier is unnamed.
    #[test]
    fn the_asserts_description_names_every_tier() {
        let (_, text) = super::RESOURCES
            .iter()
            .find(|&&(u, _)| u == "borer://asserts")
            .copied()
            .expect("listed");
        for tier in ["strong", "contested", "weak", "bare"] {
            assert!(text.contains(tier), "{tier}: {text}");
        }
    }

    /// No description of a resource reads as text addressed to an AI
    /// model, so the lines of such text an answer counts are the file's,
    /// never borer's own words.
    ///
    /// # Panics
    ///
    /// When a description carries a mark.
    #[test]
    fn no_description_addresses_a_model() {
        let described_all = super::RESOURCES
            .iter()
            .copied()
            .chain(super::RESOURCE_TEMPLATES.iter().map(|&(u, d, _)| (u, d)));
        for (uri, text) in described_all {
            assert_eq!(borer_engine::text::aimed_lines(text), 0, "{uri}: {text}");
        }
    }
}
