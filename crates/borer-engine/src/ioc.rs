//! Indicators an incident responder blocks or hunts for, read out of text:
//! URLs, domains, IP addresses, e-mail addresses, registry keys, file
//! paths, pipe and kernel object names, user agents.
//!
//! The matchers are hand-written and bounded, and lean towards saying
//! nothing: a domain needs a top-level domain from a short list that leaves
//! out the ones a file extension spells (`.rs`, `.md`, `.zip`), an address
//! after the word `version` is a version, and a URL whose host does not
//! read as one is a truncated string, not an indicator. What the matchers
//! keep but every program carries (the XML schema hosts, certificate
//! revocation servers, the loopback address) is marked benign rather than
//! dropped, so a reader sees it was looked at.

/// What an indicator is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kind {
    /// A URL with a network scheme and a host.
    Url,
    /// A host name under a known top-level domain.
    Domain,
    /// A dotted-quad IPv4 address.
    Ipv4,
    /// An IPv6 address in its colon form.
    Ipv6,
    /// An e-mail address.
    Email,
    /// A registry key, under a hive or a well-known root.
    Registry,
    /// A file path: absolute, rooted at an environment variable or a share,
    /// or the name of an executable file.
    Path,
    /// A named pipe.
    Pipe,
    /// A mutex name, as a mutex API receives it.
    Mutex,
    /// Another named kernel object: an event, a semaphore, a section.
    Object,
    /// An HTTP user agent.
    UserAgent,
}

impl Kind {
    /// Every kind, in the order a listing groups them.
    pub const ALL: [Kind; 11] = [
        Kind::Url,
        Kind::Domain,
        Kind::Ipv4,
        Kind::Ipv6,
        Kind::Email,
        Kind::Registry,
        Kind::Path,
        Kind::Pipe,
        Kind::Mutex,
        Kind::Object,
        Kind::UserAgent,
    ];

    /// The word a listing prints for the kind and a filter names it by.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            Kind::Url => "url",
            Kind::Domain => "domain",
            Kind::Ipv4 => "ipv4",
            Kind::Ipv6 => "ipv6",
            Kind::Email => "email",
            Kind::Registry => "registry",
            Kind::Path => "path",
            Kind::Pipe => "pipe",
            Kind::Mutex => "mutex",
            Kind::Object => "object",
            Kind::UserAgent => "useragent",
        }
    }
}

/// How sure a match is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Confidence {
    /// The text cannot be read another way: a URL with a valid host, a
    /// public address, a key under a hive, a name an API was handed.
    High,
    /// Most likely what it is, though some other text could look like it.
    Medium,
    /// A guess worth a look: a bare file name, a version-shaped address.
    Low,
}

impl Confidence {
    /// The word a listing prints.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            Confidence::High => "high",
            Confidence::Medium => "medium",
            Confidence::Low => "low",
        }
    }
}

/// One indicator found in a text.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Indicator {
    /// What it is.
    pub kind: Kind,
    /// The indicator as the text spells it.
    pub value: String,
    /// How sure the match is.
    pub confidence: Confidence,
    /// Every program carries it (a schema host, a revocation server, the
    /// loopback address): looked at, and not worth blocking.
    pub benign: bool,
}

/// Longest text read whole; a longer one is read only token by token.
const WHOLE_MAX: usize = 1024;

/// Longest text read at all, in bytes; the rest of a longer one is not read.
const TEXT_MAX: usize = 4096;

/// Most indicators taken from one text.
const PER_TEXT_MAX: usize = 16;

/// Longest name a named-object or forced indicator keeps, in bytes.
const NAME_MAX: usize = 260;

/// URL schemes that name a network resource.
const SCHEMES: &[&str] = &["http", "https", "ftp", "ftps", "ws", "wss"];

/// Top-level domains a host name is accepted under.
///
/// Short of the full list on purpose: a TLD that is also a common file
/// extension or field name (`rs`, `md`, `sh`, `py`, `so`, `pl`, `cc`, `zip`,
/// `mov`, `in`, `id`, `name`, `app`, `email`, `store`) would turn every
/// source path and dotted identifier into a domain.
const TLDS: &[&str] = &[
    "ae", "ai", "ar", "asia", "at", "au", "bd", "be", "bg", "bid", "biz", "br", "by", "ca", "cf",
    "ch", "cl", "cloud", "club", "cn", "co", "com", "cyou", "cz", "de", "dev", "dk", "edu", "ee",
    "es", "eu", "fi", "fr", "fun", "ga", "gov", "gq", "gr", "hk", "hr", "hu", "icu", "ie", "il",
    "info", "ink", "io", "ir", "it", "jp", "kr", "kz", "la", "life", "link", "live", "lol", "lt",
    "lv", "me", "mil", "ml", "mobi", "mx", "net", "ng", "nl", "nz", "onion", "online", "org", "ph",
    "pk", "pt", "pw", "rest", "ro", "ru", "sa", "se", "sg", "shop", "si", "site", "sk", "su",
    "tech", "th", "tk", "to", "today", "top", "tr", "tv", "tw", "ua", "uk", "us", "vip", "vn",
    "website", "win", "world", "ws", "xyz", "za",
];

/// Host names every program may carry: schema namespaces, certificate
/// authorities and their revocation servers, toolchain sites. A host equal
/// to one or under it is benign.
const BENIGN_HOSTS: &[&str] = &[
    "adobe.com",
    "apache.org",
    "comodoca.com",
    "digicert.com",
    "entrust.net",
    "globalsign.com",
    "globalsign.net",
    "gnu.org",
    "godaddy.com",
    "identrust.com",
    "letsencrypt.org",
    "localhost",
    "microsoft.com",
    "mozilla.org",
    "openssl.org",
    "purl.org",
    "python.org",
    "rust-lang.org",
    "sectigo.com",
    "symantec.com",
    "symcb.com",
    "symcd.com",
    "thawte.com",
    "usertrust.com",
    "verisign.com",
    "w3.org",
];

/// Paths every program of a toolchain carries: build trees, the null and
/// random devices.
const BENIGN_PATHS: &[&str] = &[
    ".cargo/registry",
    ".cargo\\registry",
    "/rustc/",
    "/dev/null",
    "/dev/urandom",
    "/dev/random",
];

/// Words after which a dotted quad is a version, not an address.
const VERSION_WORDS: &[&str] = &[
    "version",
    "ver",
    "v",
    "build",
    "rev",
    "revision",
    "release",
    "fileversion",
    "productversion",
    "assemblyversion",
];

/// Registry roots that name a hive, matched case-insensitively.
const HIVES: &[&str] = &[
    "hkey_local_machine\\",
    "hkey_current_user\\",
    "hkey_classes_root\\",
    "hkey_users\\",
    "hkey_current_config\\",
    "hklm\\",
    "hkcu\\",
    "hkcr\\",
    "hku\\",
    "hkcc\\",
    "\\registry\\machine\\",
    "\\registry\\user\\",
];

/// Registry keys a program opens under a hive handle it passes apart.
const RELATIVE_KEYS: &[&str] = &[
    "software\\",
    "system\\currentcontrolset\\",
    "system\\controlset0",
];

/// Prefixes of a named pipe, matched case-insensitively.
const PIPES: &[&str] = &["\\\\.\\pipe\\", "\\??\\pipe\\", "\\device\\namedpipe\\"];

/// Namespaces of a named kernel object, matched case-insensitively.
const OBJECTS: &[&str] = &[
    "global\\",
    "local\\",
    "session\\",
    "\\basenamedobjects\\",
    "\\sessions\\",
];

/// Directories an absolute Unix path starts under.
const UNIX_ROOTS: &[&str] = &[
    "/etc/",
    "/tmp/",
    "/var/",
    "/usr/",
    "/bin/",
    "/sbin/",
    "/dev/",
    "/proc/",
    "/home/",
    "/root/",
    "/lib/",
    "/lib64/",
    "/opt/",
    "/run/",
    "/sys/",
    "/boot/",
    "/mnt/",
    "/media/",
    "/srv/",
    "/Users/",
    "/Library/",
    "/System/",
    "/private/",
    "/Applications/",
    "/data/",
    "/sdcard/",
];

/// Extensions of a file that runs, which a bare name is kept for.
const RUNNABLE: &[&str] = &["exe", "bat", "cmd", "ps1", "vbs", "scr", "hta", "lnk"];

/// Finds the indicators in one string.
///
/// The whole string is tried first for the kinds that may hold spaces (a
/// registry key, a pipe or object name, a user agent, a path whose last
/// part has no space); then each URL in it, then each token between
/// spaces, quotes, brackets and the like for the rest.
///
/// # Arguments
///
/// * `text` - The string, as the binary holds it.
///
/// # Returns
///
/// The indicators in the order the text holds them, at most
/// [`PER_TEXT_MAX`], each once.
#[must_use]
pub fn classify(text: &str) -> Vec<Indicator> {
    let text = cut(text.trim(), TEXT_MAX);
    if text.len() < 4 {
        return Vec::new();
    }
    if text.len() <= WHOLE_MAX
        && let Some(found) = whole(text)
    {
        return vec![found];
    }
    let mut out: Vec<Indicator> = Vec::new();
    let mut rest = String::with_capacity(text.len());
    let mut from = 0;
    for (start, end) in url_spans(text) {
        if let Some(found) = url(&text[start..end]) {
            push(&mut out, found);
        }
        rest.push_str(&text[from..start]);
        rest.push(' ');
        from = end;
    }
    rest.push_str(&text[from..]);
    let tokens: Vec<&str> = rest.split(delimiter).filter(|t| !t.is_empty()).collect();
    for (i, raw) in tokens.iter().enumerate() {
        if out.len() >= PER_TEXT_MAX {
            break;
        }
        let tok = raw.trim_end_matches(['.', ',', ':', ';', '!', '?']);
        let prev = i
            .checked_sub(1)
            .and_then(|j| tokens.get(j))
            .map_or("", |p| p.trim_matches([':', '=', '"', '\'']));
        if let Some(found) = token(tok, prev) {
            push(&mut out, found);
        }
    }
    out.truncate(PER_TEXT_MAX);
    out
}

/// The indicator a named argument is when an API says what it names: a
/// mutex, a pipe, a key, a file.
///
/// # Arguments
///
/// * `kind` - What the API's argument names.
/// * `text` - The argument's text.
///
/// # Returns
///
/// The indicator, high confidence, or `None` for an empty name, one longer
/// than [`NAME_MAX`] or one holding a control character.
#[must_use]
pub fn named(kind: Kind, text: &str) -> Option<Indicator> {
    let value = text.trim();
    if value.is_empty() || value.len() > NAME_MAX || value.chars().any(char::is_control) {
        return None;
    }
    Some(Indicator {
        kind,
        value: value.to_owned(),
        confidence: Confidence::High,
        benign: kind == Kind::Path && benign_path(value),
    })
}

/// Cuts text to at most `max` bytes, at a character boundary.
///
/// # Arguments
///
/// * `text` - The text.
/// * `max` - Most bytes kept.
fn cut(text: &str, max: usize) -> &str {
    if text.len() <= max {
        return text;
    }
    let mut end = max;
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    &text[..end]
}

/// Adds an indicator unless the same one is there.
///
/// # Arguments
///
/// * `out` - The indicators so far.
/// * `found` - The new one.
fn push(out: &mut Vec<Indicator>, found: Indicator) {
    if !out
        .iter()
        .any(|o| o.kind == found.kind && o.value == found.value)
    {
        out.push(found);
    }
}

/// Tells whether a character separates tokens.
///
/// # Arguments
///
/// * `c` - The character.
fn delimiter(c: char) -> bool {
    c.is_whitespace()
        || matches!(
            c,
            '"' | '\''
                | '<'
                | '>'
                | '('
                | ')'
                | '['
                | ']'
                | '{'
                | '}'
                | ','
                | ';'
                | '|'
                | '`'
                | '='
        )
}

/// Tells whether `text` starts with `prefix`, ignoring ASCII case, and has
/// something after it.
///
/// # Arguments
///
/// * `text` - The text.
/// * `prefix` - A lowercase prefix.
fn starts(text: &str, prefix: &str) -> bool {
    text.len() > prefix.len()
        && text
            .get(..prefix.len())
            .is_some_and(|head| head.eq_ignore_ascii_case(prefix))
}

/// The indicator a whole string is, for the kinds that may hold spaces.
///
/// # Arguments
///
/// * `text` - The trimmed string.
fn whole(text: &str) -> Option<Indicator> {
    let found = |kind, confidence| {
        Some(Indicator {
            kind,
            value: text.to_owned(),
            confidence,
            benign: kind == Kind::Path && benign_path(text),
        })
    };
    if text.contains(['\n', '\r', '\t']) {
        return None;
    }
    if HIVES.iter().any(|h| starts(text, h)) {
        return found(Kind::Registry, Confidence::High);
    }
    if RELATIVE_KEYS.iter().any(|k| starts(text, k)) {
        return found(Kind::Registry, Confidence::Medium);
    }
    if PIPES.iter().any(|p| starts(text, p)) {
        return found(Kind::Pipe, Confidence::High);
    }
    if text.len() <= NAME_MAX && OBJECTS.iter().any(|o| starts(text, o)) {
        return found(Kind::Object, Confidence::Medium);
    }
    if text.len() >= 12 && text.starts_with("Mozilla/") {
        return found(Kind::UserAgent, Confidence::High);
    }
    let last = text.rsplit(['\\', '/']).next().unwrap_or(text);
    if path_start(text) && !last.contains(' ') {
        return found(Kind::Path, Confidence::Medium);
    }
    None
}

/// The byte spans of the URLs in a text: from the scheme to the first
/// space, quote or bracket after `://`.
///
/// # Arguments
///
/// * `text` - The text.
fn url_spans(text: &str) -> Vec<(usize, usize)> {
    let mut spans = Vec::new();
    let mut from = 0;
    while let Some(rel) = text.get(from..).and_then(|t| t.find("://")) {
        let sep = from + rel;
        let start = text[..sep]
            .char_indices()
            .rev()
            .take_while(|(_, c)| c.is_ascii_alphanumeric() || matches!(c, '+' | '.' | '-'))
            .last()
            .map_or(sep, |(i, _)| i);
        let end = text[sep..]
            .find(|c: char| {
                c.is_whitespace() || matches!(c, '"' | '\'' | '<' | '>' | '`' | '|' | '{' | '}')
            })
            .map_or(text.len(), |e| sep + e);
        if start < sep {
            spans.push((start, end));
        }
        from = end.max(sep + 3);
    }
    spans
}

/// The URL indicator a span is, when its scheme names a network resource
/// and its host reads as one.
///
/// # Arguments
///
/// * `span` - From the scheme to the URL's end.
fn url(span: &str) -> Option<Indicator> {
    let span = span.trim_end_matches(['.', ',', ':', ';', '!', '?', ')', ']']);
    let (scheme, rest) = span.split_once("://")?;
    if !SCHEMES.iter().any(|s| s.eq_ignore_ascii_case(scheme)) {
        return None;
    }
    let authority = rest.split(['/', '?', '#']).next().unwrap_or("");
    let host_port = authority.rsplit_once('@').map_or(authority, |(_, h)| h);
    let host = match host_port.strip_prefix('[') {
        Some(v6) => v6.split_once(']').map_or(v6, |(h, _)| h),
        None => host_port.split(':').next().unwrap_or(""),
    };
    let lower = host.to_ascii_lowercase();
    let benign = if let Some(ip) = ipv4(&lower) {
        ip.benign
    } else if lower == "localhost" {
        true
    } else if ipv6(&lower).is_some() || labels_ok(&lower, false) {
        benign_host(&lower)
    } else {
        return None;
    };
    Some(Indicator {
        kind: Kind::Url,
        value: span.to_owned(),
        confidence: Confidence::High,
        benign,
    })
}

/// The indicator one token is.
///
/// # Arguments
///
/// * `tok` - The token, trailing punctuation removed.
/// * `prev` - The token before it, which says when a dotted quad is a
///   version.
fn token(tok: &str, prev: &str) -> Option<Indicator> {
    if tok.len() < 4 {
        return None;
    }
    if let Some((local, domain)) = tok.split_once('@') {
        let local_ok = !local.is_empty()
            && local
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '%' | '+' | '-'));
        return (local_ok && labels_ok(domain, true)).then(|| Indicator {
            kind: Kind::Email,
            value: tok.to_owned(),
            confidence: Confidence::Medium,
            benign: benign_host(&domain.to_ascii_lowercase()),
        });
    }
    if let Some(found) = ipv4(tok) {
        let version = VERSION_WORDS.iter().any(|w| prev.eq_ignore_ascii_case(w));
        return (!version).then_some(found);
    }
    if let Some(found) = ipv6(tok) {
        return Some(found);
    }
    let found = |kind, confidence| {
        Some(Indicator {
            kind,
            value: tok.to_owned(),
            confidence,
            benign: kind == Kind::Path && benign_path(tok),
        })
    };
    if HIVES.iter().any(|h| starts(tok, h)) {
        return found(Kind::Registry, Confidence::High);
    }
    if PIPES.iter().any(|p| starts(tok, p)) {
        return found(Kind::Pipe, Confidence::High);
    }
    if path_start(tok) {
        return found(Kind::Path, Confidence::Medium);
    }
    let host = match tok.rsplit_once(':') {
        Some((host, port))
            if !port.is_empty() && port.len() <= 5 && port.bytes().all(|b| b.is_ascii_digit()) =>
        {
            host
        }
        Some(_) | None => tok,
    };
    if labels_ok(host, true) {
        return Some(Indicator {
            kind: Kind::Domain,
            value: host.to_owned(),
            confidence: Confidence::Medium,
            benign: benign_host(&host.to_ascii_lowercase()),
        });
    }
    let (stem, ext) = tok.rsplit_once('.')?;
    let runnable = RUNNABLE.iter().any(|r| ext.eq_ignore_ascii_case(r))
        && !stem.is_empty()
        && stem
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.'));
    runnable.then(|| Indicator {
        kind: Kind::Path,
        value: tok.to_owned(),
        confidence: Confidence::Low,
        benign: false,
    })
}

/// Tells whether a text starts the way a file path does: a drive, an
/// environment variable, a share, an NT or long-path prefix before one of
/// those, or an absolute Unix directory.
///
/// # Arguments
///
/// * `text` - The text.
fn path_start(text: &str) -> bool {
    let text = text
        .strip_prefix("\\\\?\\")
        .or_else(|| text.strip_prefix("\\??\\"))
        .unwrap_or(text);
    let b = text.as_bytes();
    let drive = b.len() > 3 && b[0].is_ascii_alphabetic() && b[1] == b':' && b[2] == b'\\';
    let env = b.first() == Some(&b'%')
        && text
            .get(1..)
            .and_then(|t| t.split_once("%\\"))
            .is_some_and(|(var, after)| {
                !var.is_empty()
                    && !after.is_empty()
                    && var
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '(' | ')'))
            });
    let share = text.strip_prefix("\\\\").is_some_and(|t| {
        t.split_once('\\').is_some_and(|(host, after)| {
            !host.is_empty()
                && !after.is_empty()
                && host
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_' | '$'))
                && host != "."
        })
    });
    let unix = UNIX_ROOTS
        .iter()
        .any(|r| text.len() > r.len() && text.starts_with(r));
    drive || env || share || unix
}

/// Tells whether a dotted name is a host name.
///
/// # Arguments
///
/// * `name` - The candidate.
/// * `listed` - The top-level domain must be lowercase and in [`TLDS`];
///   false accepts any alphabetic one of two letters or more, for a URL's
///   host, whose scheme already says it is one.
fn labels_ok(name: &str, listed: bool) -> bool {
    if name.len() < 4 || name.len() > 253 {
        return false;
    }
    let labels: Vec<&str> = name.split('.').collect();
    let Some((tld, below)) = labels.split_last() else {
        return false;
    };
    if below.is_empty() {
        return false;
    }
    let tld_ok = if listed {
        TLDS.contains(tld)
    } else {
        tld.len() >= 2 && tld.chars().all(|c| c.is_ascii_alphabetic())
    };
    let label_ok = |l: &&str| {
        !l.is_empty()
            && l.len() <= 63
            && !l.starts_with('-')
            && !l.ends_with('-')
            && l.chars().all(|c| c.is_ascii_alphanumeric() || c == '-')
    };
    tld_ok
        && below.iter().all(label_ok)
        && below
            .iter()
            .any(|l| l.chars().any(|c| c.is_ascii_alphabetic()))
}

/// The IPv4 indicator a token is, port allowed.
///
/// # Arguments
///
/// * `tok` - The token.
fn ipv4(tok: &str) -> Option<Indicator> {
    let (addr, port) = tok.split_once(':').unwrap_or((tok, ""));
    if !port.is_empty() && (port.len() > 5 || !port.bytes().all(|b| b.is_ascii_digit())) {
        return None;
    }
    let mut octets = [0u8; 4];
    let mut parts = addr.split('.');
    for o in &mut octets {
        let part = parts.next()?;
        let well_formed = !part.is_empty()
            && part.len() <= 3
            && part.bytes().all(|b| b.is_ascii_digit())
            && (part.len() == 1 || !part.starts_with('0'));
        if !well_formed {
            return None;
        }
        *o = part.parse().ok()?;
    }
    if parts.next().is_some() {
        return None;
    }
    let [a, b, _, _] = octets;
    let benign = a == 0 || a == 127 || octets == [255; 4];
    let private = a == 10 || (a == 192 && b == 168) || (a == 172 && (16..32).contains(&b));
    let confidence = if octets[1..] == [0, 0, 0] {
        Confidence::Low
    } else if private || benign {
        Confidence::Medium
    } else {
        Confidence::High
    };
    Some(Indicator {
        kind: Kind::Ipv4,
        value: tok.to_owned(),
        confidence,
        benign,
    })
}

/// The IPv6 indicator a token is: eight groups, or at least three around
/// one `::`, each of one to four hex digits, at least one with a digit.
///
/// # Arguments
///
/// * `tok` - The token.
fn ipv6(tok: &str) -> Option<Indicator> {
    let addr = tok
        .strip_prefix('[')
        .and_then(|t| t.strip_suffix(']'))
        .unwrap_or(tok);
    if !addr.contains(':') || !addr.chars().all(|c| c.is_ascii_hexdigit() || c == ':') {
        return None;
    }
    let compressed = addr.matches("::").count();
    let groups: Vec<&str> = addr.split(':').filter(|g| !g.is_empty()).collect();
    let shaped = match compressed {
        0 => groups.len() == 8 && addr.split(':').count() == 8,
        1 => (3..=7).contains(&groups.len()),
        _ => false,
    };
    let ok = shaped
        && !addr.contains(":::")
        && groups.iter().all(|g| g.len() <= 4)
        && groups.iter().any(|g| g.chars().any(|c| c.is_ascii_digit()));
    ok.then(|| Indicator {
        kind: Kind::Ipv6,
        value: tok.to_owned(),
        confidence: Confidence::Medium,
        benign: false,
    })
}

/// Tells whether a lowercase host is one every program may carry.
///
/// # Arguments
///
/// * `host` - The host name, lowercase.
fn benign_host(host: &str) -> bool {
    host.starts_with("ocsp.")
        || host.starts_with("crl.")
        || BENIGN_HOSTS
            .iter()
            .any(|b| host == *b || host.strip_suffix(b).is_some_and(|head| head.ends_with('.')))
}

/// Tells whether a path is one every program of a toolchain carries.
///
/// # Arguments
///
/// * `path` - The path.
fn benign_path(path: &str) -> bool {
    BENIGN_PATHS.iter().any(|b| path.contains(b))
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Confidence, Indicator, Kind, classify, named};

    /// The kind and value of each indicator, for comparing.
    ///
    /// # Arguments
    ///
    /// * `text` - The string classified.
    fn found(text: &str) -> Vec<(Kind, String)> {
        classify(text)
            .into_iter()
            .map(|i| (i.kind, i.value))
            .collect()
    }

    /// Each kind is read from the text that spells it, and the URL keeps
    /// its query.
    #[test]
    fn each_kind_is_read_from_its_text() {
        assert_eq!(
            found("GET http://evil.example.com/gate.php?id=4 now"),
            [(
                Kind::Url,
                "http://evil.example.com/gate.php?id=4".to_owned()
            )]
        );
        assert_eq!(
            found("connect to c2.badhost.ru:443 or 45.33.12.9:8080"),
            [
                (Kind::Domain, "c2.badhost.ru".to_owned()),
                (Kind::Ipv4, "45.33.12.9:8080".to_owned())
            ]
        );
        assert_eq!(
            found("SOFTWARE\\Microsoft\\Windows\\CurrentVersion\\Run"),
            [(
                Kind::Registry,
                "SOFTWARE\\Microsoft\\Windows\\CurrentVersion\\Run".to_owned()
            )]
        );
        assert_eq!(
            found("\\\\.\\pipe\\demo_pipe"),
            [(Kind::Pipe, "\\\\.\\pipe\\demo_pipe".to_owned())]
        );
        assert_eq!(
            found("Global\\demo-mutex"),
            [(Kind::Object, "Global\\demo-mutex".to_owned())]
        );
        assert_eq!(
            found("C:\\Program Files\\Demo\\demo.exe"),
            [(Kind::Path, "C:\\Program Files\\Demo\\demo.exe".to_owned())]
        );
        assert_eq!(
            found("%APPDATA%\\demo\\run.bat"),
            [(Kind::Path, "%APPDATA%\\demo\\run.bat".to_owned())]
        );
        assert_eq!(
            found("mail admin@example.org today"),
            [(Kind::Email, "admin@example.org".to_owned())]
        );
        assert_eq!(
            found("Mozilla/5.0 (Windows NT 10.0; Win64; x64)"),
            [(
                Kind::UserAgent,
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64)".to_owned()
            )]
        );
        assert_eq!(
            found("server 2001:db8::8a2e:370:7334"),
            [(Kind::Ipv6, "2001:db8::8a2e:370:7334".to_owned())]
        );
        assert_eq!(
            found("open /etc/passwd failed"),
            [(Kind::Path, "/etc/passwd".to_owned())]
        );
    }

    /// Text that only looks like an indicator is not one: a version after
    /// its word, a truncated URL, a source file whose extension is a
    /// country's domain, a dotted identifier, a C++ scope.
    #[test]
    fn lookalikes_are_not_indicators() {
        assert!(found("version 1.2.3.4").is_empty());
        assert!(found("FileVersion: 10.0.19041.1").is_empty());
        assert!(found("assembly version=\"6.0.0.0\"").is_empty());
        assert!(found("http://").is_empty());
        assert!(found("see https://ex for more").is_empty());
        assert!(found("src/main.rs").is_empty());
        assert!(found("README.md and setup.py").is_empty());
        assert!(found("System.Net.Sockets").is_empty());
        assert!(found("std::io::Error::new").is_empty());
        assert!(found("1.2.3.4.5").is_empty());
        assert!(found("300.1.1.1").is_empty());
        assert!(found("12:30:45").is_empty());
    }

    /// What every program carries is kept but marked benign: a schema URL,
    /// the loopback address, a revocation server, a toolchain's build path.
    #[test]
    fn what_every_program_carries_is_marked_benign() {
        let benign = |text: &str| classify(text).iter().map(|i| i.benign).collect::<Vec<_>>();
        assert_eq!(
            benign("http://schemas.microsoft.com/SMI/2005/WindowsSettings"),
            [true]
        );
        assert_eq!(benign("127.0.0.1"), [true]);
        assert_eq!(benign("http://ocsp.digicert.com"), [true]);
        assert_eq!(benign("/home/u/.cargo/registry/src/x/lib.rs"), [true]);
        assert_eq!(benign("http://evil.example.com/"), [false]);
        let low = classify("6.0.0.0 here");
        assert_eq!(low.first().map(|i| i.confidence), Some(Confidence::Low));
    }

    /// An API's word for its argument names what it is, whatever the text.
    #[test]
    fn an_api_names_its_argument() {
        assert_eq!(
            named(Kind::Mutex, "demo_mutex_7"),
            Some(Indicator {
                kind: Kind::Mutex,
                value: "demo_mutex_7".to_owned(),
                confidence: Confidence::High,
                benign: false,
            })
        );
        assert_eq!(named(Kind::Mutex, "  "), None);
        assert_eq!(named(Kind::Pipe, "a\nb"), None);
    }
}
