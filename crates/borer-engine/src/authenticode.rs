//! Authenticode signatures: who signed a PE, and whether the file still
//! hashes to the digest the signature covers.
//!
//! The certificate table holds a PKCS#7 `SignedData` whose content is an
//! `SpcIndirectDataContent`: the digest of the file as Authenticode hashes
//! it ([`crate::hashing::file_hash`]) and the algorithm it used. A file
//! edited after signing hashes to another digest. The signer is the
//! certificate the first `SignerInfo` names by issuer and serial, read for its
//! common name, organization and validity dates. Nothing here checks a
//! cryptographic signature or a certificate chain, and the text says so: a
//! matching digest under a forged signature still matches.

use std::fmt::Write as _;

/// `signedData`, 1.2.840.113549.1.7.2.
const SIGNED_DATA: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x07, 0x02];
/// SHA-256, 2.16.840.1.101.3.4.2.1.
const SHA256: &[u8] = &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01];
/// SHA-1, 1.3.14.3.2.26.
const SHA1: &[u8] = &[0x2b, 0x0e, 0x03, 0x02, 0x1a];
/// MD5, 1.2.840.113549.2.5.
const MD5: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x02, 0x05];
/// `commonName`, 2.5.4.3.
const COMMON_NAME: &[u8] = &[0x55, 0x04, 0x03];
/// `organizationName`, 2.5.4.10.
const ORGANIZATION: &[u8] = &[0x55, 0x04, 0x0a];
/// Longest digest a signature carries, in bytes: SHA-512's; a longer one
/// is no digest.
const DIGEST_MAX: usize = 64;
/// Most certificates read for the signer's: a table holding more is cut.
const CERTS_MAX: usize = 64;
/// Longest name the text quotes, in characters.
const NAME_MAX: usize = 96;

/// A DER `SEQUENCE`.
const SEQ: u8 = 0x30;
/// A DER `SET`.
const SET: u8 = 0x31;
/// A DER `INTEGER`.
const INT: u8 = 0x02;
/// A DER `OBJECT IDENTIFIER`.
const OID: u8 = 0x06;
/// A DER `OCTET STRING`.
const OCTETS: u8 = 0x04;
/// The first context-specific constructed tag, `[0]`.
const CTX0: u8 = 0xa0;

/// What a signature says.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    /// The digest algorithm's name, `None` for one borer does not name.
    pub(crate) algorithm: Option<&'static str>,
    /// The digest the signature covers.
    pub(crate) digest: Vec<u8>,
    /// The signer's common name, then its organization, when they differ.
    pub(crate) signer: Option<String>,
    /// The signer certificate's validity, `notBefore` and `notAfter` as
    /// `YYYY-MM-DD`.
    pub(crate) valid: Option<(String, String)>,
}

/// A cursor over DER elements, every read bounds-checked.
#[derive(Debug, Clone, Copy)]
struct Der<'a>(&'a [u8]);

impl<'a> Der<'a> {
    /// Returns the next element's tag and contents, `None` at the end or
    /// on a length the bytes do not hold (indefinite lengths included).
    fn next(&mut self) -> Option<(u8, &'a [u8])> {
        let (&tag, rest) = self.0.split_first()?;
        let (&first, rest) = rest.split_first()?;
        let (len, rest) = if first < 0x80 {
            (usize::from(first), rest)
        } else {
            let n = usize::from(first & 0x7f);
            if n == 0 || n > 4 {
                return None;
            }
            let (digits, rest) = rest.split_at_checked(n)?;
            let len = digits
                .iter()
                .fold(0usize, |l, &d| (l << 8) | usize::from(d));
            (len, rest)
        };
        let (body, rest) = rest.split_at_checked(len)?;
        self.0 = rest;
        Some((tag, body))
    }

    /// Returns the next element's contents when its tag is `tag`.
    fn take(&mut self, tag: u8) -> Option<&'a [u8]> {
        self.next().filter(|(t, _)| *t == tag).map(|(_, b)| b)
    }
}

/// Reads the signature in a certificate table entry's PKCS#7 bytes.
///
/// # Arguments
///
/// * `pkcs7` - The `WIN_CERTIFICATE`'s certificate bytes.
///
/// # Returns
///
/// The signature, or `None` when the bytes are no Authenticode
/// `SignedData` (any malformed element ends the read).
pub(crate) fn read(pkcs7: &[u8]) -> Option<Signature> {
    let mut info = Der(Der(pkcs7).take(SEQ)?);
    if info.take(OID)? != SIGNED_DATA {
        return None;
    }
    let mut signed = Der(Der(info.take(CTX0)?).take(SEQ)?);
    signed.take(INT)?;
    signed.take(SET)?;
    let mut content = Der(signed.take(SEQ)?);
    content.take(OID)?;
    let mut indirect = Der(Der(content.take(CTX0)?).take(SEQ)?);
    indirect.take(SEQ)?;
    let mut digest_info = Der(indirect.take(SEQ)?);
    let algorithm_oid = Der(digest_info.take(SEQ)?).take(OID)?;
    let digest = digest_info
        .take(OCTETS)
        .filter(|d| d.len() <= DIGEST_MAX)?
        .to_vec();
    let algorithm = [(SHA256, "sha256"), (SHA1, "sha1"), (MD5, "md5")]
        .into_iter()
        .find(|(oid, _)| *oid == algorithm_oid)
        .map(|(_, name)| name);
    let mut certs = None;
    let mut signers = None;
    while let Some((tag, body)) = signed.next() {
        match tag {
            CTX0 => certs = Some(body),
            SET => signers = Some(body),
            _ => {}
        }
    }
    let id = signers.and_then(signer_id);
    let tbs = certs.zip(id).and_then(|(c, id)| signer_tbs(c, id));
    Some(Signature {
        algorithm,
        digest,
        signer: tbs.and_then(subject),
        valid: tbs.and_then(validity),
    })
}

/// Returns the issuer name and serial number the first `SignerInfo` names
/// its certificate by.
///
/// # Arguments
///
/// * `infos` - The `signerInfos` set's contents.
fn signer_id(infos: &[u8]) -> Option<(&[u8], &[u8])> {
    let mut info = Der(Der(infos).take(SEQ)?);
    info.take(INT)?;
    let mut issuer_serial = Der(info.take(SEQ)?);
    Some((issuer_serial.take(SEQ)?, issuer_serial.take(INT)?))
}

/// Returns the `TBSCertificate` of the certificate the signer names.
///
/// That is the one with its issuer and serial number, two issuers' serials
/// being free to collide; `None` when no certificate of the table is it.
///
/// # Arguments
///
/// * `certs` - The `certificates` field's contents.
/// * `id` - The signer's issuer name and serial number.
fn signer_tbs<'a>(certs: &'a [u8], (issuer, serial): (&[u8], &[u8])) -> Option<&'a [u8]> {
    let mut all = Der(certs);
    for _ in 0..CERTS_MAX {
        let Some((SEQ, cert)) = all.next() else {
            break;
        };
        let Some(tbs) = Der(cert).take(SEQ) else {
            continue;
        };
        let mut f = fields(tbs);
        let named =
            f.take(INT) == Some(serial) && f.take(SEQ).is_some() && f.take(SEQ) == Some(issuer);
        if named {
            return Some(tbs);
        }
    }
    None
}

/// Returns a `TBSCertificate`'s fields after its optional `[0]` version.
///
/// # Arguments
///
/// * `tbs` - The `TBSCertificate`'s contents.
fn fields(tbs: &[u8]) -> Der<'_> {
    let mut d = Der(tbs);
    let mut peek = d;
    if peek.next().is_some_and(|(t, _)| t == CTX0) {
        d = peek;
    }
    d
}

/// Returns the subject's common name, with its organization when that
/// says something more.
///
/// # Arguments
///
/// * `tbs` - The `TBSCertificate`'s contents.
fn subject(tbs: &[u8]) -> Option<String> {
    let mut d = fields(tbs);
    for _ in 0..4 {
        d.next()?;
    }
    let name = d.take(SEQ)?;
    let cn = attribute(name, COMMON_NAME);
    let org = attribute(name, ORGANIZATION).filter(|o| Some(o) != cn.as_ref());
    match (cn, org) {
        (Some(cn), Some(org)) => Some(format!("{cn}, {org}")),
        (cn, org) => cn.or(org),
    }
}

/// Returns the first value of a name attribute, printable and capped.
///
/// # Arguments
///
/// * `name` - A `Name`'s contents: a sequence of relative names.
/// * `oid` - The attribute's type.
fn attribute(name: &[u8], oid: &[u8]) -> Option<String> {
    let mut rdns = Der(name);
    while let Some((SET, rdn)) = rdns.next() {
        let mut pairs = Der(rdn);
        while let Some((SEQ, pair)) = pairs.next() {
            let mut p = Der(pair);
            if p.take(OID) == Some(oid) {
                let (tag, value) = p.next()?;
                return Some(printable(tag, value));
            }
        }
    }
    None
}

/// Renders a directory string as text a line can carry.
///
/// A `BMPString` reads as UTF-16, the rest as UTF-8, control characters as
/// `?`, at most [`NAME_MAX`] characters, decoded from only as many bytes as
/// those take.
///
/// # Arguments
///
/// * `tag` - The string's DER tag.
/// * `value` - Its bytes.
fn printable(tag: u8, value: &[u8]) -> String {
    let value = value.get(..NAME_MAX * 4).unwrap_or(value);
    let text = if tag == 0x1e {
        let units: Vec<u16> = value
            .chunks_exact(2)
            .filter_map(|c| <[u8; 2]>::try_from(c).ok().map(u16::from_be_bytes))
            .collect();
        String::from_utf16_lossy(&units)
    } else {
        String::from_utf8_lossy(value).into_owned()
    };
    text.chars()
        .map(|c| if c.is_control() { '?' } else { c })
        .take(NAME_MAX)
        .collect()
}

/// Returns a `TBSCertificate`'s validity dates as `YYYY-MM-DD`.
///
/// # Arguments
///
/// * `tbs` - The `TBSCertificate`'s contents.
fn validity(tbs: &[u8]) -> Option<(String, String)> {
    let mut d = fields(tbs);
    for _ in 0..3 {
        d.next()?;
    }
    let mut v = Der(d.take(SEQ)?);
    Some((date(v.next()?)?, date(v.next()?)?))
}

/// Renders a `UTCTime` or `GeneralizedTime` as `YYYY-MM-DD`.
///
/// # Arguments
///
/// * `(tag, body)` - The time element.
fn date((tag, body): (u8, &[u8])) -> Option<String> {
    let digits = std::str::from_utf8(body).ok()?;
    let (year, rest) = match tag {
        0x17 => {
            let yy: u32 = digits.get(..2)?.parse().ok()?;
            (
                if yy < 50 { 2000 + yy } else { 1900 + yy },
                digits.get(2..)?,
            )
        }
        0x18 => (digits.get(..4)?.parse().ok()?, digits.get(4..)?),
        _ => return None,
    };
    let (month, day) = (rest.get(..2)?, rest.get(2..4)?);
    if !month.bytes().chain(day.bytes()).all(|b| b.is_ascii_digit()) {
        return None;
    }
    Some(format!("{year:04}-{month}-{day}"))
}

/// Renders what a signature says about a file, for the summary's notes.
///
/// # Arguments
///
/// * `sig` - The signature.
/// * `file_sha256` - The file's Authenticode SHA-256, `None` when it has
///   none.
///
/// # Returns
///
/// `signed by <signer>`, the validity, and whether the file still hashes to
/// the signed digest; only a SHA-256 digest is compared.
pub(crate) fn note(sig: &Signature, file_sha256: Option<&[u8; 32]>) -> String {
    let mut out = match &sig.signer {
        Some(name) => format!("signed by \"{name}\""),
        None => "signed (signer not read)".to_owned(),
    };
    if let Some((from, to)) = &sig.valid {
        let _ = write!(out, ", certificate valid {from} to {to}");
    }
    let verdict = match (sig.algorithm, file_sha256) {
        (Some("sha256"), Some(file)) if file.as_slice() == sig.digest => {
            "the file matches its signed sha256 digest".to_owned()
        }
        (Some("sha256"), Some(_)) => {
            "the file's sha256 differs from its signed digest: changed after signing".to_owned()
        }
        (Some(alg), _) => format!("signed {alg} digest not compared"),
        (None, _) => "digest algorithm not read".to_owned(),
    };
    let _ = write!(out, "; {verdict}; chain and signature not verified");
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The file matches its signature only when it hashes to the signed
    /// digest, and a digest of another algorithm is not compared.
    ///
    /// # Panics
    ///
    /// When the note misjudges the file.
    #[test]
    fn a_note_judges_the_file_by_its_digest() {
        let sig = Signature {
            algorithm: Some("sha256"),
            digest: vec![0x11; 32],
            signer: Some("Example Corp".to_owned()),
            valid: Some(("2020-01-01".to_owned(), "2030-12-31".to_owned())),
        };
        let same = note(&sig, Some(&[0x11; 32]));
        assert!(same.contains("signed by \"Example Corp\""), "{same}");
        assert!(same.contains("valid 2020-01-01 to 2030-12-31"), "{same}");
        assert!(same.contains("matches its signed sha256 digest"), "{same}");
        assert!(same.contains("not verified"), "{same}");
        let edited = note(&sig, Some(&[0x22; 32]));
        assert!(edited.contains("changed after signing"), "{edited}");
        let old = Signature {
            algorithm: Some("sha1"),
            ..sig
        };
        let old = note(&old, Some(&[0x11; 32]));
        assert!(old.contains("sha1 digest not compared"), "{old}");
    }

    /// Empty, indefinite-length or foreign bytes read as no signature.
    ///
    /// # Panics
    ///
    /// When malformed bytes read as a signature.
    #[test]
    fn malformed_bytes_read_as_no_signature() {
        assert!(read(&[]).is_none());
        assert!(read(&[0x30, 0x80, 0, 0]).is_none());
        assert!(read(&[0x30, 0x84, 0xff, 0xff, 0xff, 0xff]).is_none());
        assert!(
            read(&[
                0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01
            ])
            .is_none()
        );
    }
}
