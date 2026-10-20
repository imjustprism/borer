//! The stack protector folded out of a function's text.
//!
//! A compiler guards a frame with a copy of a secret word: the prologue
//! stores the guard (the thread block's `fs:0x28` or `gs:0x14` on Linux,
//! a guard global elsewhere, the `/GS` cookie mixed with the frame
//! address on Windows) into a slot, and every return compares the slot
//! with the guard, calling `__stack_chk_fail` or `__security_check_cookie`
//! on a mismatch. None of it is the function's work. The setup lines and
//! the checks leave the text here, after the structurer, and a header line
//! says what left; the statements stay in what the replay runs, so the
//! checks are still compared with the binary. The slot must leave with
//! them: a function that reads it anywhere else keeps its text.

use super::line::{if_opener, indent_of, is_global_name, is_ident_char, mentions_ident};

/// The checking calls `/GS` makes, by the names a binary or the analysis
/// gives the checker.
const COOKIE_CHECKERS: [&str; 2] = ["__security_check_cookie", "@__security_check_cookie@4"];

/// What a folded stack protector was and how much of it the text left out.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Folded {
    /// `stack canary` or `/GS cookie`.
    pub(super) what: &'static str,
    /// The slot that held the guard's copy (`local_10`), when the text
    /// named one.
    pub(super) slot: Option<String>,
    /// How many checks left the text.
    pub(super) checks: usize,
    /// The function the checks call, which the text no longer shows.
    pub(super) callee: String,
}

impl Folded {
    /// The header line's text, after `// folded: `: what left, and the
    /// callee whose calls left with it in the words the structure check
    /// reads a left-out call by ([`super::traces`]).
    pub(super) fn note(&self) -> String {
        let s = if self.checks == 1 { "" } else { "s" };
        let slot = self
            .slot
            .as_ref()
            .map_or(String::new(), |l| format!(" in {l}"));
        format!(
            "{}{slot}, {} check{s}; calls to {} are left out (still replayed)",
            self.what, self.checks, self.callee
        )
    }
}

/// Tells whether a value is a stack canary's guard: the thread block's
/// word, a hoisted global or the guard's own symbol.
///
/// # Arguments
///
/// * `v` - The value as the text spells it.
fn is_guard(v: &str) -> bool {
    matches!(
        v,
        "*(uint64_t*)(fs + 0x28)" | "*(uint32_t*)(gs + 0x14)" | "__stack_chk_guard"
    ) || is_global_name(v)
}

/// Tells whether a value is the `/GS` cookie mixed with a frame address,
/// `g64_140014140 ^ &local_dc8`.
///
/// # Arguments
///
/// * `v` - The value as the text spells it.
fn is_cookie(v: &str) -> bool {
    let Some((cookie, frame)) = v.split_once(" ^ ") else {
        return false;
    };
    let frame_slot = frame
        .strip_prefix("&local_")
        .or_else(|| frame.strip_prefix("&arg_"))
        .is_some_and(|h| !h.is_empty() && h.bytes().all(|b| b.is_ascii_hexdigit()));
    frame_slot && (is_global_name(cookie) || cookie == "__security_cookie")
}

/// A `local_N = VALUE;` line's slot and value.
///
/// # Arguments
///
/// * `t` - The line without indentation.
fn slot_store(t: &str) -> Option<(&str, &str)> {
    let (slot, value) = t.strip_suffix(';')?.split_once(" = ")?;
    slot.starts_with("local_").then_some((slot, value))
}

/// Tells whether a line inside a failed check only fails: the call to
/// `__stack_chk_fail`, its result assigned or not, or the jump a call that
/// never returns leaves after it.
///
/// # Arguments
///
/// * `t` - The line without indentation.
fn fails(t: &str) -> bool {
    fail_callee(t).is_some() || t.starts_with("goto *0x") && t.ends_with(';')
}

/// The `__stack_chk_fail` a line calls, its result assigned or not.
///
/// # Arguments
///
/// * `t` - The line without indentation.
pub(super) fn fail_callee(t: &str) -> Option<&str> {
    let call = t.split_once(" = ").map_or(t, |(_, c)| c);
    let (name, _) = call.strip_suffix(");")?.split_once('(')?;
    name.starts_with("__stack_chk_fail").then_some(name)
}

/// What a protector's fold found: the line spans that leave, the line
/// spans that stay one level shallower, and what left.
type Found = (Vec<(usize, usize)>, Vec<(usize, usize)>, Folded);

/// A canary check: the lines it spans, the guard and the slots it names.
struct Check<'l> {
    /// Its first line.
    from: usize,
    /// Its last line.
    to: usize,
    /// The guard it compares.
    guard: &'l str,
    /// The slot it compares the guard with, or stores the guard in on the
    /// way to failing (a setup the lifter sank into the failing path).
    slot: Option<&'l str>,
    /// The function it fails through.
    callee: &'l str,
    /// The lines inside an inverted check, `if (GUARD == local_N) { .. }`
    /// followed by the failing call, which stay one level shallower.
    inside: Option<(usize, usize)>,
}

/// The guard and the slot a condition compares, `GUARD op local_N` or
/// the difference GCC subtracts, `local_N - GUARD op 0`.
///
/// # Arguments
///
/// * `cond` - The condition.
/// * `op` - The comparison, ` != ` or ` == `.
///
/// # Returns
///
/// The guard and the slot, `None` for the slot where the lifter forwarded
/// its value and the guard is compared with itself; `None` when the
/// condition compares no guard.
fn compared<'l>(cond: &'l str, op: &str) -> Option<(&'l str, Option<&'l str>)> {
    let (a, b) = cond.split_once(op)?;
    let (a, b) = match (b, a.split_once(" - ")) {
        ("0", Some(diff)) => diff,
        _ => (a, b),
    };
    match (is_guard(a), is_guard(b)) {
        (true, _) if a == b => Some((a, None)),
        (true, false) => b.starts_with("local_").then_some((a, Some(b))),
        (false, true) => a.starts_with("local_").then_some((b, Some(a))),
        (true, true) | (false, false) => None,
    }
}

/// Returns the canary check an `if` line opens.
///
/// The check compares the guard with its slot ([`compared`]) in a body
/// that only fails and has no `else`; the inverted check is an `if` on
/// the guard's being intact whose body is the function's own and ends in
/// a `return` or a `goto`, and whose closing line the failing call
/// follows.
///
/// # Arguments
///
/// * `lines` - The body.
/// * `at` - The line the `if` may open.
fn check_at<'l>(lines: &[&'l str], at: usize) -> Option<Check<'l>> {
    let line = lines.get(at)?;
    let t = line.trim_start();
    if let Some((cond, then)) = t.strip_prefix("if (").and_then(|r| r.rsplit_once(") "))
        && let Some(callee) = fail_callee(then)
        && let Some((guard, slot)) = compared(cond, " != ")
    {
        return Some(Check {
            from: at,
            to: at,
            guard,
            slot,
            callee,
            inside: None,
        });
    }
    let pad = indent_of(line);
    if let Some((guard, slot)) = compared(if_opener(t)?, " == ") {
        let close =
            (at + 1..lines.len()).find(|&i| lines.get(i).is_some_and(|l| indent_of(l) <= pad))?;
        let fail = close + 1;
        let shut = lines
            .get(close)
            .is_some_and(|l| indent_of(l) == pad && l.trim_start() == "}")
            && lines.get(close.checked_sub(1)?).is_some_and(|l| {
                let last = l.trim_start();
                indent_of(l) == pad + 2 && (last.starts_with("return") || last.starts_with("goto "))
            });
        let failed = lines
            .get(fail)
            .filter(|l| indent_of(l) == pad)
            .and_then(|l| fail_callee(l.trim_start()));
        return failed.filter(|_| shut).map(|callee| Check {
            from: at,
            to: fail,
            guard,
            slot,
            callee,
            inside: Some((at + 1, close - 1)),
        });
    }
    let (guard, mut slot) = compared(if_opener(t)?, " != ")?;
    let mut to = at + 1;
    let mut failed = None;
    while let Some(inner) = lines.get(to) {
        let it = inner.trim_start();
        if indent_of(inner) == pad && it == "}" {
            return failed.map(|callee| Check {
                from: at,
                to,
                guard,
                slot,
                callee,
                inside: None,
            });
        }
        if indent_of(inner) <= pad {
            return None;
        }
        match slot_store(it) {
            Some((s, v)) if v == guard && slot.is_none_or(|x| x == s) => slot = Some(s),
            Some(_) => return None,
            None if fails(it) => failed = failed.or_else(|| fail_callee(it)),
            None => return None,
        }
        to += 1;
    }
    None
}

/// Folds the stack protector out of a function's body.
///
/// The canary's checks are the `if (GUARD != local_N)` blocks that only
/// call `__stack_chk_fail` (or store the guard first, a setup the lifter
/// sank there), and the `if (GUARD == local_N) { .. }` blocks the failing
/// call follows, whose body stays one level shallower; its setups are the
/// lines `local_N = GUARD;`. A return of what GCC's check subtracted,
/// `return local_N - GUARD;`, past the check that it is zero, returns 0. The cookie's
/// checks are the calls to `__security_check_cookie`; its setups the lines
/// `local_N = COOKIE ^ &local_M;`. Checks and setups leave together, and
/// only when the slot is read nowhere else; an `if` left with an empty
/// body by them, whose condition calls nothing, leaves too.
///
/// # Arguments
///
/// * `body` - The function's body, header and declarations apart.
///
/// # Returns
///
/// The body without the protector and what left, or the body as it was
/// and `None`.
pub(super) fn fold(body: &str) -> (String, Option<Folded>) {
    let lines: Vec<&str> = body.lines().collect();
    let found = cookie(&lines).or_else(|| canary(&lines));
    let Some((gone, inside, folded)) = found else {
        return (body.to_owned(), None);
    };
    let kept: Vec<(usize, &str)> = lines
        .iter()
        .enumerate()
        .filter(|(i, _)| !gone.iter().any(|(a, b)| (a..=b).contains(&i)))
        .map(|(i, l)| {
            let deeper = inside.iter().filter(|(a, b)| (a..=b).contains(&&i)).count();
            (
                i,
                (0..deeper).fold(*l, |l, _| l.strip_prefix("  ").unwrap_or(l)),
            )
        })
        .collect();
    let zeroed = |l: &str| -> Option<String> {
        let diff = l.trim_start().strip_prefix("return ")?.strip_suffix(';')?;
        let (a, b) = diff.split_once(" - ")?;
        (Some(a) == folded.slot.as_deref() && is_guard(b))
            .then(|| format!("{}return 0;", &l[..indent_of(l)]))
    };
    let owned: Vec<(usize, String)> = kept
        .iter()
        .map(|(i, l)| (*i, zeroed(l).unwrap_or_else(|| (*l).to_owned())))
        .collect();
    let kept: Vec<(usize, &str)> = owned.iter().map(|(i, l)| (*i, l.as_str())).collect();
    if let Some(slot) = &folded.slot
        && kept.iter().any(|(_, l)| mentions_ident(l, slot))
    {
        return (body.to_owned(), None);
    }
    let mut out = String::with_capacity(body.len());
    for l in drop_emptied_ifs(&kept) {
        out.push_str(l);
        out.push('\n');
    }
    (out, Some(folded))
}

/// The `/GS` cookie's checks and setups, and what folding them leaves out.
///
/// # Arguments
///
/// * `lines` - The body.
fn cookie(lines: &[&str]) -> Option<Found> {
    let mut callees: Vec<&str> = Vec::new();
    let checks: Vec<(usize, usize)> = lines
        .iter()
        .enumerate()
        .filter(|(_, l)| {
            let t = l.trim_start();
            let checker = COOKIE_CHECKERS.iter().find(|c| {
                t.strip_prefix(**c)
                    .is_some_and(|r| r.starts_with('(') && r.ends_with(");"))
            });
            if let Some(c) = checker
                && !callees.contains(c)
            {
                callees.push(c);
            }
            checker.is_some()
        })
        .map(|(i, _)| (i, i))
        .collect();
    if checks.is_empty() {
        return None;
    }
    let slot = lines
        .iter()
        .find_map(|l| slot_store(l.trim_start()).filter(|(_, v)| is_cookie(v)))
        .map(|(s, _)| s);
    let setups = lines.iter().enumerate().filter(|(_, l)| {
        slot_store(l.trim_start()).is_some_and(|(s, v)| Some(s) == slot && is_cookie(v))
    });
    let folded = Folded {
        what: "/GS cookie",
        slot: slot.map(str::to_owned),
        checks: checks.len(),
        callee: callees.join(", "),
    };
    let mut gone = checks;
    gone.extend(setups.map(|(i, _)| (i, i)));
    Some((gone, Vec::new(), folded))
}

/// The stack canary's checks and setups, and what folding them leaves
/// out: every check of the guard the first check compares.
///
/// # Arguments
///
/// * `lines` - The body.
fn canary(lines: &[&str]) -> Option<Found> {
    let mut checks: Vec<Check<'_>> = Vec::new();
    let mut at = 0;
    while at < lines.len() {
        match check_at(lines, at) {
            Some(c) if checks.first().is_none_or(|f| f.guard == c.guard) => {
                at = c.to + 1;
                checks.push(c);
            }
            Some(_) | None => at += 1,
        }
    }
    let first = checks.first()?;
    let guard = first.guard;
    let slot = checks.iter().find_map(|c| c.slot);
    if checks
        .iter()
        .any(|c| c.slot.is_some_and(|s| Some(s) != slot))
    {
        return None;
    }
    let mut gone: Vec<(usize, usize)> = Vec::new();
    let mut inside: Vec<(usize, usize)> = Vec::new();
    for c in &checks {
        match c.inside {
            Some((first, last)) => {
                gone.extend([(c.from, c.from), (last + 1, c.to)]);
                inside.push((first, last));
            }
            None => gone.push((c.from, c.to)),
        }
    }
    gone.extend(
        lines
            .iter()
            .enumerate()
            .filter(|(_, l)| {
                slot_store(l.trim_start()).is_some_and(|(s, v)| Some(s) == slot && v == guard)
            })
            .map(|(i, _)| (i, i)),
    );
    let mut callees: Vec<&str> = Vec::new();
    for c in &checks {
        if !callees.contains(&c.callee) {
            callees.push(c.callee);
        }
    }
    let folded = Folded {
        what: "stack canary",
        slot: slot.map(str::to_owned),
        checks: checks.len(),
        callee: callees.join(", "),
    };
    Some((gone, inside, folded))
}

/// Drops each `if (COND) {` the fold left directly followed by its closing
/// `}`, whose condition calls nothing, so reading it changes nothing; an
/// `if` empty before the fold stays.
///
/// # Arguments
///
/// * `lines` - The kept lines, each with its line number before the fold.
fn drop_emptied_ifs<'a>(lines: &[(usize, &'a str)]) -> Vec<&'a str> {
    let calls = |cond: &str| {
        cond.char_indices().any(|(i, c)| {
            c == '('
                && cond
                    .get(..i)
                    .and_then(|h| h.chars().last())
                    .is_some_and(is_ident_char)
        })
    };
    let mut out: Vec<&str> = Vec::with_capacity(lines.len());
    let mut i = 0;
    while let Some(&(was, line)) = lines.get(i) {
        let emptied = if_opener(line.trim_start()).is_some_and(|c| !calls(c))
            && lines.get(i + 1).is_some_and(|&(next, n)| {
                next > was + 1 && indent_of(n) == indent_of(line) && n.trim_start() == "}"
            });
        if emptied {
            i += 2;
        } else {
            out.push(line);
            i += 1;
        }
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::fold;

    /// A Linux canary's setup and checks leave the text, and the header
    /// says what left.
    #[test]
    fn a_linux_canary_folds() {
        let body = "local_10 = *(uint64_t*)(fs + 0x28);\n\
                    rax = f(&local_14);\n\
                    if (rax == 0) {\n  *a3 = local_14;\n}\n\
                    if (*(uint64_t*)(fs + 0x28) != local_10) {\n  __stack_chk_fail();\n  goto *0x238840;\n}\n\
                    return rax;\n";
        let (out, folded) = fold(body);
        let folded = folded.expect("folds");
        assert_eq!(folded.checks, 1);
        assert!(!out.contains("local_10"), "{out}");
        assert!(!out.contains("__stack_chk_fail"), "{out}");
        assert!(out.contains("return rax;"), "{out}");
        assert_eq!(
            folded.note(),
            "stack canary in local_10, 1 check; calls to __stack_chk_fail are left out (still replayed)"
        );
    }

    /// GCC's check subtracts the guard from its copy and tests the
    /// difference, `local_10 - GUARD != 0`; it folds as the compare does.
    #[test]
    fn a_subtracted_canary_folds() {
        let body = "local_10 = *(uint64_t*)(fs + 0x28);\n\
                    var1 = f(a1);\n\
                    if (local_10 - *(uint64_t*)(fs + 0x28) != 0) {\n  __stack_chk_fail();\n}\n\
                    return var1;\n";
        let (out, folded) = fold(body);
        assert_eq!(folded.map(|f| f.checks), Some(1));
        assert_eq!(out, "var1 = f(a1);\nreturn var1;\n");
    }

    /// Where the failing call is no-return, the structurer writes the
    /// check inverted: the return under `if (GUARD == local_N)` and the
    /// call after it. The return stays, one level shallower.
    #[test]
    fn an_inverted_canary_folds() {
        let body = "local_10 = *(uint64_t*)(fs + 0x28);\n\
                    if (a1 != 0) {\n  var1 = f(a1);\n}\n\
                    if (local_10 - *(uint64_t*)(fs + 0x28) == 0) {\n  return var1;\n}\n\
                    __stack_chk_fail();\n\
                    L_10:\n\
                    return 0;\n";
        let (out, folded) = fold(body);
        assert_eq!(folded.map(|f| f.checks), Some(1));
        assert_eq!(
            out,
            "if (a1 != 0) {\n  var1 = f(a1);\n}\nreturn var1;\nL_10:\nreturn 0;\n"
        );
    }

    /// A function whose result register still holds the checked
    /// difference returns it past the check, where it is zero.
    #[test]
    fn a_returned_difference_reads_as_zero() {
        let body = "local_40 = *(uint64_t*)(fs + 0x28);\n\
                    if (local_40 - *(uint64_t*)(fs + 0x28) != 0) {\n  __stack_chk_fail();\n}\n\
                    return local_40 - *(uint64_t*)(fs + 0x28);\n";
        let (out, folded) = fold(body);
        assert_eq!(folded.map(|f| f.checks), Some(1));
        assert_eq!(out, "return 0;\n");
    }

    /// An inverted check whose body may fall into the failing call is no
    /// check: folding it would run on past the call.
    #[test]
    fn an_inverted_check_that_falls_through_stays() {
        let body = "local_10 = *(uint64_t*)(fs + 0x28);\n\
                    if (local_10 - *(uint64_t*)(fs + 0x28) == 0) {\n  g = 1;\n}\n\
                    __stack_chk_fail();\n";
        assert_eq!(fold(body).1, None);
    }

    /// A check whose slot the lifter forwarded compares the guard with
    /// itself and stores it only on the way to failing; it folds too.
    #[test]
    fn a_forwarded_canary_folds() {
        let body = "if (*(uint64_t*)(fs + 0x28) != *(uint64_t*)(fs + 0x28)) {\n  \
                    local_8 = *(uint64_t*)(fs + 0x28);\n  __stack_chk_fail();\n}\n\
                    return a1 + 1;\n";
        let (out, folded) = fold(body);
        assert_eq!(folded.map(|f| f.checks), Some(1));
        assert_eq!(out, "return a1 + 1;\n");
    }

    /// The `/GS` cookie's setup, each copy the structurer made of it, and
    /// the checker's calls leave the text.
    #[test]
    fn a_gs_cookie_folds() {
        let body = "if (a2 == 0) {\n  local_38 = g64_140014140 ^ &local_dc8;\n  a2 = 2;\n} else {\n  \
                    local_38 = g64_140014140 ^ &local_dc8;\n  a2 = 1;\n}\n\
                    if (a1 == 0) {\n  __security_check_cookie();\n  return 0;\n}\n\
                    __security_check_cookie();\n\
                    return 1;\n";
        let (out, folded) = fold(body);
        assert_eq!(folded.map(|f| f.checks), Some(2));
        assert!(
            !out.contains("security") && !out.contains("local_38"),
            "{out}"
        );
        assert!(
            out.contains("return 0;") && out.contains("return 1;"),
            "{out}"
        );
    }

    /// A slot read anywhere but its checks keeps the whole protector, and
    /// a check that does more than fail is no check.
    #[test]
    fn a_slot_read_elsewhere_keeps_the_text() {
        let read = "local_28 = g64_311a30;\nx0 = f(local_28);\n\
                    if (g64_311a30 != local_28) {\n  x0 = __stack_chk_fail();\n}\nreturn x0;\n";
        assert_eq!(fold(read).1, None);
        let busy = "local_28 = g64_311a30;\n\
                    if (g64_311a30 != local_28) {\n  x0 = __stack_chk_fail();\n  g = 1;\n}\nreturn x0;\n";
        assert_eq!(fold(busy).1, None);
    }

    /// An `if` whose only statement was a check leaves with it.
    #[test]
    fn an_if_emptied_by_a_check_leaves() {
        let body = "local_28 = g64_311a30;\n\
                    if ((uint32_t)x22 != 2) {\n  if (g64_311a30 != local_28) {\n    x0 = __stack_chk_fail();\n  }\n}\n\
                    return 0;\n";
        let (out, folded) = fold(body);
        assert!(folded.is_some());
        assert_eq!(out, "return 0;\n");
    }
}
