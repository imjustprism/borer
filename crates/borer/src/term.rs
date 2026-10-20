//! What a person at a terminal sees around the CLI's answer: a loading line
//! while a binary loads and analyzes, styled help, and status marks.
//!
//! None of it reaches the answer. The answer collects in [`out`] and is
//! written to stdout once, by [`flush`], after the loading line is cleared,
//! so its bytes are the same whether a person or an agent runs the command.
//! The loading line and the styling are drawn only on an interactive
//! terminal, and never when `NO_COLOR` is set or `TERM` is `dumb`; piped or
//! run by an agent, borer prints exactly what it always did.

use std::fmt::Write as _;
use std::io::{IsTerminal as _, Write as _};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::thread::JoinHandle;
use std::time::Duration;

/// The answer as it collects, written by [`flush`].
static OUT: Mutex<String> = Mutex::new(String::new());

/// The loading line, while one is drawn.
static BUSY: Mutex<Option<Busy>> = Mutex::new(None);

/// Whether a stream may carry styling: a terminal, with no request for
/// plain text.
///
/// # Arguments
///
/// * `terminal` - Whether the stream is a terminal.
fn styled(terminal: bool) -> bool {
    let set = |name: &str| std::env::var_os(name).is_some_and(|v| !v.is_empty() && v != "0");
    if set("NO_COLOR") {
        return false;
    }
    if set("FORCE_COLOR") || set("CLICOLOR_FORCE") {
        return true;
    }
    terminal && std::env::var("TERM").map_or(true, |t| t != "dumb")
}

/// The terminal's width in columns, for wrapping help; 100 off a terminal.
fn width() -> usize {
    terminal_size::terminal_size()
        .map_or(100, |(w, _)| usize::from(w.0))
        .max(60)
}

/// Words joined into lines no wider than `width`, each after the first
/// starting at `indent` columns.
///
/// # Arguments
///
/// * `text` - The text.
/// * `first` - The columns the first line already uses.
/// * `indent` - Where the following lines start.
/// * `width` - The widest a line may be.
fn wrap(text: &str, first: usize, indent: usize, width: usize) -> Vec<String> {
    let mut lines = vec![String::new()];
    let mut col = first;
    for word in text.split(' ').filter(|w| !w.is_empty()) {
        let n = word.chars().count();
        let line = lines.last_mut().map_or(0, |l| l.chars().count());
        if line > 0 && col + 1 + n > width {
            lines.push(String::new());
            col = indent;
        }
        if let Some(l) = lines.last_mut() {
            if !l.is_empty() {
                l.push(' ');
                col += 1;
            }
            l.push_str(word);
            col += n;
        }
    }
    lines
}

/// Whether stdout is a person's terminal.
pub(crate) fn styled_out() -> bool {
    styled(std::io::stdout().is_terminal())
}

/// Whether stderr is a person's terminal.
pub(crate) fn styled_err() -> bool {
    styled(std::io::stderr().is_terminal())
}

/// Adds to the answer; the CLI's `print!` and `println!` land here.
///
/// # Arguments
///
/// * `text` - What the command printed.
pub(crate) fn out(text: std::fmt::Arguments<'_>) {
    let mut buf = OUT.lock().unwrap_or_else(PoisonError::into_inner);
    let _ = buf.write_fmt(text);
}

/// Clears the loading line and writes the answer to stdout in one piece.
pub(crate) fn flush() {
    stop();
    let text = std::mem::take(&mut *OUT.lock().unwrap_or_else(PoisonError::into_inner));
    if text.is_empty() {
        return;
    }
    let mut stdout = std::io::stdout().lock();
    let _ = stdout.write_all(text.as_bytes());
    let _ = stdout.flush();
}

/// Writes a line to stderr without tearing the loading line: it is cleared
/// first and redrawn on its next frame.
///
/// # Arguments
///
/// * `line` - The line, without its newline.
pub(crate) fn note(line: &str) {
    let mut err = std::io::stderr().lock();
    if BUSY
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .is_some()
    {
        let _ = write!(err, "\r\x1b[2K");
    }
    let _ = writeln!(err, "{line}");
}

/// A drawn loading line: the thread that draws it and what it says.
#[derive(Debug)]
struct Busy {
    /// Set to stop the drawing thread.
    done: Arc<AtomicBool>,
    /// What the line says, changed as the work moves on.
    label: Arc<Mutex<String>>,
    /// The drawing thread.
    thread: JoinHandle<()>,
}

/// The spinner's frames.
const SPIN: [char; 10] = ['⠋', '⠙', '⠹', '⠸', '⠼', '⠴', '⠦', '⠧', '⠇', '⠏'];

/// How many of the file's bytes the line streams past at once.
const WINDOW: usize = 14;

/// Shows, or relabels, the loading line on a terminal: a spinner, what is
/// happening, the file's own bytes streaming past, and the time so far.
///
/// It first draws after a short pause, so work that finishes at once never
/// flashes a line.
///
/// # Arguments
///
/// * `label` - What is happening, e.g. `loading notepad.exe`.
/// * `bytes` - Some of the file's bytes to stream; empty for none.
pub(crate) fn busy(label: &str, bytes: &[u8]) {
    if !styled_err() {
        return;
    }
    let mut slot = BUSY.lock().unwrap_or_else(PoisonError::into_inner);
    if let Some(b) = slot.as_ref() {
        label.clone_into(&mut b.label.lock().unwrap_or_else(PoisonError::into_inner));
        return;
    }
    let done = Arc::new(AtomicBool::new(false));
    let shown = Arc::new(Mutex::new(label.to_owned()));
    let hex: Vec<String> = bytes.iter().map(|b| format!("{b:02x}")).collect();
    let thread = {
        let done = Arc::clone(&done);
        let shown = Arc::clone(&shown);
        std::thread::spawn(move || draw(&done, &shown, &hex))
    };
    *slot = Some(Busy {
        done,
        label: shown,
        thread,
    });
}

/// Draws frames until told to stop.
///
/// # Arguments
///
/// * `done` - Set when the line is to go.
/// * `label` - What the line says.
/// * `hex` - The bytes to stream, as hex pairs.
fn draw(done: &AtomicBool, label: &Mutex<String>, hex: &[String]) {
    #[expect(
        clippy::disallowed_methods,
        reason = "the loading line shows a person how long the work has taken; no answer reads it"
    )]
    let start = std::time::Instant::now();
    std::thread::sleep(Duration::from_millis(140));
    let mut frame = 0usize;
    while !done.load(Ordering::Relaxed) {
        let text = label.lock().unwrap_or_else(PoisonError::into_inner).clone();
        let mut line = format!(
            "\r\x1b[2K\x1b[38;5;250m{}\x1b[0m {text}",
            SPIN[frame % SPIN.len()]
        );
        if !hex.is_empty() {
            line.push_str("  ");
            for i in 0..WINDOW {
                let pair = &hex[(frame + i) % hex.len()];
                let shade = 236 + (i * 10 / WINDOW);
                let _ = write!(line, "\x1b[38;5;{shade}m{pair}\x1b[0m ");
            }
        }
        let _ = write!(line, " \x1b[2m{:.1}s\x1b[0m", start.elapsed().as_secs_f32());
        let mut err = std::io::stderr().lock();
        let _ = err.write_all(line.as_bytes());
        let _ = err.flush();
        drop(err);
        frame = frame.wrapping_add(1);
        std::thread::sleep(Duration::from_millis(70));
    }
}

/// Takes the loading line down, if one is up.
pub(crate) fn stop() {
    let Some(b) = BUSY.lock().unwrap_or_else(PoisonError::into_inner).take() else {
        return;
    };
    b.done.store(true, Ordering::Relaxed);
    let _ = b.thread.join();
    let mut err = std::io::stderr().lock();
    let _ = err.write_all(b"\r\x1b[2K");
    let _ = err.flush();
}

/// The usage text styled for a terminal: section headings bold, command
/// names bright, their arguments soft, and their descriptions dim and
/// wrapped to the terminal's width under one column.
///
/// # Arguments
///
/// * `usage` - The usage text, as [`crate::cli`] keeps it.
pub(crate) fn paint_usage(usage: &str) -> String {
    /// The column descriptions start at, as the usage text aligns them.
    const DESC: usize = 43;
    let width = width();
    let mut out = String::with_capacity(usage.len() * 2);
    for line in usage.lines() {
        if !line.starts_with(' ') {
            let _ = writeln!(out, "\x1b[1m{line}\x1b[0m");
            continue;
        }
        let body = line.trim_start();
        let indent = line.len() - body.len();
        let (head, desc) = body.split_once("  ").unwrap_or((body, ""));
        let (word, rest) = head.split_once(' ').unwrap_or((head, ""));
        let _ = write!(out, "{}\x1b[1m{word}\x1b[0m", " ".repeat(indent));
        if !rest.is_empty() {
            let _ = write!(out, " \x1b[38;5;246m{rest}\x1b[0m");
        }
        let desc = desc.trim_start();
        if !desc.is_empty() {
            let used = indent + head.chars().count();
            let start = if used + 2 > DESC {
                out.push('\n');
                0
            } else {
                used
            };
            out.push_str(&" ".repeat(DESC - start));
            for (i, part) in wrap(desc, DESC, DESC, width).iter().enumerate() {
                if i > 0 {
                    let _ = write!(out, "\n{}", " ".repeat(DESC));
                }
                let _ = write!(out, "\x1b[2m{part}\x1b[0m");
            }
        }
        out.push('\n');
    }
    out
}

/// A status mark for a line meant for a person: a check or a cross on a
/// terminal, nothing otherwise.
///
/// # Arguments
///
/// * `ok` - Whether the line reports success.
pub(crate) fn mark(ok: bool) -> &'static str {
    match (styled_out(), ok) {
        (false, _) => "",
        (true, true) => "\x1b[38;5;114m✓\x1b[0m ",
        (true, false) => "\x1b[38;5;203m✗\x1b[0m ",
    }
}

/// What `borer` alone says at a terminal: what it is, how agents start it,
/// and the commands a person reaches for first.
pub(crate) fn welcome() -> String {
    /// The commands a person reaches for first, with what each does.
    const FIRST: [(&str, &str); 5] = [
        (
            "borer setup --apply",
            "register borer with every MCP client found",
        ),
        (
            "borer info <binary>",
            "what a file is: format, arch, sections, symbols",
        ),
        (
            "borer decompile <binary> <fn>",
            "pseudo-C of a function, checked against the binary",
        ),
        ("borer update", "install the latest release"),
        ("borer help", "every command"),
    ];
    let (b, d, r) = if styled_out() {
        ("\x1b[1m", "\x1b[2m", "\x1b[0m")
    } else {
        ("", "", "")
    };
    let version = crate::doctor::version();
    let mut out = format!(
        "{b}borer{r} {d}{version}{r}  reverse engineering, rebuilt for AI agents\n\n\
         borer is an MCP server: your agent starts it over stdin and stdout.\n\n"
    );
    for (command, what) in FIRST {
        let _ = writeln!(out, "  {b}{command:<31}{r} {d}{what}{r}");
    }
    let _ = writeln!(out, "\n{d}docs: https://borer.lol/docs{r}");
    out
}
