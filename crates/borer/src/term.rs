//! What a person at a terminal sees around the CLI's answer: a loading line
//! while a binary loads and analyzes or an update downloads, styled help,
//! and status marks.
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
use std::time::{Duration, Instant};

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

/// The terminal's width in columns, when there is a terminal.
fn terminal_width() -> Option<usize> {
    terminal_size::terminal_size().map(|(w, _)| usize::from(w.0))
}

/// The terminal's width in columns, for wrapping help; 100 off a terminal.
fn width() -> usize {
    terminal_width().unwrap_or(100).max(60)
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
        .as_ref()
        .is_some_and(|b| b.drew.load(Ordering::Relaxed))
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
    /// What the line shows, changed as the work moves on.
    shown: Arc<Mutex<Shown>>,
    /// The drawing thread.
    thread: JoinHandle<()>,
    /// Set once a frame has been written. The clear is that frame's undo.
    drew: Arc<AtomicBool>,
    /// When the line went up, for the time it shows.
    start: Instant,
}

/// What a loading line shows besides its spinner and its time.
#[derive(Debug)]
struct Shown {
    /// What is happening, e.g. `loading notepad.exe`.
    label: String,
    /// The bytes streaming past, as hex pairs.
    hex: Vec<String>,
    /// The bytes done and, when known, all there are, for a bar.
    progress: Option<(u64, Option<u64>)>,
}

/// The spinner's frames.
const SPIN: [char; 10] = ['⠋', '⠙', '⠹', '⠸', '⠼', '⠴', '⠦', '⠧', '⠇', '⠏'];

/// How many of the file's bytes the line streams past at once, at most.
const WINDOW: usize = 14;

/// The cells of a bar.
const BAR: usize = 16;

/// Bytes as hex pairs, for a loading line to stream.
///
/// # Arguments
///
/// * `bytes` - The bytes.
fn hex_pairs(bytes: &[u8]) -> Vec<String> {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

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
    if !show_spinner(std::io::stderr().is_terminal()) {
        return;
    }
    let mut slot = BUSY.lock().unwrap_or_else(PoisonError::into_inner);
    if let Some(b) = slot.as_ref() {
        label.clone_into(&mut b.shown.lock().unwrap_or_else(PoisonError::into_inner).label);
        return;
    }
    #[expect(
        clippy::disallowed_methods,
        reason = "the loading line shows a person how long the work has taken; no answer reads it"
    )]
    let start = Instant::now();
    let done = Arc::new(AtomicBool::new(false));
    let shown = Arc::new(Mutex::new(Shown {
        label: label.to_owned(),
        hex: hex_pairs(bytes),
        progress: None,
    }));
    let drew = Arc::new(AtomicBool::new(false));
    let thread = {
        let done = Arc::clone(&done);
        let shown = Arc::clone(&shown);
        let drew = Arc::clone(&drew);
        std::thread::spawn(move || draw(&done, &shown, start, &drew))
    };
    *slot = Some(Busy {
        done,
        shown,
        thread,
        drew,
        start,
    });
}

/// Shows on the loading line how far its work has come: a bar, a percent
/// and the speed when the total is known, the bytes and speed when not,
/// and the work's newest bytes streaming past.
///
/// # Arguments
///
/// * `done` - The bytes done.
/// * `total` - All there are, when known.
/// * `bytes` - Some of the newest bytes; empty keeps those shown.
pub(crate) fn progress(done: u64, total: Option<u64>, bytes: &[u8]) {
    if let Some(b) = BUSY.lock().unwrap_or_else(PoisonError::into_inner).as_ref() {
        let mut shown = b.shown.lock().unwrap_or_else(PoisonError::into_inner);
        shown.progress = Some((done, total));
        if !bytes.is_empty() {
            shown.hex = hex_pairs(bytes);
        }
    }
}

/// Takes the loading line down and leaves, in its place, `line` with a
/// check or a cross and the time the step took; nothing where no line was
/// up, as off a terminal.
///
/// # Arguments
///
/// * `ok` - Whether the step succeeded.
/// * `line` - What the finished step says.
pub(crate) fn finish(ok: bool, line: &str) {
    let took = BUSY
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .as_ref()
        .map(|b| b.start.elapsed().as_secs_f32());
    stop();
    if let Some(text) = finished(ok, line, took) {
        note(&text);
    }
}

/// The line a finished step leaves: a check or a cross, what it says, and
/// the time it took.
///
/// # Arguments
///
/// * `ok` - Whether the step succeeded.
/// * `line` - What the finished step says.
/// * `took` - The step's time in seconds; `None` when no loading line
///   showed it.
///
/// # Returns
///
/// `None` for a step no loading line showed, so nothing is written where
/// nothing was drawn.
fn finished(ok: bool, line: &str, took: Option<f32>) -> Option<String> {
    took.map(|secs| format!("{}{line}  \x1b[2m{secs:.1}s\x1b[0m", marked(true, ok)))
}

/// A size in megabytes, one decimal.
///
/// # Arguments
///
/// * `bytes` - The size, in bytes.
pub(crate) fn megabytes(bytes: u64) -> String {
    format!("{:.1} MB", borer_engine::num::as_f64(bytes) / 1e6)
}

/// The bar, percent, size and speed of work `done` bytes along, as a
/// loading line shows them.
///
/// # Arguments
///
/// * `done` - The bytes done.
/// * `total` - All there are, when known; without it, no bar or percent.
/// * `secs` - The time so far, in seconds.
fn meter(done: u64, total: Option<u64>, secs: f32) -> String {
    let speed = if secs > 0.0 {
        borer_engine::num::as_f64(done) / 1e6 / f64::from(secs)
    } else {
        0.0
    };
    let Some(total) = total.filter(|&t| t > 0) else {
        return format!(" {}  {speed:.1} MB/s", megabytes(done));
    };
    let done = done.min(total);
    let cells = borer_engine::num::from_usize(BAR);
    let filled = borer_engine::num::saturating_usize(done.saturating_mul(cells) / total);
    let percent = done.saturating_mul(100) / total;
    format!(
        " \x1b[38;5;250m{}\x1b[38;5;238m{}\x1b[0m {percent:>3}%  {:.1}/{}  {speed:.1} MB/s",
        "━".repeat(filled),
        "━".repeat(BAR.saturating_sub(filled)),
        borer_engine::num::as_f64(done) / 1e6,
        megabytes(total)
    )
}

/// The columns `text` takes on a terminal: its characters outside escape
/// sequences, a carriage return aside.
///
/// # Arguments
///
/// * `text` - The text, escape sequences and all.
fn columns(text: &str) -> usize {
    let mut cols = 0;
    let mut escape = false;
    for c in text.chars() {
        if escape {
            escape = !c.is_ascii_alphabetic();
        } else if c == '\x1b' {
            escape = true;
        } else if c != '\r' {
            cols += 1;
        }
    }
    cols
}

/// One frame of the loading line, narrower than `width` so it never
/// wraps: the spinner, the label, the progress when there is some and it
/// fits, as many of the bytes as fit, and the time.
///
/// # Arguments
///
/// * `turn` - The frame's number: it turns the spinner and moves the bytes
///   along.
/// * `shown` - What the line shows.
/// * `secs` - The time so far, in seconds.
/// * `width` - The terminal's width, in columns.
fn frame(turn: usize, shown: &Shown, secs: f32, width: usize) -> String {
    let time = format!(" \x1b[2m{secs:.1}s\x1b[0m");
    let fixed = 3 + columns(&time);
    let meter = shown
        .progress
        .map(|(done, total)| meter(done, total, secs))
        .filter(|m| fixed + columns(m) <= width)
        .unwrap_or_default();
    let room = width.saturating_sub(fixed + columns(&meter));
    let label: String = shown.label.chars().take(room).collect();
    let pairs = (room.saturating_sub(label.chars().count()).saturating_sub(2) / 3).min(WINDOW);
    let mut line = format!(
        "\r\x1b[2K\x1b[38;5;250m{}\x1b[0m {label}{meter}",
        SPIN[turn % SPIN.len()]
    );
    if !shown.hex.is_empty() && pairs > 0 {
        line.push_str("  ");
        for i in 0..pairs {
            let pair = &shown.hex[(turn + i) % shown.hex.len()];
            let shade = 236 + (i * 10 / WINDOW);
            let _ = write!(line, "\x1b[38;5;{shade}m{pair}\x1b[0m ");
        }
    }
    line.push_str(&time);
    line
}

/// Whether the loading line may be drawn.
///
/// `FORCE_COLOR` still colors usage text on a pipe. The loading line is a
/// cursor move, so it stays off unless stderr is a terminal.
///
/// # Arguments
///
/// * `terminal` - Whether stderr is a terminal.
fn show_spinner(terminal: bool) -> bool {
    terminal && styled(terminal)
}

/// Draws frames until told to stop.
///
/// Each frame fits the terminal's own width, read again for every frame so
/// a resize takes effect (80 columns if it cannot be read): no floor, since
/// a frame wider than the terminal wraps, and the next frame clears only
/// the line it is on.
///
/// # Arguments
///
/// * `done` - Set when the line is to go.
/// * `shown` - What the line shows.
/// * `start` - When the line went up.
/// * `drew` - Set after the first frame is written.
fn draw(done: &AtomicBool, shown: &Mutex<Shown>, start: Instant, drew: &AtomicBool) {
    std::thread::sleep(Duration::from_millis(140));
    let mut turn = 0usize;
    while !done.load(Ordering::Relaxed) {
        let line = frame(
            turn,
            &shown.lock().unwrap_or_else(PoisonError::into_inner),
            start.elapsed().as_secs_f32(),
            terminal_width().unwrap_or(80),
        );
        let mut err = std::io::stderr().lock();
        publish_frame(&mut err, line.as_bytes(), drew);
        drop(err);
        turn = turn.wrapping_add(1);
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
    let clear = clear_bytes(b.drew.load(Ordering::Relaxed));
    if clear.is_empty() {
        return;
    }
    let mut err = std::io::stderr().lock();
    let _ = err.write_all(clear);
    let _ = err.flush();
}

/// Writes one frame and records that the write happened.
///
/// The record is stored before this returns, while the caller still holds
/// the stderr lock. A `note` that takes the lock next then sees the frame.
///
/// # Arguments
///
/// * `err` - The locked stderr.
/// * `line` - The frame, including its clear.
/// * `drew` - Set once the frame has been written.
fn publish_frame(err: &mut impl std::io::Write, line: &[u8], drew: &AtomicBool) {
    let _ = err.write_all(line);
    let _ = err.flush();
    drew.store(true, Ordering::Relaxed);
}

/// The bytes that take a drawn frame down. Nothing, when no frame was drawn.
///
/// # Arguments
///
/// * `drew` - Whether a frame reached stderr.
fn clear_bytes(drew: bool) -> &'static [u8] {
    if drew { b"\r\x1b[2K" } else { b"" }
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
    marked(styled_out(), ok)
}

/// A check or a cross for a stream that carries styling, nothing for one
/// that does not.
///
/// # Arguments
///
/// * `styled` - Whether the stream carries styling.
/// * `ok` - Whether the line reports success.
fn marked(styled: bool, ok: bool) -> &'static str {
    match (styled, ok) {
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

#[cfg(test)]
mod tests {
    use super::{
        Shown, WINDOW, clear_bytes, columns, finished, frame, hex_pairs, meter, publish_frame,
        show_spinner,
    };
    use std::sync::atomic::{AtomicBool, Ordering};

    /// No frame is ever as wide as its terminal.
    ///
    /// Where it fits, a loading line keeps its look: the label, a full
    /// window of the bytes and the time. A narrower terminal shows fewer
    /// bytes, then drops the bar, then shortens the label.
    ///
    /// # Panics
    ///
    /// When a frame reads otherwise or would wrap.
    #[test]
    fn a_frame_fits_its_terminal() {
        let shown = Shown {
            label: "loading notepad.exe".to_owned(),
            hex: hex_pairs(b"MZ\x90"),
            progress: None,
        };
        let wide = frame(1, &shown, 0.3, 200);
        assert!(
            wide.starts_with(
                "\r\x1b[2K\x1b[38;5;250m⠙\x1b[0m loading notepad.exe  \x1b[38;5;236m5a\x1b[0m \
                 \x1b[38;5;236m90\x1b[0m \x1b[38;5;237m4d\x1b[0m "
            ),
            "{wide:?}"
        );
        assert!(wide.ends_with("\x1b[0m  \x1b[2m0.3s\x1b[0m"), "{wide:?}");
        assert_eq!(columns(&wide), 2 + 19 + 2 + 3 * WINDOW + 1 + 4);
        let narrow = frame(1, &shown, 0.3, 40);
        assert!(narrow.contains("loading notepad.exe  "), "{narrow:?}");
        assert_eq!(columns(&narrow), 2 + 19 + 2 + 3 * 3 + 1 + 4);
        let download = Shown {
            label: "downloading v0.2.11".to_owned(),
            hex: hex_pairs(b"PK\x03\x04"),
            progress: Some((3_400_000, Some(8_100_000))),
        };
        assert!(frame(0, &download, 2.0, 100).contains("downloading v0.2.11 \x1b[38;5;250m━"));
        assert!(!frame(0, &download, 2.0, 40).contains('%'));
        for width in (12..=200).step_by(7) {
            for shown in [&shown, &download] {
                let line = frame(7, shown, 123.4, width);
                assert!(columns(&line) < width, "{width}: {line:?}");
            }
        }
    }

    /// A bar shows the share done, the percent, all there is and the
    /// speed; work of unknown size shows what is done and the speed.
    ///
    /// # Panics
    ///
    /// When a meter reads otherwise.
    #[test]
    fn a_meter_shows_how_far_a_download_has_come() {
        assert_eq!(
            meter(3_400_000, Some(8_100_000), 2.0),
            format!(
                " \x1b[38;5;250m{}\x1b[38;5;238m{}\x1b[0m  41%  3.4/8.1 MB  1.7 MB/s",
                "━".repeat(6),
                "━".repeat(10)
            )
        );
        let full = format!("{}\x1b[38;5;238m\x1b[0m 100%", "━".repeat(16));
        assert!(meter(9, Some(9), 1.0).contains(&full));
        assert!(meter(10, Some(9), 1.0).contains(&full));
        assert_eq!(meter(2_000_000, None, 4.0), " 2.0 MB  0.5 MB/s");
        assert_eq!(meter(2_000_000, Some(0), 0.0), " 2.0 MB  0.0 MB/s");
    }

    /// A finished step leaves its mark, its line and its time, and a step
    /// no loading line showed leaves nothing.
    ///
    /// # Panics
    ///
    /// When it reads otherwise.
    #[test]
    fn a_finished_step_leaves_a_line_only_where_one_was_drawn() {
        assert_eq!(finished(true, "unpacked", None), None);
        assert_eq!(
            finished(false, "unpacking", Some(1.3)).as_deref(),
            Some("\x1b[38;5;203m✗\x1b[0m unpacking  \x1b[2m1.3s\x1b[0m")
        );
        assert_eq!(
            finished(true, "installed", Some(0.04)).as_deref(),
            Some("\x1b[38;5;114m✓\x1b[0m installed  \x1b[2m0.0s\x1b[0m")
        );
    }

    /// The drawn flag is set after the bytes are written, before the caller
    /// drops the stderr lock.
    ///
    /// # Panics
    ///
    /// When the flag is set before the write, or is still clear afterward.
    #[test]
    fn a_frame_is_marked_drawn_before_the_lock_returns() {
        let drew = AtomicBool::new(false);
        let early = AtomicBool::new(false);
        let mut buf = Vec::new();
        struct Watch<'a> {
            buf: &'a mut Vec<u8>,
            drew: &'a AtomicBool,
            early: &'a AtomicBool,
        }
        impl std::io::Write for Watch<'_> {
            fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
                if self.drew.load(Ordering::Relaxed) {
                    self.early.store(true, Ordering::Relaxed);
                }
                self.buf.extend_from_slice(bytes);
                Ok(bytes.len())
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        publish_frame(
            &mut Watch {
                buf: &mut buf,
                drew: &drew,
                early: &early,
            },
            b"\r\x1b[2Kframe",
            &drew,
        );
        assert!(!early.load(Ordering::Relaxed));
        assert!(drew.load(Ordering::Relaxed));
        assert_eq!(buf, b"\r\x1b[2Kframe");
    }

    /// A pipe stays quiet even when color is forced, and a frame that was
    /// never drawn has nothing to clear.
    ///
    /// # Panics
    ///
    /// When a pipe draws a spinner, or clearing an undrawn line writes.
    #[test]
    fn a_pipe_draws_no_spinner_and_an_undrawn_line_is_not_cleared() {
        assert!(!show_spinner(false));
        assert!(clear_bytes(false).is_empty());
        assert_eq!(clear_bytes(true), b"\r\x1b[2K");
    }
}
