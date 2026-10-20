//! The compiler from a function's statements to the steps the text runs.

use super::*;

/// Turns a function's statements into steps and labels.
pub(super) struct Compiler<'t> {
    /// Each body line's tokens, or why it does not tokenize, by its index
    /// in the whole text.
    pub(super) toks: Vec<Result<Vec<Tok>, String>>,
    /// Tells whether a name holds a value.
    pub(super) values: &'t dyn Fn(&str) -> bool,
    /// Enumerator names from the function's `// enum` header.
    pub(super) enumerators: &'t FxHashMap<String, u64>,
    /// The machine word in bits.
    pub(super) word: u8,
    /// The steps so far.
    pub(super) ops: Vec<Op1>,
    /// Each label's step, once placed.
    pub(super) labels: Vec<Option<usize>>,
    /// The label of each block a `goto` or a `L_x:` names.
    pub(super) blocks: FxHashMap<u64, usize>,
}

impl Compiler<'_> {
    /// A new label, not yet placed.
    fn label(&mut self) -> usize {
        self.labels.push(None);
        self.labels.len() - 1
    }

    /// Places a label at the next step; a label placed already stays.
    ///
    /// # Arguments
    ///
    /// * `l` - The label.
    fn place(&mut self, l: usize) {
        if let Some(slot) = self.labels.get_mut(l)
            && slot.is_none()
        {
            *slot = Some(self.ops.len());
        }
    }

    /// The label of a block.
    ///
    /// # Arguments
    ///
    /// * `addr` - The block's address.
    fn block(&mut self, addr: u64) -> usize {
        if let Some(&l) = self.blocks.get(&addr) {
            return l;
        }
        let l = self.label();
        self.blocks.insert(addr, l);
        l
    }

    /// Adds a step.
    ///
    /// # Arguments
    ///
    /// * `line` - Its 1-based line.
    /// * `step` - The step.
    pub(super) fn emit(&mut self, line: usize, step: Step) {
        self.ops.push(Op1 { line, step });
    }

    /// A line's tokens.
    ///
    /// # Arguments
    ///
    /// * `line` - The 1-based line.
    ///
    /// # Errors
    ///
    /// When the line does not tokenize.
    fn line(&self, line: usize) -> Result<&[Tok], String> {
        match self.toks.get(line.wrapping_sub(1)) {
            Some(Ok(t)) => Ok(t),
            Some(Err(why)) => Err(why.clone()),
            None => Err("a line past the text".to_owned()),
        }
    }

    /// The constant a case label stands for: a literal, or an enumerator
    /// the function's header names.
    ///
    /// # Arguments
    ///
    /// * `e` - The label's expression.
    fn case_value(&self, e: &Ast) -> Option<u64> {
        match e {
            Ast::Name(n) => self.enumerators.get(n).copied(),
            other => constant(other),
        }
    }

    /// Reads an expression out of a line's tokens.
    ///
    /// # Arguments
    ///
    /// * `toks` - The tokens.
    ///
    /// # Errors
    ///
    /// When they do not read as one expression.
    fn expr(&self, toks: &[Tok]) -> Result<Ast, String> {
        expression(toks, self.values, self.word)
    }

    /// The condition of the structure a line opens.
    ///
    /// # Arguments
    ///
    /// * `line` - The 1-based line.
    /// * `word` - The keyword whose group holds it.
    ///
    /// # Errors
    ///
    /// When the line or its condition does not read.
    fn condition(&self, line: usize, word: &str) -> Result<Ast, String> {
        let toks = self.line(line)?;
        let group = group_after(toks, word).ok_or_else(|| format!("no {word} condition"))?;
        self.expr(group)
    }

    /// Adds a step, or the reason it does not read.
    ///
    /// # Arguments
    ///
    /// * `line` - Its 1-based line.
    /// * `step` - The step, or why it does not read.
    fn emit_or(&mut self, line: usize, step: Result<Step, String>) {
        let step = step.unwrap_or_else(Step::Unreadable);
        self.emit(line, step);
    }

    /// Compiles a run of statements.
    ///
    /// # Arguments
    ///
    /// * `stmts` - The statements.
    /// * `brk` - Where `break` goes.
    /// * `cont` - Where `continue` goes.
    pub(super) fn run(&mut self, stmts: &[Stmt], brk: Option<usize>, cont: Option<usize>) {
        for s in stmts {
            self.stmt(s, brk, cont);
        }
    }

    /// Compiles one statement.
    ///
    /// # Arguments
    ///
    /// * `s` - The statement.
    /// * `brk` - Where `break` goes.
    /// * `cont` - Where `continue` goes.
    fn stmt(&mut self, s: &Stmt, brk: Option<usize>, cont: Option<usize>) {
        match s {
            Stmt::Label(addr, _) => {
                let l = self.block(*addr);
                self.place(l);
            }
            Stmt::Plain(line) => {
                let step = self.line(*line).and_then(|toks| {
                    let part = statement_part(toks);
                    let body = part
                        .strip_suffix(&[Tok::Punct(";")])
                        .ok_or("a statement without its `;`")?;
                    if body == [Tok::Name("__asm".to_owned())] {
                        return Err("an instruction left as asm".to_owned());
                    }
                    self.expr(body).map(Step::Eval)
                });
                self.emit_or(*line, step);
            }
            Stmt::Return(line) => {
                let step = self.line(*line).and_then(|toks| {
                    let part = statement_part(toks);
                    let body = part
                        .strip_suffix(&[Tok::Punct(";")])
                        .and_then(|b| b.strip_prefix(&[Tok::Name("return".to_owned())]))
                        .ok_or("a return that does not read")?;
                    if body.is_empty() {
                        Ok(Step::Return(None))
                    } else {
                        self.expr(body).map(|e| Step::Return(Some(e)))
                    }
                });
                self.emit_or(*line, step);
            }
            Stmt::Halt(line) => {
                let jumps = self
                    .line(*line)
                    .is_ok_and(|t| t.contains(&Tok::Name("goto".to_owned())));
                self.emit(*line, if jumps { Step::Leave } else { Step::Halt });
            }
            Stmt::If(line, then, other) => {
                let otherwise = self.label();
                let cond = self.condition(*line, "if");
                self.emit_or(*line, cond.map(|c| Step::Test(c, otherwise)));
                self.run(then, brk, cont);
                if other.is_empty() {
                    self.place(otherwise);
                } else {
                    let end = self.label();
                    self.emit(*line, Step::Jump(end));
                    self.place(otherwise);
                    self.run(other, brk, cont);
                    self.place(end);
                }
            }
            Stmt::Loop(body) => {
                let (top, end) = (self.label(), self.label());
                self.place(top);
                self.run(body, Some(end), Some(top));
                self.emit(self.last_line(), Step::Jump(top));
                self.place(end);
            }
            Stmt::While(line, body) => {
                let (top, end) = (self.label(), self.label());
                self.place(top);
                let cond = self.condition(*line, "while");
                self.emit_or(*line, cond.map(|c| Step::Test(c, end)));
                self.run(body, Some(end), Some(top));
                self.emit(*line, Step::Jump(top));
                self.place(end);
            }
            Stmt::For(line, body) => self.for_loop(*line, body),
            Stmt::Do(body, line) => {
                let (top, test, end) = (self.label(), self.label(), self.label());
                self.place(top);
                self.run(body, Some(end), Some(test));
                self.place(test);
                let cond = self.condition(*line, "while");
                self.emit_or(*line, cond.map(|c| Step::Test(c, end)));
                self.emit(*line, Step::Jump(top));
                self.place(end);
            }
            Stmt::Switch(line, arms) => self.switch(*line, arms, cont),
            Stmt::Try(line, ..) => {
                self.emit(*line, Step::Unreadable("a guarded region".to_owned()));
            }
            Stmt::Goto(addr) => {
                let l = self.block(*addr);
                self.emit(self.last_line(), Step::Jump(l));
            }
            Stmt::Break => self.jump_or(brk, "a stray break"),
            Stmt::Continue => self.jump_or(cont, "a stray continue"),
        }
    }

    /// The line of the last step, for a step that has none of its own.
    fn last_line(&self) -> usize {
        self.ops.last().map_or(0, |o| o.line)
    }

    /// Jumps to a `break` or `continue` target, or stops the run where
    /// there is none.
    ///
    /// # Arguments
    ///
    /// * `to` - The target, if the statement has one.
    /// * `stray` - Why the run stops without one.
    fn jump_or(&mut self, to: Option<usize>, stray: &str) {
        let step = to.map_or_else(|| Step::Unreadable(stray.to_owned()), Step::Jump);
        self.emit(self.last_line(), step);
    }

    /// Compiles a `for` loop.
    ///
    /// # Arguments
    ///
    /// * `line` - The header's line.
    /// * `body` - The body.
    fn for_loop(&mut self, line: usize, body: &[Stmt]) {
        let parts = self.line(line).and_then(|toks| {
            let group = group_after(toks, "for").ok_or("no for header")?;
            let parts = split_top(group, ";");
            let [init, test, step] = parts.as_slice() else {
                return Err("a for header without three parts".to_owned());
            };
            let read = |t: &[Tok]| -> Result<Option<Ast>, String> {
                if t.is_empty() {
                    Ok(None)
                } else {
                    self.expr(t).map(Some)
                }
            };
            Ok((read(init)?, read(test)?, read(step)?))
        });
        let (init, test, step) = match parts {
            Ok(p) => p,
            Err(why) => {
                self.emit(line, Step::Unreadable(why));
                return;
            }
        };
        let (top, next, end) = (self.label(), self.label(), self.label());
        if let Some(i) = init {
            self.emit(line, Step::Eval(i));
        }
        self.place(top);
        if let Some(t) = test {
            self.emit(line, Step::Test(t, end));
        }
        self.run(body, Some(end), Some(next));
        self.place(next);
        if let Some(s) = step {
            self.emit(line, Step::Eval(s));
        }
        self.emit(line, Step::Jump(top));
        self.place(end);
    }

    /// Compiles a `switch`: a dispatch to each arm's label, the arms in
    /// order falling into each other as C's do.
    ///
    /// # Arguments
    ///
    /// * `line` - The line of the value switched on.
    /// * `arms` - Each arm: whether it is the default, its labels' line,
    ///   its body.
    /// * `cont` - Where `continue` goes.
    fn switch(&mut self, line: usize, arms: &[(bool, usize, Vec<Stmt>)], cont: Option<usize>) {
        let end = self.label();
        let mut cases: Vec<(u64, usize)> = Vec::new();
        let mut default = end;
        let mut entries = Vec::with_capacity(arms.len());
        let mut bad: Option<String> = None;
        for (is_default, at, _) in arms {
            let l = self.label();
            entries.push(l);
            if *is_default {
                default = l;
            }
            let toks = match self.line(*at) {
                Ok(t) => t.to_vec(),
                Err(why) => {
                    bad = Some(why);
                    continue;
                }
            };
            let mut rest: &[Tok] = &toks;
            while let Some(Tok::Name(n)) = rest.first() {
                if n == "default" {
                    rest = rest.get(2..).unwrap_or(&[]);
                } else if n == "case" {
                    let colon = rest
                        .iter()
                        .position(|t| *t == Tok::Punct(":"))
                        .unwrap_or(rest.len());
                    match self
                        .expr(rest.get(1..colon).unwrap_or(&[]))
                        .ok()
                        .and_then(|e| self.case_value(&e))
                    {
                        Some(v) => cases.push((v, l)),
                        None => bad = Some("a case label that is not a number".to_owned()),
                    }
                    rest = rest.get(colon + 1..).unwrap_or(&[]);
                } else {
                    break;
                }
            }
        }
        let value = self.condition(line, "switch");
        let step = match (value, bad) {
            (Ok(v), None) => Step::Switch(v, cases, default),
            (Err(why), _) | (_, Some(why)) => Step::Unreadable(why),
        };
        self.emit(line, step);
        for ((_, _, body), l) in arms.iter().zip(entries) {
            self.place(l);
            self.run(body, Some(end), cont);
        }
        self.place(end);
    }
}
