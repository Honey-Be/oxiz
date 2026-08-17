//! SMT-LIB2 command parsing

use super::super::lexer::TokenKind;
use super::{Command, Parser, parse_decimal_to_rational};
use crate::ast::{RoundingMode, TermId};
use crate::error::{OxizError, Result};
#[allow(unused_imports)]
use crate::prelude::*;
#[cfg(feature = "profiling")]
use crate::profiling::{ProfilingCategory, ScopedTimer};
use num_bigint::BigInt;

impl<'a> Parser<'a> {
    /// Expect an opening parenthesis '('
    pub(super) fn expect_lparen(&mut self) -> Result<()> {
        let token = self
            .lexer
            .next_token()
            .ok_or_else(|| OxizError::ParseError {
                position: self.lexer.position(),
                message: "expected '(', found end of input".to_string(),
            })?;

        if !matches!(token.kind, TokenKind::LParen) {
            return Err(OxizError::ParseError {
                position: token.start,
                message: format!("expected '(', found {:?}", token.kind),
            });
        }
        Ok(())
    }

    /// Read a `set-option` VALUE, which the SMT-LIB grammar makes an
    /// `<attribute_value>`: a symbol, a numeral, a decimal, a hex/binary
    /// literal, a string literal, or nothing at all.
    ///
    /// This used to be `expect_symbol().unwrap_or_default()`, and
    /// `expect_symbol` accepts ONLY `TokenKind::Symbol` — so every NUMERIC
    /// option was silently reduced to the empty string. `(set-option :timeout
    /// 5000)`, the standard spelling z3 accepts, set nothing and reported
    /// nothing. The failure is invisible by construction: the option handler
    /// downstream sees a value it cannot interpret and does nothing, which is
    /// indistinguishable from the option not having been written.
    ///
    /// Returns the empty string when the next token is `)` — an option with no
    /// value, which the grammar allows — WITHOUT consuming it, so the caller's
    /// `expect_rparen` still lines up. Any other token is consumed and
    /// rendered, matching the old behaviour's token accounting exactly (the old
    /// code consumed the token even when it rejected it).
    pub(super) fn parse_option_value(&mut self) -> String {
        if matches!(self.lexer.peek().map(|t| t.kind), Some(TokenKind::RParen)) {
            return String::new();
        }
        match self.lexer.next_token().map(|t| t.kind) {
            Some(
                TokenKind::Symbol(s)
                | TokenKind::Numeral(s)
                | TokenKind::Decimal(s)
                | TokenKind::Hexadecimal(s)
                | TokenKind::Binary(s)
                | TokenKind::StringLit(s),
            ) => s,
            Some(TokenKind::Keyword(s)) => format!(":{s}"),
            _ => String::new(),
        }
    }

    /// Expect a symbol token and return its string value
    pub(super) fn expect_symbol(&mut self) -> Result<String> {
        let token = self
            .lexer
            .next_token()
            .ok_or_else(|| OxizError::ParseError {
                position: self.lexer.position(),
                message: "expected symbol, found end of input".to_string(),
            })?;

        match token.kind {
            TokenKind::Symbol(s) => Ok(s),
            _ => Err(OxizError::ParseError {
                position: token.start,
                message: format!("expected symbol, found {:?}", token.kind),
            }),
        }
    }

    /// Expect a keyword token (e.g., :named) and return its string value (without leading colon)
    pub(super) fn expect_keyword(&mut self) -> Result<String> {
        let token = self
            .lexer
            .next_token()
            .ok_or_else(|| OxizError::ParseError {
                position: self.lexer.position(),
                message: "expected keyword, found end of input".to_string(),
            })?;

        match token.kind {
            TokenKind::Keyword(k) => Ok(k),
            _ => Err(OxizError::ParseError {
                position: token.start,
                message: format!("expected keyword, found {:?}", token.kind),
            }),
        }
    }

    /// Expect a string literal token and return its content
    pub(super) fn expect_string(&mut self) -> Result<String> {
        let token = self
            .lexer
            .next_token()
            .ok_or_else(|| OxizError::ParseError {
                position: self.lexer.position(),
                message: "expected string, found end of input".to_string(),
            })?;

        match token.kind {
            TokenKind::StringLit(s) => Ok(s),
            _ => Err(OxizError::ParseError {
                position: token.start,
                message: format!("expected string, found {:?}", token.kind),
            }),
        }
    }

    /// Parse an IEEE 754 rounding mode symbol (RNE, RNA, RTP, RTN, RTZ or long forms)
    pub(super) fn parse_rounding_mode(&mut self) -> Result<RoundingMode> {
        let token = self
            .lexer
            .next_token()
            .ok_or_else(|| OxizError::ParseError {
                position: self.lexer.position(),
                message: "expected rounding mode, found end of input".to_string(),
            })?;

        match &token.kind {
            TokenKind::Symbol(s) => match s.as_str() {
                "RNE" | "roundNearestTiesToEven" => Ok(RoundingMode::RNE),
                "RNA" | "roundNearestTiesToAway" => Ok(RoundingMode::RNA),
                "RTP" | "roundTowardPositive" => Ok(RoundingMode::RTP),
                "RTN" | "roundTowardNegative" => Ok(RoundingMode::RTN),
                "RTZ" | "roundTowardZero" => Ok(RoundingMode::RTZ),
                _ => Err(OxizError::ParseError {
                    position: token.start,
                    message: format!("unknown rounding mode: {}", s),
                }),
            },
            _ => Err(OxizError::ParseError {
                position: token.start,
                message: format!("expected rounding mode symbol, found {:?}", token.kind),
            }),
        }
    }

    /// Parse a single SMT-LIB2 top-level command.
    /// Returns `None` on EOF.
    pub fn parse_command(&mut self) -> Result<Option<Command>> {
        #[cfg(feature = "profiling")]
        let _timer = ScopedTimer::new(ProfilingCategory::Parser);
        let token = match self.lexer.next_token() {
            Some(t) if matches!(t.kind, TokenKind::Eof) => return Ok(None),
            Some(t) => t,
            None => return Ok(None),
        };

        if !matches!(token.kind, TokenKind::LParen) {
            return Err(OxizError::ParseError {
                position: token.start,
                message: format!("expected '(', found {:?}", token.kind),
            });
        }

        let cmd_name = self.expect_symbol()?;

        let cmd = match cmd_name.as_str() {
            "set-logic" => {
                let logic = self.expect_symbol()?;
                self.expect_rparen()?;
                Command::SetLogic(logic)
            }
            "set-option" => {
                let opt = self.expect_keyword()?;
                // option value is optional / may be missing
                let val = self.parse_option_value();
                self.expect_rparen()?;
                Command::SetOption(opt, val)
            }
            "declare-const" => {
                let name = self.expect_symbol()?;
                let sort_id = self.parse_sort()?;
                self.expect_rparen()?;
                self.constants.insert(name.clone(), sort_id);
                let sort_str = self.sort_id_to_string(sort_id);
                Command::DeclareConst(name, sort_str)
            }
            "declare-fun" => {
                let name = self.expect_symbol()?;
                self.expect_lparen()?;
                let mut arg_sorts = Vec::new();
                let mut arg_sort_ids = Vec::new();
                loop {
                    if let Some(t) = self.lexer.peek()
                        && matches!(t.kind, TokenKind::RParen)
                    {
                        self.lexer.next_token();
                        break;
                    }
                    let sort_id = self.parse_sort()?;
                    arg_sort_ids.push(sort_id);
                    arg_sorts.push(self.sort_id_to_string(sort_id));
                }
                let ret_sort_id = self.parse_sort()?;
                let ret_sort = self.sort_id_to_string(ret_sort_id);
                self.expect_rparen()?;

                if arg_sorts.is_empty() {
                    self.constants.insert(name.clone(), ret_sort_id);
                } else {
                    self.functions
                        .insert(name.clone(), (arg_sort_ids.clone(), ret_sort_id));
                }
                Command::DeclareFun(name, arg_sorts, ret_sort)
            }
            "assert" => {
                let term = self.parse_term()?;
                self.expect_rparen()?;
                Command::Assert(term)
            }
            "check-sat" => {
                self.expect_rparen()?;
                Command::CheckSat
            }
            "get-model" => {
                self.expect_rparen()?;
                Command::GetModel
            }
            "get-value" => {
                self.expect_lparen()?;
                let mut terms = Vec::new();
                loop {
                    if let Some(t) = self.lexer.peek()
                        && matches!(t.kind, TokenKind::RParen)
                    {
                        self.lexer.next_token();
                        break;
                    }
                    terms.push(self.parse_term()?);
                }
                self.expect_rparen()?;
                Command::GetValue(terms)
            }
            "push" => {
                let n = self.parse_optional_numeral(1)?;
                self.expect_rparen()?;
                Command::Push(n)
            }
            "pop" => {
                let n = self.parse_optional_numeral(1)?;
                self.expect_rparen()?;
                Command::Pop(n)
            }
            "reset" => {
                self.expect_rparen()?;
                // #424 item 1 follow-up: `(reset)` erases ALL prior
                // declarations per SMT-LIB semantics (`Context::reset`,
                // executed later, mirrors this for the rest of solver
                // state) — but `check_dt_group_no_name_collisions` consults
                // `self.dt_constructors`/`self.dt_selectors` directly, and
                // those maps are otherwise monotonic across an entire
                // parse (both within one `parse_script`/
                // `parse_script_with_env` call, which parses the WHOLE
                // script into a `Vec<Command>` before any command
                // executes, and across separate calls via `ParserEnv`).
                // Without this, two datatypes separated by a `(reset)` that
                // happen to reuse a constructor/selector name are wrongly
                // rejected even though z3/cvc5 both accept them (the reset
                // genuinely makes the two declarations unrelated). Clearing
                // here — the instant `Command::Reset` is produced, so it
                // takes effect before any later command in this same parse
                // call is parsed — closes that false-rejection gap. Scoped
                // to exactly these two maps (not `constants`/`functions`/
                // `sort_aliases`/`function_defs`, which have no analogous
                // duplicate-rejection check and whose cross-reset accrual
                // is pre-existing, unrelated parser behavior, untouched
                // here).
                self.dt_constructors.clear();
                self.dt_selectors.clear();
                Command::Reset
            }
            "reset-assertions" => {
                self.expect_rparen()?;
                Command::ResetAssertions
            }
            "get-assertions" => {
                self.expect_rparen()?;
                Command::GetAssertions
            }
            "get-assignment" => {
                self.expect_rparen()?;
                Command::GetAssignment
            }
            "get-proof" => {
                self.expect_rparen()?;
                Command::GetProof
            }
            "get-unsat-core" => {
                self.expect_rparen()?;
                Command::GetUnsatCore
            }
            "get-option" => {
                let opt = self.expect_keyword()?;
                self.expect_rparen()?;
                Command::GetOption(opt)
            }
            "check-sat-assuming" => {
                self.expect_lparen()?;
                let mut assumptions = Vec::new();
                loop {
                    if let Some(t) = self.lexer.peek()
                        && matches!(t.kind, TokenKind::RParen)
                    {
                        self.lexer.next_token();
                        break;
                    }
                    assumptions.push(self.parse_term()?);
                }
                self.expect_rparen()?;
                Command::CheckSatAssuming(assumptions)
            }
            "simplify" => {
                let term = self.parse_term()?;
                self.expect_rparen()?;
                Command::Simplify(term)
            }
            "exit" => {
                self.expect_rparen()?;
                Command::Exit
            }
            "echo" => {
                let msg = self.expect_string()?;
                self.expect_rparen()?;
                Command::Echo(msg)
            }
            "set-info" => {
                let keyword = self.expect_keyword()?;
                // Peek to decide whether the value is a string literal or a symbol
                // without consuming the token on a failed match.
                let value = if let Some(tok) = self.lexer.peek()
                    && matches!(tok.kind, TokenKind::StringLit(_))
                {
                    self.expect_string()?
                } else {
                    self.expect_symbol()?
                };
                self.expect_rparen()?;
                Command::SetInfo(keyword, value)
            }
            "get-info" => {
                let keyword = self.expect_keyword()?;
                self.expect_rparen()?;
                Command::GetInfo(keyword)
            }
            "define-sort" => {
                // (define-sort name (params) sort-expr)
                let name = self.expect_symbol()?;
                self.expect_lparen()?;
                let mut params = Vec::new();
                loop {
                    if let Some(t) = self.lexer.peek()
                        && matches!(t.kind, TokenKind::RParen)
                    {
                        self.lexer.next_token();
                        break;
                    }
                    params.push(self.expect_symbol()?);
                }
                let sort_expr = self.expect_symbol()?;
                self.expect_rparen()?;

                self.sort_aliases
                    .insert(name.clone(), (params.clone(), sort_expr.clone()));

                Command::DefineSort(name, params, sort_expr)
            }
            "define-fun" => {
                // (define-fun name ((param sort) ...) ret-sort body)
                let name = self.expect_symbol()?;
                self.expect_lparen()?;

                let mut params: Vec<(String, String)> = Vec::new();
                loop {
                    if let Some(t) = self.lexer.peek()
                        && matches!(t.kind, TokenKind::RParen)
                    {
                        self.lexer.next_token();
                        break;
                    }
                    self.expect_lparen()?;
                    let param_name = self.expect_symbol()?;
                    let param_sort_id = self.parse_sort()?;
                    let param_sort = self.sort_id_to_string(param_sort_id);
                    self.expect_rparen()?;
                    params.push((param_name, param_sort));
                }

                let ret_sort_id = self.parse_sort()?;
                let ret_sort = self.sort_id_to_string(ret_sort_id);

                // Save any shadowed bindings
                let old_bindings: Vec<(String, TermId)> = params
                    .iter()
                    .filter_map(|(pname, _)| self.bindings.get(pname).map(|&t| (pname.clone(), t)))
                    .collect();

                // Create placeholder vars for parameters, KEEPING their terms:
                // re-deriving them at each call site from the name alone is the
                // defect `FunctionMacro` exists to remove.
                let mut param_terms = Vec::with_capacity(params.len());
                for (pname, psort) in &params {
                    let sort_id = self.parse_sort_name(psort)?;
                    let param_term = self.manager.mk_var(pname, sort_id);
                    param_terms.push(param_term);
                    self.bindings.insert(pname.clone(), param_term);
                }

                // Parse body
                let body = self.parse_term()?;
                self.expect_rparen()?;

                // Restore old bindings
                for (pname, _) in &params {
                    self.bindings.remove(pname);
                }
                for (pname, term) in old_bindings {
                    self.bindings.insert(pname, term);
                }

                // Register function definition
                self.function_defs.insert(
                    name.clone(),
                    super::FunctionMacro {
                        params: params.clone(),
                        param_terms,
                        body,
                    },
                );

                // For nullary define-fun, inline it directly as a binding
                if params.is_empty() {
                    self.bindings.insert(name.clone(), body);
                }

                Command::DefineFun(name, params, ret_sort, body)
            }
            "declare-datatypes" => self.parse_declare_datatypes()?,
            "declare-datatype" => self.parse_declare_datatype()?,
            "minimize" => {
                let term = self.parse_term()?;
                let (_weight, id) = self.parse_opt_objective_kwargs()?;
                self.expect_rparen()?;
                Command::Minimize { term, id }
            }
            "maximize" => {
                let term = self.parse_term()?;
                let (_weight, id) = self.parse_opt_objective_kwargs()?;
                self.expect_rparen()?;
                Command::Maximize { term, id }
            }
            "assert-soft" => {
                let term = self.parse_term()?;
                let (weight, group) = self.parse_opt_objective_kwargs()?;
                let weight = weight.ok_or_else(|| OxizError::ParseError {
                    position: self.lexer.position(),
                    message: "assert-soft requires a :weight <numeral> argument".to_string(),
                })?;
                self.expect_rparen()?;
                Command::AssertSoft {
                    term,
                    weight,
                    group: group.clone(),
                    id: group,
                }
            }
            "get-objectives" => {
                self.expect_rparen()?;
                Command::GetObjectives
            }
            _ => {
                // Skip unknown command (balanced paren skipping)
                let mut depth = 1;
                while depth > 0 {
                    match self.lexer.next_token().map(|t| t.kind) {
                        Some(TokenKind::LParen) => depth += 1,
                        Some(TokenKind::RParen) => depth -= 1,
                        Some(TokenKind::Eof) | None => break,
                        _ => {}
                    }
                }
                return self.parse_command();
            }
        };

        Ok(Some(cmd))
    }

    /// Parse the trailing `:weight <numeral>` / `:id <symbol>` keyword
    /// arguments shared by `minimize`/`maximize`/`assert-soft`, up to (not
    /// consuming) the command's closing `)`. Mirrors `parse_attributes`'s
    /// keyword-loop shape (peek a `TokenKind::Keyword`, consume it, consume
    /// its value) rather than hand-rolling a new one, but is specialized to
    /// this exact pair since neither value is ever a term/S-expression.
    ///
    /// Returns `(weight, id)`. `minimize`/`maximize` never emit a `:weight`
    /// keyword in a well-formed script and so always get `None` back for
    /// it; `assert-soft` requires one and its caller turns a `None` into a
    /// parse error itself (a missing `:weight` is only an error in THAT
    /// command's context, not this shared helper's).
    fn parse_opt_objective_kwargs(&mut self) -> Result<(Option<TermId>, Option<String>)> {
        let mut weight = None;
        let mut id = None;
        loop {
            let Some(tok) = self.lexer.peek() else {
                break;
            };
            let TokenKind::Keyword(kw) = &tok.kind else {
                break;
            };
            match kw.as_str() {
                "weight" => {
                    self.lexer.next_token();
                    weight = Some(self.parse_numeral_literal_term()?);
                }
                "id" => {
                    self.lexer.next_token();
                    id = Some(self.expect_symbol()?);
                }
                // An unrecognized keyword here is left for `expect_rparen`
                // to report as a clear "expected ')'" error, rather than
                // silently consuming it.
                _ => break,
            }
        }
        Ok((weight, id))
    }

    /// Parse a bare numeral/decimal literal token into a `TermId`, via the
    /// exact same numeral-to-term construction (`mk_int`/`mk_real`) that
    /// `parse_term` uses for a plain `<numeral>`/`<decimal>` token. A MaxSMT
    /// `:weight` value is always one of these two token kinds per the
    /// grammar — never a compound term — so this deliberately does not
    /// delegate to the full `parse_term`.
    fn parse_numeral_literal_term(&mut self) -> Result<TermId> {
        let token = self
            .lexer
            .next_token()
            .ok_or_else(|| OxizError::ParseError {
                position: self.lexer.position(),
                message: "expected a numeral or decimal weight, found end of input".to_string(),
            })?;

        match token.kind {
            TokenKind::Numeral(n) => {
                let value: BigInt = n.parse().map_err(|_| OxizError::ParseError {
                    position: token.start,
                    message: format!("invalid numeral: {n}"),
                })?;
                Ok(self.manager.mk_int(value))
            }
            TokenKind::Decimal(d) => {
                let rational =
                    parse_decimal_to_rational(&d).map_err(|e| OxizError::ParseError {
                        position: token.start,
                        message: format!("invalid decimal: {d} - {e}"),
                    })?;
                Ok(self.manager.mk_real(rational))
            }
            other => Err(OxizError::ParseError {
                position: token.start,
                message: format!("expected a numeral or decimal weight, found {other:?}"),
            }),
        }
    }

    /// Parse an optional numeral from the token stream; return `default` if none present
    fn parse_optional_numeral(&mut self, default: u32) -> Result<u32> {
        if let Some(t) = self.lexer.peek()
            && matches!(t.kind, TokenKind::Numeral(_))
            && let Some(token) = self.lexer.next_token()
            && let TokenKind::Numeral(n) = token.kind
        {
            return n.parse::<u32>().map_err(|_| OxizError::ParseError {
                position: token.start,
                message: format!("invalid numeral: {n}"),
            });
        }
        Ok(default)
    }

    /// Parse `(declare-datatypes (...) (...))` — multi-datatype form
    fn parse_declare_datatypes(&mut self) -> Result<Command> {
        // (declare-datatypes ((name1 arity1) (name2 arity2) ...)
        //                    ((constructors1 ...) (constructors2 ...)))
        self.expect_lparen()?;

        let mut datatype_names = Vec::new();
        loop {
            if let Some(t) = self.lexer.peek()
                && matches!(t.kind, TokenKind::RParen)
            {
                self.lexer.next_token();
                break;
            }

            self.expect_lparen()?;
            let dt_name = self.expect_symbol()?;
            // Skip the arity
            if let Some(t) = self.lexer.peek()
                && matches!(t.kind, TokenKind::Numeral(_))
            {
                self.lexer.next_token();
            }
            self.expect_rparen()?;
            datatype_names.push(dt_name);
        }

        // Parse the constructor-groups list — one group per declared
        // datatype.  adsmt-patch (rc.30): the previous code parsed
        // only the FIRST group then expected the command-closing `)`,
        // so a multi-datatype `(declare-datatypes ((R 0)(L 0)) (g1 g2))`
        // failed with "expected ')', found LParen" at the second
        // group.  Loop over every group and collect each datatype's raw
        // constructor structure so later terms resolve.
        //
        // #418 item 4 (well-foundedness): this pass is deliberately RAW —
        // selector sorts are kept as parsed symbol strings, with NO
        // SortManager/dt_constructors/dt_selectors mutation yet — so that if
        // the well-foundedness gate below rejects the group, no partial
        // registration state is left behind for the rejected declaration.
        self.expect_lparen()?; // outer constructor-groups list

        let mut raw_groups: Vec<Vec<(String, Vec<(String, String)>)>> = Vec::new();
        loop {
            // End of the outer constructor-groups list?
            if let Some(t) = self.lexer.peek()
                && matches!(t.kind, TokenKind::RParen)
            {
                self.lexer.next_token();
                break;
            }

            // This datatype's constructor group.
            self.expect_lparen()?;
            let mut group_ctors: Vec<(String, Vec<(String, String)>)> = Vec::new();
            loop {
                if let Some(t) = self.lexer.peek()
                    && matches!(t.kind, TokenKind::RParen)
                {
                    self.lexer.next_token();
                    break;
                }

                self.expect_lparen()?;
                let ctor_name = self.expect_symbol()?;

                let mut selectors = Vec::new();
                loop {
                    if let Some(t) = self.lexer.peek()
                        && matches!(t.kind, TokenKind::RParen)
                    {
                        self.lexer.next_token();
                        break;
                    }

                    self.expect_lparen()?;
                    let selector_name = self.expect_symbol()?;
                    let selector_sort = self.expect_symbol()?;
                    self.expect_rparen()?;
                    selectors.push((selector_name, selector_sort));
                }

                group_ctors.push((ctor_name, selectors));
            }

            raw_groups.push(group_ctors);
        }

        // Close the outer command list.
        self.expect_rparen()?;

        // #418 item 4 — well-foundedness (strict positivity) check, BEFORE
        // any sort/constructor registration below. z3/cvc5 reject a
        // mutually-recursive group with no reachable base case at
        // declare-time; oxiz must match that (a parse-time rejection, not a
        // silent accept that can make a provably-uninhabited sort report
        // `sat`).
        let position = self.lexer.position();
        Self::check_dt_group_well_founded(position, &datatype_names, &raw_groups)?;

        // #424 item 1 — cross-datatype constructor/selector name collision
        // check, also BEFORE any registration (see the function's doc
        // comment for the full rationale).
        self.check_dt_group_no_name_collisions(position, &raw_groups)?;

        // Pre-create every declared datatype's SORT before resolving the
        // constructor groups' field sorts, so a selector of a MUTUALLY-
        // recursive sibling (or a self-reference) resolves to the datatype
        // sort rather than the uninterpreted fallback (#399).
        for n in &datatype_names {
            let _ = self.manager.sorts.mk_datatype_sort(n);
        }

        let mut constructors: Vec<(String, Vec<(String, String)>)> = Vec::new();
        for (group_idx, group_ctors) in raw_groups.into_iter().enumerate() {
            // Register this datatype's sort + constructors.
            let dt_name = datatype_names
                .get(group_idx)
                .cloned()
                .unwrap_or_else(|| "UnknownDatatype".to_string());
            let dt_sort = self.manager.sorts.mk_datatype_sort(&dt_name);
            for (ctor_name, _selectors) in &group_ctors {
                self.dt_constructors.insert(ctor_name.clone(), dt_sort);
            }
            // #399 — register the full definition (ctor inventory + selector
            // sorts) with the SortManager, so sort-driven datatype reasoning
            // (nullary-ctor exhaustiveness, selector typing) can see it. The
            // pre-created sibling sorts make forward references resolve.
            let mut ctor_defs: Vec<crate::sort::DataTypeConstructor> = Vec::new();
            for (ctor_name, selectors) in &group_ctors {
                let mut sels: smallvec::SmallVec<
                    [(crate::interner::Spur, crate::sort::SortId); 4],
                > = smallvec::SmallVec::new();
                for (field_index, (sel_name, sel_sort)) in selectors.iter().enumerate() {
                    let sid = self.parse_sort_name(sel_sort)?;
                    let sspur = self.manager.sorts.intern_str(sel_name);
                    sels.push((sspur, sid));
                    // An applied selector symbol (e.g. `(hd v)`) must build a
                    // TermKind::DtSelector node, not an opaque Apply — the
                    // same gap 74dd5ae fixed for constructors (#406).
                    self.dt_selectors
                        .insert(sel_name.clone(), (ctor_name.clone(), field_index, sid));
                }
                let cspur = self.manager.sorts.intern_str(ctor_name);
                ctor_defs.push(crate::sort::DataTypeConstructor { name: cspur, selectors: sels });
            }
            self.manager.sorts.declare_datatype(&dt_name, ctor_defs);
            constructors.extend(group_ctors);
        }

        let name = datatype_names
            .first()
            .cloned()
            .unwrap_or_else(|| "UnknownDatatype".to_string());

        Ok(Command::DeclareDatatype { name, constructors })
    }

    /// #418 item 4 — well-foundedness / strict-positivity check for a
    /// `declare-datatypes` mutually-recursive group (or a singular
    /// `declare-datatype`, as the size-1 case). Mirrors the standard
    /// algorithm z3/cvc5 use (equivalent to computing productive/nullable
    /// nonterminals in a grammar, or Coq/Agda "strict positivity"):
    ///
    /// A datatype D (within its declared group) is "founded" if it has at
    /// least one constructor all of whose FIELDS are either (a) not of a
    /// datatype sort belonging to this same group, or (b) of a
    /// group-datatype sort that is ALREADY founded. Fixpoint from
    /// founded = {}, repeatedly adding any datatype that now qualifies,
    /// until no change (monotone, bounded by group size, always
    /// terminates). If any group member is not founded at the fixpoint, the
    /// whole group is rejected.
    ///
    /// `names[i]` is the i-th declared datatype's name; `groups[i]` is its
    /// constructor list as `(ctor_name, [(selector_name, selector_SORT_NAME)])`
    /// — the selector sort is still the RAW parsed symbol string (sort
    /// resolution/registration happens only after this check passes, and
    /// only if it passes), so this needs no SortManager access at all: a
    /// field's sort counts as "a group member" purely by matching one of
    /// `names` textually — a field sort naming some OTHER, already-declared
    /// and hence already-validated, datatype is correctly treated as case
    /// (a) (safe), since it cannot participate in a NEW cycle through this
    /// group.
    fn check_dt_group_well_founded(
        position: usize,
        names: &[String],
        groups: &[Vec<(String, Vec<(String, String)>)>],
    ) -> Result<()> {
        let n = names.len();
        let mut founded = vec![false; n];
        loop {
            let mut changed = false;
            for i in 0..n {
                if founded[i] {
                    continue;
                }
                // `.get(i)` (not `groups[i]`): a malformed script can supply
                // a MISMATCHED number of constructor groups vs. declared
                // names (a separate, unrelated grammar error the rest of the
                // parser already tolerates via `.get()`/fallback names
                // rather than panicking) — a name with no group at all
                // correctly has zero constructors, hence trivially never
                // founds, rather than indexing out of bounds.
                let has_base_ctor = groups.get(i).into_iter().flatten().any(|(_ctor_name, selectors)| {
                    selectors.iter().all(|(_sel_name, sel_sort)| {
                        match names.iter().position(|nm| nm == sel_sort) {
                            // A field whose sort is another (or the same)
                            // datatype IN THIS GROUP is only safe once that
                            // sibling is already founded.
                            Some(j) => founded[j],
                            // Not a member of this recursive group at all (a
                            // base/interpreted sort, or an unrelated,
                            // already-declared — hence already-validated —
                            // datatype) — always safe.
                            None => true,
                        }
                    })
                });
                if has_base_ctor {
                    founded[i] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        let non_founded: Vec<&str> = names
            .iter()
            .zip(founded.iter())
            .filter(|(_, f)| !**f)
            .map(|(nm, _)| nm.as_str())
            .collect();

        if non_founded.is_empty() {
            Ok(())
        } else {
            Err(OxizError::ParseError {
                position,
                message: format!(
                    "non-well-founded datatype declaration: {} — every constructor of every \
                     listed datatype recursively requires a value of a datatype in the same \
                     mutually-recursive group, so no ground (finite/base) value of this sort can \
                     ever be constructed; z3/cvc5 reject this at declaration time",
                    non_founded.join(", ")
                ),
            })
        }
    }

    /// #424 item 1 — cross-datatype constructor/selector name collision
    /// check, mirroring [`check_dt_group_well_founded`]'s "raw
    /// pre-registration structure, check-before-commit" pattern.
    ///
    /// Two independent bugs stack when the same constructor or selector name
    /// is (re)used by a SECOND, different datatype: (a)
    /// `TermManager::intern`'s general cache keys purely on `TermKind`, and
    /// `TermKind::DtConstructor` carries no sort field, so
    /// `mk_dt_constructor("c0", [], sortA)` followed by
    /// `mk_dt_constructor("c0", [], sortB)` collapse to ONE term — `sortB`'s
    /// binding is silently discarded; (b) the parser's own flat
    /// `dt_constructors`/`dt_selectors` maps have no duplicate-name check and
    /// a later `declare-datatype`/`declare-datatypes` silently OVERWRITES an
    /// earlier entry. z3/cvc5 instead accept the bare declaration and only
    /// reject a later AMBIGUOUS bare reference (e.g. `c0` when two sibling
    /// datatypes both declare it), requiring `(as c0 A)` to disambiguate —
    /// oxiz implements no such sort-based overload resolution, so this is
    /// intentionally MORE restrictive: it rejects the declaration itself,
    /// closing both bugs by construction (a rejected declaration never
    /// reaches either `mk_dt_constructor` or the `dt_constructors`/
    /// `dt_selectors` map insertion).
    ///
    /// Checks WITHIN-NAMESPACE only: constructor names are checked against
    /// other constructor names (both `self.dt_constructors` as it stands
    /// before this command, AND every other constructor already seen earlier
    /// in the SAME group/command being processed here), and likewise
    /// selector names against selector names. A constructor name colliding
    /// with an unrelated datatype's SELECTOR name (or vice versa) is
    /// deliberately NOT checked here — that's a separate, pre-existing
    /// routing quirk in `terms.rs`'s selector-before-constructor lookup
    /// order, out of scope for this check.
    ///
    /// Must be called strictly BEFORE any registration
    /// (`SortManager`/`dt_constructors`/`dt_selectors`/`TermManager`) happens
    /// for the current command, exactly like the well-foundedness check —
    /// re-registering partial state on a later rejection would defeat the
    /// purpose of checking at all.
    fn check_dt_group_no_name_collisions(
        &self,
        position: usize,
        groups: &[Vec<(String, Vec<(String, String)>)>],
    ) -> Result<()> {
        let mut seen_ctors: FxHashSet<&str> = FxHashSet::default();
        let mut seen_sels: FxHashSet<&str> = FxHashSet::default();

        for group in groups {
            for (ctor_name, selectors) in group {
                if self.dt_constructors.contains_key(ctor_name.as_str())
                    || seen_ctors.contains(ctor_name.as_str())
                {
                    return Err(OxizError::ParseError {
                        position,
                        message: format!(
                            "duplicate datatype constructor name: '{ctor_name}' is already \
                             used by a previously declared datatype (or earlier in this same \
                             declaration) — oxiz does not support sort-based overload \
                             resolution for ambiguous bare constructor references, so \
                             cross-datatype constructor name reuse is rejected at \
                             declaration time"
                        ),
                    });
                }
                seen_ctors.insert(ctor_name.as_str());

                for (sel_name, _sel_sort) in selectors {
                    if self.dt_selectors.contains_key(sel_name.as_str())
                        || seen_sels.contains(sel_name.as_str())
                    {
                        return Err(OxizError::ParseError {
                            position,
                            message: format!(
                                "duplicate datatype selector name: '{sel_name}' is already \
                                 used by a previously declared datatype (or earlier in this \
                                 same declaration) — oxiz does not support sort-based overload \
                                 resolution for ambiguous bare selector references, so \
                                 cross-datatype selector name reuse is rejected at declaration \
                                 time"
                            ),
                        });
                    }
                    seen_sels.insert(sel_name.as_str());
                }
            }
        }

        Ok(())
    }

    /// Parse `(declare-datatype name (...))` — single-datatype form
    fn parse_declare_datatype(&mut self) -> Result<Command> {
        let name = self.expect_symbol()?;
        self.expect_lparen()?;

        let mut constructors = Vec::new();
        loop {
            if let Some(t) = self.lexer.peek()
                && matches!(t.kind, TokenKind::RParen)
            {
                self.lexer.next_token();
                break;
            }

            self.expect_lparen()?;
            let ctor_name = self.expect_symbol()?;

            let mut selectors = Vec::new();
            loop {
                if let Some(t) = self.lexer.peek()
                    && matches!(t.kind, TokenKind::RParen)
                {
                    self.lexer.next_token();
                    break;
                }

                self.expect_lparen()?;
                let selector_name = self.expect_symbol()?;
                let selector_sort = self.expect_symbol()?;
                self.expect_rparen()?;
                selectors.push((selector_name, selector_sort));
            }

            constructors.push((ctor_name, selectors));
        }

        self.expect_rparen()?;

        // #418 item 4 — well-foundedness check (a single self-recursive
        // datatype is just a mutually-recursive group of size 1: it must
        // have at least one constructor with no field of its own sort,
        // reachable without going through any OTHER not-yet-founded
        // group member — trivially itself here). Runs BEFORE any
        // sort/constructor registration below, so a rejection leaves no
        // partial state behind.
        let position = self.lexer.position();
        Self::check_dt_group_well_founded(
            position,
            std::slice::from_ref(&name),
            std::slice::from_ref(&constructors),
        )?;

        // #424 item 1 — cross-datatype constructor/selector name collision
        // check, also BEFORE any registration (see the function's doc
        // comment for the full rationale).
        self.check_dt_group_no_name_collisions(position, std::slice::from_ref(&constructors))?;

        let dt_sort = self.manager.sorts.mk_datatype_sort(&name);
        for (ctor_name, _selectors) in &constructors {
            self.dt_constructors.insert(ctor_name.clone(), dt_sort);
        }
        // #399 — register the full definition with the SortManager (see the
        // plural form for the rationale).
        let mut ctor_defs: Vec<crate::sort::DataTypeConstructor> = Vec::new();
        for (ctor_name, selectors) in &constructors {
            let mut sels: smallvec::SmallVec<
                [(crate::interner::Spur, crate::sort::SortId); 4],
            > = smallvec::SmallVec::new();
            for (field_index, (sel_name, sel_sort)) in selectors.iter().enumerate() {
                let sid = self.parse_sort_name(sel_sort)?;
                let sspur = self.manager.sorts.intern_str(sel_name);
                sels.push((sspur, sid));
                // See the plural-form handler for the rationale (#406).
                self.dt_selectors
                    .insert(sel_name.clone(), (ctor_name.clone(), field_index, sid));
            }
            let cspur = self.manager.sorts.intern_str(ctor_name);
            ctor_defs.push(crate::sort::DataTypeConstructor { name: cspur, selectors: sels });
        }
        self.manager.sorts.declare_datatype(&name, ctor_defs);

        Ok(Command::DeclareDatatype { name, constructors })
    }
}
