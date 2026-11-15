//! Arithmetic contents `$((..))` / `((..))` (`ShellCheck.Parser` readArithmeticContents family).
use super::{Id, InnerToken, PResult, Parser, Severity, Token};
use reblessive::Stk;

impl Parser {
    /// `spacing` local to arithmetic: many (whitespace | "\\\n").
    pub(super) async fn arith_spacing(&mut self, stk: &mut Stk) {
        loop {
            let m = self.mark();
            if self.string("\\\n").is_ok() {
                continue;
            }
            self.reset(m);
            if self.whitespace(stk).await.is_ok() {
                continue;
            }
            break;
        }
    }

    /// `readComboOp op token`: match one of `ops` (atomic), require it not be
    /// followed by another op char (`failIfIncompleteOp`), give it a span-only
    /// id, then eat trailing spacing. Returns `(id, matched-op)`.
    pub(super) async fn arith_read_combo_op(
        &mut self,
        stk: &mut Stk,
        ops: &[&str],
    ) -> PResult<(Id, String)> {
        let start = self.pos();
        let outer = self.mark();
        let mut matched: Option<String> = None;
        for op in ops {
            let m = self.mark();
            // Each alternative is its own `try`: `string "<="` reads the `<` of
            // `<<<` before refusing the `=`, and the rewind must bring back the
            // error that stood before it -- the one the `<<` attempt left past
            // the third `<` -- which the reading had dropped.
            let saved = self.failure.clone();
            if self.string(op).is_ok() {
                // `failIfIncompleteOp = notFollowedBy2 (oneOf "&|<>=")`, and
                // `unexpecting` reads the character before it fails: `p|&`
                // reports "Unexpected " past the `&`, from inside the `try`.
                if !matches!(self.peek(), Some(c) if "&|<>=".contains(c)) {
                    matched = Some((*op).to_string());
                    break;
                }
                self.fail_past(1, "Unexpected ");
            }
            self.reset(m);
            self.restore_failure(saved);
        }
        let Some(op) = matched else {
            self.reset(outer);
            return Err(());
        };
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing(stk).await;
        Ok((id, op))
    }

    /// Recover a pasted Unicode dash as minus while retaining an error.
    fn arith_unicode_minus(&mut self) -> bool {
        if !self.peek().is_some_and(|c| "֊־‐‑‒–—―﹣－−".contains(c)) {
            return false;
        }
        let start = self.pos();
        self.bump();
        self.problem_at(
            start,
            self.pos(),
            Severity::ErrorC,
            1100,
            "This is a unicode dash. Delete and retype as ASCII minus.",
        );
        true
    }

    /// `readMinusOp`: binary `-`, but warn (SC1106) for `-lt`/`-gt`/&c.
    pub(super) async fn arith_read_minus_op(&mut self, stk: &mut Stk) -> PResult<(Id, String)> {
        let start = self.pos();
        let pos = self.pos();
        let outer = self.mark();
        // try (char '-' >> failIfIncompleteOp)
        if !self.arith_unicode_minus() && self.char('-').is_err() {
            self.reset(outer);
            return Err(());
        }
        if matches!(self.peek(), Some(c) if "&|<>=".contains(c)) {
            // `failIfIncompleteOp` again: "Unexpected " one past the character.
            self.fail_past(1, "Unexpected ");
            self.reset(outer);
            return Err(());
        }
        // optional lookAhead: -lt/-gt/... -> SC1106
        let look = self.mark();
        let alts = [
            ("lt", "<"),
            ("gt", ">"),
            ("le", "<="),
            ("ge", ">="),
            ("eq", "=="),
            ("ne", "!="),
        ];
        let mut found: Option<(&str, &str)> = None;
        for (s, alt) in alts {
            let m = self.mark();
            if self.string(s).is_ok() && self.spacing1().is_ok() {
                found = Some((s, alt));
                self.reset(m);
                break;
            }
            self.reset(m);
        }
        self.reset(look);
        if let Some((s, alt)) = found {
            self.problem_at(
                pos,
                pos,
                Severity::ErrorC,
                1106,
                &format!("In arithmetic contexts, use {alt} instead of -{s}"),
            );
        }
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing(stk).await;
        Ok((id, "-".to_string()))
    }

    /// Generic `splitBy sub ops = chainl1 sub (readBinary ops)` producing
    /// left-associated `TA_Binary` nodes.
    pub(super) async fn arith_split_by(
        &mut self,
        stk: &mut Stk,
        sub: impl AsyncFn(&mut Self, &mut Stk) -> PResult<Token>,
        ops: &[&str],
    ) -> PResult<Token> {
        let mut x = sub(self, stk).await?;
        loop {
            let m = self.mark();
            if let Ok((id, op)) = self.arith_read_combo_op(stk, ops).await {
                // op consumed: term is now required (Parsec propagates failure)
                let y = sub(self, stk).await?;
                x = Token::new(id, InnerToken::TA_Binary { op, lhs: x, rhs: y });
            } else {
                self.reset(m);
                break;
            }
        }
        Ok(x)
    }

    /// Entry point: `readArithmeticContents = readSequence`.
    pub(super) async fn read_arithmetic_contents(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.read_arith_sequence(stk).await
    }

    /// `readSequence`: comma-separated assignments -> `TA_Sequence`.
    pub(super) async fn read_arith_sequence(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_spacing(stk).await;
        let start = self.pos();
        let mut list = Vec::new();
        let m = self.mark();
        match self.read_arith_assignment(stk).await {
            Ok(first) => {
                list.push(first);
                // many (char ',' >> spacing >> readAssignment)
                loop {
                    let mm = self.mark();
                    if self.char(',').is_ok() {
                        self.arith_spacing(stk).await;
                        // sepBy1's inner is `sep >> p`; if sep consumed then p
                        // fails, Parsec propagates the failure.
                        let t = self.read_arith_assignment(stk).await?;
                        list.push(t);
                    } else {
                        self.reset(mm);
                        break;
                    }
                }
            }
            // `readAssignment `sepBy` ..`: none at all is fine, but only when
            // the attempt consumed nothing.
            Err(()) if self.idx != m.idx => return Err(()),
            Err(()) => {
                self.reset(m);
            }
        }
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(id, InnerToken::TA_Sequence(list)))
    }

    /// `readAssignment = chainr1 readTrinary readAssignmentOp` -> `TA_Assignment`.
    pub(super) async fn read_arith_assignment(&mut self, stk: &mut Stk) -> PResult<Token> {
        let x = self.read_arith_trinary(stk).await?;
        let m = self.mark();
        if let Ok((id, op)) = self
            .arith_read_combo_op(
                stk,
                &[
                    "=", "*=", "/=", "%=", "+=", "-=", "<<=", ">>=", "&=", "^=", "|=",
                ],
            )
            .await
        {
            // chainr1: right-recurse
            let y = stk.run(|stk| self.read_arith_assignment(stk)).await?;
            Ok(Token::new(
                id,
                InnerToken::TA_Assignment { op, lhs: x, rhs: y },
            ))
        } else {
            self.reset(m);
            Ok(x)
        }
    }

    /// `readTrinary` (?:) -> `TA_Trinary`.
    pub(super) async fn read_arith_trinary(&mut self, stk: &mut Stk) -> PResult<Token> {
        // Each precedence level below waits on the next one. The levels
        // between here and an operand are too many for one future. This call
        // splits them, and so do the steps from shifts to additions and from
        // products to powers.
        let x = stk.run(|stk| self.read_arith_logical_or(stk)).await?;
        let m = self.mark();
        let start = self.pos();
        if self.string("?").is_ok() {
            self.arith_spacing(stk).await;
            let y = stk.run(|stk| self.read_arith_trinary(stk)).await?;
            // string ":" — required
            if self.string(":").is_err() {
                // consumed input; propagate failure faithfully
                return Err(());
            }
            self.arith_spacing(stk).await;
            let z = stk.run(|stk| self.read_arith_trinary(stk)).await?;
            let id = self.next_id_between(start, self.pos());
            Ok(Token::new(
                id,
                InnerToken::TA_Trinary {
                    cond: x,
                    then: y,
                    els: z,
                },
            ))
        } else {
            self.reset(m);
            Ok(x)
        }
    }

    pub(super) async fn read_arith_logical_or(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_split_by(
            stk,
            async |p, stk| p.read_arith_logical_and(stk).await,
            &["||"],
        )
        .await
    }
    pub(super) async fn read_arith_logical_and(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_split_by(stk, async |p, stk| p.read_arith_bit_or(stk).await, &["&&"])
            .await
    }
    pub(super) async fn read_arith_bit_or(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_split_by(stk, async |p, stk| p.read_arith_bit_xor(stk).await, &["|"])
            .await
    }
    pub(super) async fn read_arith_bit_xor(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_split_by(stk, async |p, stk| p.read_arith_bit_and(stk).await, &["^"])
            .await
    }
    pub(super) async fn read_arith_bit_and(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_split_by(stk, async |p, stk| p.read_arith_equated(stk).await, &["&"])
            .await
    }
    pub(super) async fn read_arith_equated(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_split_by(
            stk,
            async |p, stk| p.read_arith_compared(stk).await,
            &["==", "!="],
        )
        .await
    }
    pub(super) async fn read_arith_compared(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_split_by(
            stk,
            async |p, stk| p.read_arith_shift(stk).await,
            &["<=", ">=", "<", ">"],
        )
        .await
    }
    pub(super) async fn read_arith_shift(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_split_by(
            stk,
            async |p, stk| stk.run(|stk| p.read_arith_addition(stk)).await,
            &["<<", ">>"],
        )
        .await
    }

    /// `readAddition = chainl1 readMultiplication (readBinary ["+"] <|> readMinusOp)`.
    pub(super) async fn read_arith_addition(&mut self, stk: &mut Stk) -> PResult<Token> {
        let mut x = self.read_arith_multiplication(stk).await?;
        loop {
            let m = self.mark();
            // try "+" combo op, else minus op
            let opres = if let Ok(op) = self.arith_read_combo_op(stk, &["+"]).await {
                Some(op)
            } else {
                self.reset(m);
                let op = self.arith_read_minus_op(stk).await.ok();
                if op.is_none() {
                    self.reset(m);
                }
                op
            };
            match opres {
                Some((id, op)) => {
                    let y = self.read_arith_multiplication(stk).await?;
                    x = Token::new(id, InnerToken::TA_Binary { op, lhs: x, rhs: y });
                }
                None => break,
            }
        }
        Ok(x)
    }

    pub(super) async fn read_arith_multiplication(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_split_by(
            stk,
            async |p, stk| stk.run(|stk| p.read_arith_exponential(stk)).await,
            &["*", "/", "%"],
        )
        .await
    }
    pub(super) async fn read_arith_exponential(&mut self, stk: &mut Stk) -> PResult<Token> {
        self.arith_split_by(
            stk,
            async |p, stk| p.read_arith_any_negated(stk).await,
            &["**"],
        )
        .await
    }

    /// `readAnyNegated = readNegated <|> readAnySigned`.
    /// `readAnyNegated = readNegated <|> readAnySigned`, a bare alternation.
    pub(super) async fn read_arith_any_negated(&mut self, stk: &mut Stk) -> PResult<Token> {
        let m = self.mark();
        match self.read_arith_negated(stk).await {
            Ok(t) => Ok(t),
            Err(()) if self.idx != m.idx => Err(()),
            Err(()) => {
                self.reset(m);
                self.read_arith_any_signed(stk).await
            }
        }
    }

    /// `readNegated`: `! | ~` prefix -> `TA_Unary`.
    pub(super) async fn read_arith_negated(&mut self, stk: &mut Stk) -> PResult<Token> {
        let start = self.pos();
        let op = self.one_of("!~")?;
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing(stk).await;
        let x = stk.run(|stk| self.read_arith_any_negated(stk)).await?;
        Ok(Token::new(
            id,
            InnerToken::TA_Unary {
                op: op.to_string(),
                operand: x,
            },
        ))
    }

    /// `readAnySigned = readSigned <|> readAnycremented`.
    pub(super) async fn read_arith_any_signed(&mut self, stk: &mut Stk) -> PResult<Token> {
        let m = self.mark();
        match self.read_arith_signed(stk).await {
            Ok(t) => Ok(t),
            Err(()) if self.idx != m.idx => Err(()),
            Err(()) => {
                self.reset(m);
                self.read_arith_anycremented(stk).await
            }
        }
    }

    /// `readSigned`: unary `+`/`-` (not `++`/`--`) -> `TA_Unary`.
    pub(super) async fn read_arith_signed(&mut self, stk: &mut Stk) -> PResult<Token> {
        let start = self.pos();
        let outer = self.mark();
        let mut got = self.arith_unicode_minus().then_some('-');
        for c in ['+', '-'] {
            if got.is_some() {
                break;
            }
            let m = self.mark();
            if self.char(c).is_ok() {
                // notFollowedBy2 (char c)
                if self.peek() != Some(c) {
                    self.arith_spacing(stk).await;
                    got = Some(c);
                    break;
                }
            }
            self.reset(m);
        }
        let Some(op) = got else {
            self.reset(outer);
            return Err(());
        };
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing(stk).await;
        let x = self.read_arith_anycremented(stk).await?;
        Ok(Token::new(
            id,
            InnerToken::TA_Unary {
                op: op.to_string(),
                operand: x,
            },
        ))
    }

    /// `readAnycremented = readNormalOrPostfixIncremented <|> readPrefixIncremented`.
    pub(super) async fn read_arith_anycremented(&mut self, stk: &mut Stk) -> PResult<Token> {
        let m = self.mark();
        match self.read_arith_normal_or_postfix(stk).await {
            Ok(t) => Ok(t),
            Err(()) if self.idx != m.idx => Err(()),
            Err(()) => {
                self.reset(m);
                self.read_arith_prefix_incremented(stk).await
            }
        }
    }

    /// `readPrefixIncremented`: `++x`/`--x` -> `TA_Unary` with op `"++|"`/`"--|"`.
    pub(super) async fn read_arith_prefix_incremented(&mut self, stk: &mut Stk) -> PResult<Token> {
        let start = self.pos();
        let m = self.mark();
        let op = if self.string("++").is_ok() {
            "++"
        } else {
            self.reset(m);
            if self.string("--").is_ok() {
                "--"
            } else {
                self.reset(m);
                return Err(());
            }
        };
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing(stk).await;
        let x = self.read_arith_term(stk).await?;
        Ok(Token::new(
            id,
            InnerToken::TA_Unary {
                op: format!("{op}|"),
                operand: x,
            },
        ))
    }

    /// `readNormalOrPostfixIncremented`: term, optional trailing `++`/`--`
    /// -> `TA_Unary` with op `"|++"`/`"|--"`.
    pub(super) async fn read_arith_normal_or_postfix(&mut self, stk: &mut Stk) -> PResult<Token> {
        let x = self.read_arith_term(stk).await?;
        self.arith_spacing(stk).await;
        let start = self.pos();
        let m = self.mark();
        let op = if self.string("++").is_ok() {
            Some("++")
        } else {
            self.reset(m);
            if self.string("--").is_ok() {
                Some("--")
            } else {
                self.reset(m);
                None
            }
        };
        match op {
            Some(op) => {
                let id = self.next_id_between(start, self.pos());
                self.arith_spacing(stk).await;
                Ok(Token::new(
                    id,
                    InnerToken::TA_Unary {
                        op: format!("|{op}"),
                        operand: x,
                    },
                ))
            }
            None => Ok(x),
        }
    }

    /// `readArithTerm = readGroup <|> readVariable <|> readExpansion`: bare
    /// alternations, so an alternative that consumed before failing -- a
    /// variable whose index never closes -- leaves the rest out of reach.
    pub(super) async fn read_arith_term(&mut self, stk: &mut Stk) -> PResult<Token> {
        let m = self.mark();
        match self.read_arith_group(stk).await {
            Ok(t) => return Ok(t),
            Err(()) if self.idx != m.idx => return Err(()),
            Err(()) => self.reset(m),
        }
        match self.read_arith_variable(stk).await {
            Ok(t) => return Ok(t),
            Err(()) if self.idx != m.idx => return Err(()),
            Err(()) => self.reset(m),
        }
        // Word parsing below this point is deep. `stk.run` starts it on a
        // fresh future.
        stk.run(|stk| self.read_arith_expansion(stk)).await
    }

    /// `readGroup`: `( sequence )` -> `TA_Parenthesis`.
    pub(super) async fn read_arith_group(&mut self, stk: &mut Stk) -> PResult<Token> {
        let start = self.pos();
        self.char('(')?;
        let s = stk.run(|stk| self.read_arith_sequence(stk)).await?;
        self.char(')')?;
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing(stk).await;
        Ok(Token::new(id, InnerToken::TA_Parenthesis(s)))
    }

    /// `readVariable`: name + array indices -> `TA_Variable`.
    pub(super) async fn read_arith_variable(&mut self, stk: &mut Stk) -> PResult<Token> {
        let start = self.pos();
        let name = self.read_variable_name()?;
        let mut indices = Vec::new();
        // `many readArrayIndex`: an index that failed past its `[` fails the
        // variable, and everything above it.
        loop {
            let m = self.mark();
            match self.read_arith_array_index(stk).await {
                Ok(t) => indices.push(t),
                Err(()) if self.idx != m.idx => return Err(()),
                Err(()) => {
                    self.reset(m);
                    break;
                }
            }
        }
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing(stk).await;
        Ok(Token::new(id, InnerToken::TA_Variable { name, indices }))
    }

    /// `readArrayIndex` (arithmetic-local): `[ arith ]` -> `T_UnparsedIndex`
    /// storing the source position and the raw text, read through
    /// `readStringForParser readArithmeticContents` -- so what the inner parse
    /// reported is forgotten, and when it fails, the frames it opened are put
    /// back before the failure goes on: `` ((a[` `` names the `((..))` command,
    /// not the backtick.
    pub(super) async fn read_arith_array_index(&mut self, stk: &mut Stk) -> PResult<Token> {
        let start = self.pos();
        self.char('[')?;
        let pos = self.pos();
        let raw = self
            .read_string_for_parser(stk, async |p, stk| {
                p.read_arithmetic_contents(stk).await.map(|_| ())
            })
            .await?;
        self.char(']')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_UnparsedIndex {
                pos: self.file_pos(pos),
                str: raw,
            },
        ))
    }

    /// `readExpansion`: `$`-expansions / quotes / literals -> `TA_Expansion`.
    pub(super) async fn read_arith_expansion(&mut self, stk: &mut Stk) -> PResult<Token> {
        let start = self.pos();
        let mut pieces = Vec::new();
        loop {
            let m = self.mark();
            let piece = match self.peek() {
                Some('\'') => self.read_single_quoted(stk).await,
                Some('"') => self.read_double_quoted(stk).await,
                Some('$') => self.read_normal_dollar(stk).await,
                Some('`') => self.read_backticked(stk, false).await,
                Some('{') => self.read_braced(stk).await,
                Some('#') => {
                    let s = self.pos();
                    self.bump();
                    let lid = self.next_id_between(s, self.pos());
                    Ok(Token::new(lid, InnerToken::T_Literal("#".to_string())))
                }
                _ => {
                    self.read_normal_literal(stk, "+-*/=%^,]?:֊־‐‑‒–—―﹣－−")
                        .await
                }
            };
            match piece {
                Ok(t) => pieces.push(t),
                // `many1 $ choice [..]`: a piece that failed after consuming --
                // a backtick with no closing one -- takes the expansion, and
                // the whole arithmetic expression, down with it.
                Err(()) if self.idx != m.idx => return Err(()),
                Err(()) => {
                    self.reset(m);
                    break;
                }
            }
        }
        if pieces.is_empty() {
            return Err(());
        }
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing(stk).await;
        Ok(Token::new(id, InnerToken::TA_Expansion(pieces)))
    }
}
