//! Arithmetic contents `$((..))` / `((..))` (`ShellCheck.Parser` readArithmeticContents family).
use super::*;

impl Parser {
    /// `spacing` local to arithmetic: many (whitespace | "\\\n").
    pub(super) fn arith_spacing(&mut self) {
        loop {
            let m = self.mark();
            if self.string("\\\n").is_ok() {
                continue;
            }
            self.reset(m);
            if self.whitespace().is_ok() {
                continue;
            }
            break;
        }
    }

    /// `readComboOp op token`: match one of `ops` (atomic), require it not be
    /// followed by another op char (`failIfIncompleteOp`), give it a span-only
    /// id, then eat trailing spacing. Returns `(id, matched-op)`.
    pub(super) fn arith_read_combo_op(&mut self, ops: &[&str]) -> PResult<(Id, String)> {
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
        let op = match matched {
            Some(o) => o,
            None => {
                self.reset(outer);
                return Err(());
            }
        };
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        Ok((id, op))
    }

    /// `readMinusOp`: binary `-`, but warn (SC1106) for `-lt`/`-gt`/&c.
    pub(super) fn arith_read_minus_op(&mut self) -> PResult<(Id, String)> {
        let start = self.pos();
        let pos = self.pos();
        let outer = self.mark();
        // try (char '-' >> failIfIncompleteOp)
        if self.char('-').is_err() {
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
                pos.clone(),
                pos,
                Severity::ErrorC,
                1106,
                &format!("In arithmetic contexts, use {} instead of -{}", alt, s),
            );
        }
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        Ok((id, "-".to_string()))
    }

    /// Generic `splitBy sub ops = chainl1 sub (readBinary ops)` producing
    /// left-associated `TA_Binary` nodes.
    pub(super) fn arith_split_by(
        &mut self,
        sub: fn(&mut Self) -> PResult<Token>,
        ops: &[&str],
    ) -> PResult<Token> {
        let mut x = sub(self)?;
        loop {
            let m = self.mark();
            match self.arith_read_combo_op(ops) {
                Ok((id, op)) => {
                    // op consumed: term is now required (Parsec propagates failure)
                    let y = sub(self)?;
                    x = Token::new(id, InnerToken::TA_Binary { op, lhs: x, rhs: y });
                }
                Err(()) => {
                    self.reset(m);
                    break;
                }
            }
        }
        Ok(x)
    }

    /// Entry point: `readArithmeticContents = readSequence`.
    pub(super) fn read_arithmetic_contents(&mut self) -> PResult<Token> {
        self.read_arith_sequence()
    }

    /// `readSequence`: comma-separated assignments -> `TA_Sequence`.
    pub(super) fn read_arith_sequence(&mut self) -> PResult<Token> {
        self.arith_spacing();
        let start = self.pos();
        let mut list = Vec::new();
        let m = self.mark();
        match self.read_arith_assignment() {
            Ok(first) => {
                list.push(first);
                // many (char ',' >> spacing >> readAssignment)
                loop {
                    let mm = self.mark();
                    if self.char(',').is_ok() {
                        self.arith_spacing();
                        // sepBy1's inner is `sep >> p`; if sep consumed then p
                        // fails, Parsec propagates the failure.
                        let t = self.read_arith_assignment()?;
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
    pub(super) fn read_arith_assignment(&mut self) -> PResult<Token> {
        let x = self.read_arith_trinary()?;
        let m = self.mark();
        match self.arith_read_combo_op(&[
            "=", "*=", "/=", "%=", "+=", "-=", "<<=", ">>=", "&=", "^=", "|=",
        ]) {
            Ok((id, op)) => {
                // chainr1: right-recurse
                let y = self.read_arith_assignment()?;
                Ok(Token::new(
                    id,
                    InnerToken::TA_Assignment { op, lhs: x, rhs: y },
                ))
            }
            Err(()) => {
                self.reset(m);
                Ok(x)
            }
        }
    }

    /// `readTrinary` (?:) -> `TA_Trinary`.
    pub(super) fn read_arith_trinary(&mut self) -> PResult<Token> {
        let x = self.read_arith_logical_or()?;
        let m = self.mark();
        let start = self.pos();
        if self.string("?").is_ok() {
            self.arith_spacing();
            let y = self.read_arith_trinary()?;
            // string ":" — required
            if self.string(":").is_err() {
                // consumed input; propagate failure faithfully
                return Err(());
            }
            self.arith_spacing();
            let z = self.read_arith_trinary()?;
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

    pub(super) fn read_arith_logical_or(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_logical_and, &["||"])
    }
    pub(super) fn read_arith_logical_and(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_bit_or, &["&&"])
    }
    pub(super) fn read_arith_bit_or(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_bit_xor, &["|"])
    }
    pub(super) fn read_arith_bit_xor(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_bit_and, &["^"])
    }
    pub(super) fn read_arith_bit_and(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_equated, &["&"])
    }
    pub(super) fn read_arith_equated(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_compared, &["==", "!="])
    }
    pub(super) fn read_arith_compared(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_shift, &["<=", ">=", "<", ">"])
    }
    pub(super) fn read_arith_shift(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_addition, &["<<", ">>"])
    }

    /// `readAddition = chainl1 readMultiplication (readBinary ["+"] <|> readMinusOp)`.
    pub(super) fn read_arith_addition(&mut self) -> PResult<Token> {
        let mut x = self.read_arith_multiplication()?;
        loop {
            let m = self.mark();
            // try "+" combo op, else minus op
            let opres = match self.arith_read_combo_op(&["+"]) {
                Ok(r) => Some(r),
                Err(()) => {
                    self.reset(m);
                    match self.arith_read_minus_op() {
                        Ok(r) => Some(r),
                        Err(()) => {
                            self.reset(m);
                            None
                        }
                    }
                }
            };
            match opres {
                Some((id, op)) => {
                    let y = self.read_arith_multiplication()?;
                    x = Token::new(id, InnerToken::TA_Binary { op, lhs: x, rhs: y });
                }
                None => break,
            }
        }
        Ok(x)
    }

    pub(super) fn read_arith_multiplication(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_exponential, &["*", "/", "%"])
    }
    pub(super) fn read_arith_exponential(&mut self) -> PResult<Token> {
        self.arith_split_by(Self::read_arith_any_negated, &["**"])
    }

    /// `readAnyNegated = readNegated <|> readAnySigned`.
    /// `readAnyNegated = readNegated <|> readAnySigned`, a bare alternation.
    pub(super) fn read_arith_any_negated(&mut self) -> PResult<Token> {
        let m = self.mark();
        match self.read_arith_negated() {
            Ok(t) => Ok(t),
            Err(()) if self.idx != m.idx => Err(()),
            Err(()) => {
                self.reset(m);
                self.read_arith_any_signed()
            }
        }
    }

    /// `readNegated`: `! | ~` prefix -> `TA_Unary`.
    pub(super) fn read_arith_negated(&mut self) -> PResult<Token> {
        let start = self.pos();
        let op = self.one_of("!~")?;
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        let x = self.read_arith_any_negated()?;
        Ok(Token::new(
            id,
            InnerToken::TA_Unary {
                op: op.to_string(),
                operand: x,
            },
        ))
    }

    /// `readAnySigned = readSigned <|> readAnycremented`.
    pub(super) fn read_arith_any_signed(&mut self) -> PResult<Token> {
        let m = self.mark();
        match self.read_arith_signed() {
            Ok(t) => Ok(t),
            Err(()) if self.idx != m.idx => Err(()),
            Err(()) => {
                self.reset(m);
                self.read_arith_anycremented()
            }
        }
    }

    /// `readSigned`: unary `+`/`-` (not `++`/`--`) -> `TA_Unary`.
    pub(super) fn read_arith_signed(&mut self) -> PResult<Token> {
        let start = self.pos();
        let outer = self.mark();
        let mut got: Option<char> = None;
        for c in ['+', '-'] {
            let m = self.mark();
            if self.char(c).is_ok() {
                // notFollowedBy2 (char c)
                if self.peek() != Some(c) {
                    self.arith_spacing();
                    got = Some(c);
                    break;
                }
            }
            self.reset(m);
        }
        let op = match got {
            Some(c) => c,
            None => {
                self.reset(outer);
                return Err(());
            }
        };
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        let x = self.read_arith_anycremented()?;
        Ok(Token::new(
            id,
            InnerToken::TA_Unary {
                op: op.to_string(),
                operand: x,
            },
        ))
    }

    /// `readAnycremented = readNormalOrPostfixIncremented <|> readPrefixIncremented`.
    pub(super) fn read_arith_anycremented(&mut self) -> PResult<Token> {
        let m = self.mark();
        match self.read_arith_normal_or_postfix() {
            Ok(t) => Ok(t),
            Err(()) if self.idx != m.idx => Err(()),
            Err(()) => {
                self.reset(m);
                self.read_arith_prefix_incremented()
            }
        }
    }

    /// `readPrefixIncremented`: `++x`/`--x` -> `TA_Unary` with op `"++|"`/`"--|"`.
    pub(super) fn read_arith_prefix_incremented(&mut self) -> PResult<Token> {
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
        self.arith_spacing();
        let x = self.read_arith_term()?;
        Ok(Token::new(
            id,
            InnerToken::TA_Unary {
                op: format!("{}|", op),
                operand: x,
            },
        ))
    }

    /// `readNormalOrPostfixIncremented`: term, optional trailing `++`/`--`
    /// -> `TA_Unary` with op `"|++"`/`"|--"`.
    pub(super) fn read_arith_normal_or_postfix(&mut self) -> PResult<Token> {
        let x = self.read_arith_term()?;
        self.arith_spacing();
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
                self.arith_spacing();
                Ok(Token::new(
                    id,
                    InnerToken::TA_Unary {
                        op: format!("|{}", op),
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
    pub(super) fn read_arith_term(&mut self) -> PResult<Token> {
        let m = self.mark();
        match self.read_arith_group() {
            Ok(t) => return Ok(t),
            Err(()) if self.idx != m.idx => return Err(()),
            Err(()) => self.reset(m),
        }
        match self.read_arith_variable() {
            Ok(t) => return Ok(t),
            Err(()) if self.idx != m.idx => return Err(()),
            Err(()) => self.reset(m),
        }
        self.read_arith_expansion()
    }

    /// `readGroup`: `( sequence )` -> `TA_Parenthesis`.
    pub(super) fn read_arith_group(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('(')?;
        let s = self.read_arith_sequence()?;
        self.char(')')?;
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        Ok(Token::new(id, InnerToken::TA_Parenthesis(s)))
    }

    /// `readVariable`: name + array indices -> `TA_Variable`.
    pub(super) fn read_arith_variable(&mut self) -> PResult<Token> {
        let start = self.pos();
        let name = self.read_variable_name()?;
        let mut indices = Vec::new();
        // `many readArrayIndex`: an index that failed past its `[` fails the
        // variable, and everything above it.
        loop {
            let m = self.mark();
            match self.read_arith_array_index() {
                Ok(t) => indices.push(t),
                Err(()) if self.idx != m.idx => return Err(()),
                Err(()) => {
                    self.reset(m);
                    break;
                }
            }
        }
        let id = self.next_id_between(start, self.pos());
        self.arith_spacing();
        Ok(Token::new(id, InnerToken::TA_Variable { name, indices }))
    }

    /// `readArrayIndex` (arithmetic-local): `[ arith ]` -> `T_UnparsedIndex`
    /// storing the source position and the raw text, read through
    /// `readStringForParser readArithmeticContents` -- so what the inner parse
    /// reported is forgotten, and when it fails, the frames it opened are put
    /// back before the failure goes on: `((a[\`` names the `((..))` command,
    /// not the backtick.
    pub(super) fn read_arith_array_index(&mut self) -> PResult<Token> {
        let start = self.pos();
        self.char('[')?;
        let pos = self.pos();
        let raw = self.read_string_for_parser(|p| p.read_arithmetic_contents().map(|_| ()))?;
        self.char(']')?;
        let id = self.next_id_between(start, self.pos());
        Ok(Token::new(
            id,
            InnerToken::T_UnparsedIndex { pos, str: raw },
        ))
    }

    /// `readExpansion`: `$`-expansions / quotes / literals -> `TA_Expansion`.
    pub(super) fn read_arith_expansion(&mut self) -> PResult<Token> {
        let start = self.pos();
        let mut pieces = Vec::new();
        loop {
            let m = self.mark();
            let piece = match self.peek() {
                Some('\'') => self.read_single_quoted(),
                Some('"') => self.read_double_quoted(),
                Some('$') => self.read_normal_dollar(),
                Some('`') => self.read_backticked(false),
                Some('{') => self.read_braced(),
                Some('#') => {
                    let s = self.pos();
                    self.bump();
                    let lid = self.next_id_between(s, self.pos());
                    Ok(Token::new(lid, InnerToken::T_Literal("#".to_string())))
                }
                _ => self.read_normal_literal("+-*/=%^,]?:"),
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
        self.arith_spacing();
        Ok(Token::new(id, InnerToken::TA_Expansion(pieces)))
    }
}
