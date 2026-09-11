//! Port of `ShellCheck.AST`.
//!
//! The Haskell AST is `newtype Id = Id Int` and
//! `data Token = OuterToken Id (InnerToken Token)`, where `InnerToken` derives
//! `Functor`/`Foldable`/`Traversable` over its child-token parameter. Here
//! `InnerToken` holds `Token` children directly and `Token` boxes its inner to
//! break the type cycle. Generic traversal is provided by [`Token::children`]
//! and the `visit_*`/`transform` helpers instead of derived typeclasses.
//!
//! IMPORTANT: Haskell defines `instance Eq Token` to compare **only the inner
//! token, ignoring the Id**. Structural checks rely on this. We reproduce it
//! with a hand-written `PartialEq` on `Token`.

/// `newtype Id = Id Int`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id(pub i32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quoted {
    Quoted,
    Unquoted,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dashed {
    Dashed,
    Undashed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Piped {
    Piped,
    Unpiped,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignmentMode {
    Assign,
    Append,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaseType {
    CaseBreak,
    CaseFallThrough,
    CaseContinue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConditionType {
    DoubleBracket,
    SingleBracket,
}

/// `ShellCheck.AST.Annotation`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Annotation {
    /// `DisableComment from to` — half-open range `[from, to)`.
    DisableComment(i64, i64),
    EnableComment(String),
    SourceOverride(String),
    ShellOverride(String),
    SourcePath(String),
    ExternalSources(bool),
    ExtendedAnalysis(bool),
}

/// One `(CaseType, patterns, body)` clause of a case expression.
pub type CaseClause = (CaseType, Vec<Token>, Vec<Token>);

/// A `(conditions, body)` clause of an if/elif chain.
pub type IfClause = (Vec<Token>, Vec<Token>);

/// `data Token = OuterToken Id (InnerToken Token)`.
///
/// Equality ignores `id` (see module docs).
#[derive(Debug, Clone)]
pub struct Token {
    pub id: Id,
    pub inner: Box<InnerToken>,
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        // Mirrors `instance Eq Token where OuterToken _ a == OuterToken _ b = a == b`
        self.inner == other.inner
    }
}
impl Eq for Token {}

impl Token {
    pub fn new(id: Id, inner: InnerToken) -> Token {
        Token { id, inner: Box::new(inner) }
    }

    /// `getId`.
    #[inline]
    pub fn id(&self) -> Id {
        self.id
    }

    #[inline]
    pub fn inner(&self) -> &InnerToken {
        &self.inner
    }
}

/// The inner token payload. Mirrors `InnerToken t` with `t = Token`.
///
/// Variant order matches the Haskell `data InnerToken` declaration order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InnerToken {
    // --- Arithmetic (TA_*) ---
    TA_Binary { op: String, lhs: Token, rhs: Token },
    TA_Assignment { op: String, lhs: Token, rhs: Token },
    TA_Variable { name: String, indices: Vec<Token> },
    TA_Expansion(Vec<Token>),
    TA_Sequence(Vec<Token>),
    TA_Parenthesis(Token),
    TA_Trinary { cond: Token, then: Token, els: Token },
    TA_Unary { op: String, operand: Token },

    // --- Test conditions (TC_*) ---
    TC_And { typ: ConditionType, op: String, lhs: Token, rhs: Token },
    TC_Binary { typ: ConditionType, op: String, lhs: Token, rhs: Token },
    TC_Group { typ: ConditionType, token: Token },
    TC_Nullary { typ: ConditionType, token: Token },
    TC_Or { typ: ConditionType, op: String, lhs: Token, rhs: Token },
    TC_Unary { typ: ConditionType, op: String, token: Token },
    TC_Empty { typ: ConditionType },

    // --- Operator / keyword leaves ---
    T_AND_IF,
    T_AndIf { lhs: Token, rhs: Token },
    T_Arithmetic(Token),
    T_Array(Vec<Token>),
    T_IndexedElement { indices: Vec<Token>, value: Token },
    /// Index stored as string, parsed later as arithmetic or string.
    T_UnparsedIndex { pos: crate::interface::Position, str: String },
    T_Assignment { mode: AssignmentMode, var: String, indices: Vec<Token>, value: Token },
    T_Backgrounded(Token),
    T_Backticked(Vec<Token>),
    T_Bang,
    T_Banged(Token),
    T_BraceExpansion(Vec<Token>),
    T_BraceGroup(Vec<Token>),
    T_CLOBBER,
    T_Case,
    T_CaseExpression { word: Token, cases: Vec<CaseClause> },
    T_Condition { typ: ConditionType, token: Token },
    T_DGREAT,
    T_DLESS,
    T_DLESSDASH,
    T_DSEMI,
    T_Do,
    T_DollarArithmetic(Token),
    T_DollarBraced { braced: bool, op: Token },
    T_DollarBracket(Token),
    T_DollarDoubleQuoted(Vec<Token>),
    T_DollarExpansion(Vec<Token>),
    T_DollarSingleQuoted(String),
    T_DollarBraceCommandExpansion { pipe: Piped, list: Vec<Token> },
    T_Done,
    T_DoubleQuoted(Vec<Token>),
    T_EOF,
    T_Elif,
    T_Else,
    T_Esac,
    T_Extglob { op: String, list: Vec<Token> },
    T_FdRedirect { fd: String, target: Token },
    T_Fi,
    T_For,
    T_ForArithmetic { init: Token, cond: Token, step: Token, body: Vec<Token> },
    T_ForIn { var: String, items: Vec<Token>, body: Vec<Token> },
    T_Function { keyword: bool, parens: bool, name: String, body: Token },
    T_GREATAND,
    T_Glob(String),
    T_Greater,
    T_HereDoc { dashed: Dashed, quoted: Quoted, delim: String, body: Vec<Token> },
    T_HereString(Token),
    T_If,
    T_IfExpression { clauses: Vec<IfClause>, elses: Vec<Token> },
    T_In,
    T_IoFile { op: Token, file: Token },
    T_IoDuplicate { op: Token, num: String },
    T_LESSAND,
    T_LESSGREAT,
    T_Lbrace,
    T_Less,
    T_Literal(String),
    T_Lparen,
    T_NEWLINE,
    T_NormalWord(Vec<Token>),
    T_OR_IF,
    T_OrIf { lhs: Token, rhs: Token },
    T_ParamSubSpecialChar(String),
    T_Pipeline { separators: Vec<Token>, commands: Vec<Token> },
    T_ProcSub { op: String, list: Vec<Token> },
    T_Rbrace,
    T_Redirecting { redirs: Vec<Token>, cmd: Token },
    T_Rparen,
    T_Script { shebang: Token, commands: Vec<Token> },
    T_Select,
    T_SelectIn { var: String, items: Vec<Token>, body: Vec<Token> },
    T_Semi,
    T_SimpleCommand { assignments: Vec<Token>, words: Vec<Token> },
    T_SingleQuoted(String),
    T_Subshell(Vec<Token>),
    T_Then,
    T_Until,
    T_UntilExpression { condition: Vec<Token>, body: Vec<Token> },
    T_While,
    T_WhileExpression { condition: Vec<Token>, body: Vec<Token> },
    T_Annotation { annotations: Vec<Annotation>, token: Token },
    T_Pipe(String),
    T_CoProc { name: Option<Token>, body: Token },
    T_CoProcBody(Token),
    T_Include(Token),
    T_SourceCommand { includer: Token, included: Token },
    T_BatsTest { name: String, body: Token },
}

impl InnerToken {
    /// Immediate child tokens, in Haskell `Traversable` order (fields
    /// left-to-right, list elements in order). Used by pre-order traversal.
    pub fn children(&self) -> Vec<&Token> {
        use InnerToken::*;
        let mut out: Vec<&Token> = Vec::new();
        match self {
            TA_Binary { lhs, rhs, .. } | TA_Assignment { lhs, rhs, .. } => {
                out.push(lhs);
                out.push(rhs);
            }
            TA_Variable { indices, .. } => out.extend(indices.iter()),
            TA_Expansion(l) | TA_Sequence(l) => out.extend(l.iter()),
            TA_Parenthesis(t) => out.push(t),
            TA_Trinary { cond, then, els } => {
                out.push(cond);
                out.push(then);
                out.push(els);
            }
            TA_Unary { operand, .. } => out.push(operand),

            TC_And { lhs, rhs, .. } | TC_Binary { lhs, rhs, .. } | TC_Or { lhs, rhs, .. } => {
                out.push(lhs);
                out.push(rhs);
            }
            TC_Group { token, .. } | TC_Nullary { token, .. } | TC_Unary { token, .. } => {
                out.push(token)
            }
            TC_Empty { .. } => {}

            T_AndIf { lhs, rhs } | T_OrIf { lhs, rhs } => {
                out.push(lhs);
                out.push(rhs);
            }
            T_Arithmetic(t)
            | T_Backgrounded(t)
            | T_Banged(t)
            | T_DollarArithmetic(t)
            | T_DollarBracket(t)
            | T_HereString(t)
            | T_CoProcBody(t)
            | T_Include(t) => out.push(t),
            T_Array(l)
            | T_Backticked(l)
            | T_BraceExpansion(l)
            | T_BraceGroup(l)
            | T_DollarDoubleQuoted(l)
            | T_DollarExpansion(l)
            | T_DoubleQuoted(l)
            | T_NormalWord(l)
            | T_Subshell(l) => out.extend(l.iter()),
            T_IndexedElement { indices, value } => {
                out.extend(indices.iter());
                out.push(value);
            }
            T_Assignment { indices, value, .. } => {
                out.extend(indices.iter());
                out.push(value);
            }
            T_CaseExpression { word, cases } => {
                out.push(word);
                for (_, pats, body) in cases {
                    out.extend(pats.iter());
                    out.extend(body.iter());
                }
            }
            T_Condition { token, .. } => out.push(token),
            T_DollarBraced { op, .. } => out.push(op),
            T_DollarBraceCommandExpansion { list, .. } => out.extend(list.iter()),
            T_Extglob { list, .. } => out.extend(list.iter()),
            T_FdRedirect { target, .. } => out.push(target),
            T_ForArithmetic { init, cond, step, body } => {
                out.push(init);
                out.push(cond);
                out.push(step);
                out.extend(body.iter());
            }
            T_ForIn { items, body, .. } | T_SelectIn { items, body, .. } => {
                out.extend(items.iter());
                out.extend(body.iter());
            }
            T_Function { body, .. } => out.push(body),
            T_HereDoc { body, .. } => out.extend(body.iter()),
            T_IfExpression { clauses, elses } => {
                for (cond, body) in clauses {
                    out.extend(cond.iter());
                    out.extend(body.iter());
                }
                out.extend(elses.iter());
            }
            T_IoFile { op, file } => {
                out.push(op);
                out.push(file);
            }
            T_IoDuplicate { op, .. } => out.push(op),
            T_Pipeline { separators, commands } => {
                out.extend(separators.iter());
                out.extend(commands.iter());
            }
            T_ProcSub { list, .. } => out.extend(list.iter()),
            T_Redirecting { redirs, cmd } => {
                out.extend(redirs.iter());
                out.push(cmd);
            }
            T_Script { shebang, commands } => {
                out.push(shebang);
                out.extend(commands.iter());
            }
            T_SimpleCommand { assignments, words } => {
                out.extend(assignments.iter());
                out.extend(words.iter());
            }
            T_UntilExpression { condition, body }
            | T_WhileExpression { condition, body } => {
                out.extend(condition.iter());
                out.extend(body.iter());
            }
            T_Annotation { token, .. } => out.push(token),
            T_CoProc { name, body } => {
                if let Some(n) = name {
                    out.push(n);
                }
                out.push(body);
            }
            T_SourceCommand { includer, included } => {
                out.push(includer);
                out.push(included);
            }
            T_BatsTest { body, .. } => out.push(body),

            // Leaves with no token children.
            T_AND_IF | T_Bang | T_Case | T_CLOBBER | T_DGREAT | T_DLESS | T_DLESSDASH
            | T_DSEMI | T_Do | T_DollarSingleQuoted(_) | T_Done | T_Elif | T_Else | T_EOF
            | T_Esac | T_Fi | T_For | T_Glob(_) | T_GREATAND | T_Greater | T_If | T_In
            | T_Lbrace | T_Less | T_LESSAND | T_LESSGREAT | T_Literal(_) | T_Lparen
            | T_NEWLINE | T_OR_IF | T_ParamSubSpecialChar(_) | T_Pipe(_) | T_Rbrace
            | T_Rparen | T_Select | T_Semi | T_SingleQuoted(_) | T_Then | T_UnparsedIndex { .. }
            | T_Until | T_While => {}
        }
        out
    }
}

impl InnerToken {
    /// Mutable immediate child tokens, in the same order as [`children`].
    pub fn children_mut(&mut self) -> Vec<&mut Token> {
        use InnerToken::*;
        let mut out: Vec<&mut Token> = Vec::new();
        match self {
            TA_Binary { lhs, rhs, .. } | TA_Assignment { lhs, rhs, .. } => {
                out.push(lhs);
                out.push(rhs);
            }
            TA_Variable { indices, .. } => out.extend(indices.iter_mut()),
            TA_Expansion(l) | TA_Sequence(l) => out.extend(l.iter_mut()),
            TA_Parenthesis(t) => out.push(t),
            TA_Trinary { cond, then, els } => {
                out.push(cond);
                out.push(then);
                out.push(els);
            }
            TA_Unary { operand, .. } => out.push(operand),
            TC_And { lhs, rhs, .. } | TC_Binary { lhs, rhs, .. } | TC_Or { lhs, rhs, .. } => {
                out.push(lhs);
                out.push(rhs);
            }
            TC_Group { token, .. } | TC_Nullary { token, .. } | TC_Unary { token, .. } => {
                out.push(token)
            }
            TC_Empty { .. } => {}
            T_AndIf { lhs, rhs } | T_OrIf { lhs, rhs } => {
                out.push(lhs);
                out.push(rhs);
            }
            T_Arithmetic(t)
            | T_Backgrounded(t)
            | T_Banged(t)
            | T_DollarArithmetic(t)
            | T_DollarBracket(t)
            | T_HereString(t)
            | T_CoProcBody(t)
            | T_Include(t) => out.push(t),
            T_Array(l)
            | T_Backticked(l)
            | T_BraceExpansion(l)
            | T_BraceGroup(l)
            | T_DollarDoubleQuoted(l)
            | T_DollarExpansion(l)
            | T_DoubleQuoted(l)
            | T_NormalWord(l)
            | T_Subshell(l) => out.extend(l.iter_mut()),
            T_IndexedElement { indices, value } => {
                out.extend(indices.iter_mut());
                out.push(value);
            }
            T_Assignment { indices, value, .. } => {
                out.extend(indices.iter_mut());
                out.push(value);
            }
            T_CaseExpression { word, cases } => {
                out.push(word);
                for (_, pats, body) in cases {
                    out.extend(pats.iter_mut());
                    out.extend(body.iter_mut());
                }
            }
            T_Condition { token, .. } => out.push(token),
            T_DollarBraced { op, .. } => out.push(op),
            T_DollarBraceCommandExpansion { list, .. } => out.extend(list.iter_mut()),
            T_Extglob { list, .. } => out.extend(list.iter_mut()),
            T_FdRedirect { target, .. } => out.push(target),
            T_ForArithmetic { init, cond, step, body } => {
                out.push(init);
                out.push(cond);
                out.push(step);
                out.extend(body.iter_mut());
            }
            T_ForIn { items, body, .. } | T_SelectIn { items, body, .. } => {
                out.extend(items.iter_mut());
                out.extend(body.iter_mut());
            }
            T_Function { body, .. } => out.push(body),
            T_HereDoc { body, .. } => out.extend(body.iter_mut()),
            T_IfExpression { clauses, elses } => {
                for (cond, body) in clauses {
                    out.extend(cond.iter_mut());
                    out.extend(body.iter_mut());
                }
                out.extend(elses.iter_mut());
            }
            T_IoFile { op, file } => {
                out.push(op);
                out.push(file);
            }
            T_IoDuplicate { op, .. } => out.push(op),
            T_Pipeline { separators, commands } => {
                out.extend(separators.iter_mut());
                out.extend(commands.iter_mut());
            }
            T_ProcSub { list, .. } => out.extend(list.iter_mut()),
            T_Redirecting { redirs, cmd } => {
                out.extend(redirs.iter_mut());
                out.push(cmd);
            }
            T_Script { shebang, commands } => {
                out.push(shebang);
                out.extend(commands.iter_mut());
            }
            T_SimpleCommand { assignments, words } => {
                out.extend(assignments.iter_mut());
                out.extend(words.iter_mut());
            }
            T_UntilExpression { condition, body } | T_WhileExpression { condition, body } => {
                out.extend(condition.iter_mut());
                out.extend(body.iter_mut());
            }
            T_Annotation { token, .. } => out.push(token),
            T_CoProc { name, body } => {
                if let Some(n) = name {
                    out.push(n);
                }
                out.push(body);
            }
            T_SourceCommand { includer, included } => {
                out.push(includer);
                out.push(included);
            }
            T_BatsTest { body, .. } => out.push(body),
            T_AND_IF | T_Bang | T_Case | T_CLOBBER | T_DGREAT | T_DLESS | T_DLESSDASH
            | T_DSEMI | T_Do | T_DollarSingleQuoted(_) | T_Done | T_Elif | T_Else | T_EOF
            | T_Esac | T_Fi | T_For | T_Glob(_) | T_GREATAND | T_Greater | T_If | T_In
            | T_Lbrace | T_Less | T_LESSAND | T_LESSGREAT | T_Literal(_) | T_Lparen
            | T_NEWLINE | T_OR_IF | T_ParamSubSpecialChar(_) | T_Pipe(_) | T_Rbrace
            | T_Rparen | T_Select | T_Semi | T_SingleQuoted(_) | T_Then | T_UnparsedIndex { .. }
            | T_Until | T_While => {}
        }
        out
    }
}

impl Token {
    /// Immediate children of this token.
    pub fn children(&self) -> Vec<&Token> {
        self.inner.children()
    }

    /// Pre-order visit (parent before children), matching `doAnalysis f`.
    pub fn visit_preorder<F: FnMut(&Token)>(&self, f: &mut F) {
        f(self);
        for c in self.children() {
            c.visit_preorder(f);
        }
    }

    /// Stack analysis: `start` pre-order, recurse, `end` post-order —
    /// matching `doStackAnalysis`.
    pub fn visit_stack<S: FnMut(&Token), E: FnMut(&Token)>(&self, start: &mut S, end: &mut E) {
        start(self);
        for c in self.children() {
            c.visit_stack(start, end);
        }
        end(self);
    }
}
