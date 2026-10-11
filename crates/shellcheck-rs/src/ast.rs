//! Port of `ShellCheck.AST`.
//!
//! The Haskell AST is `newtype Id = Id Int` and
//! `data Token = OuterToken Id (InnerToken Token)`, where `InnerToken` derives
//! `Functor`/`Foldable`/`Traversable` over its child-token parameter. Here
//! `InnerToken` holds `Token` children directly and `Token` holds its inner
//! behind an `Rc` to break the type cycle and to keep `clone` a pointer copy,
//! as it is in Haskell. Generic traversal is provided by [`Token::children`]
//! and the `visit_*`/`transform` helpers instead of derived typeclasses.
//!
//! IMPORTANT: Haskell defines `instance Eq Token` to compare **only the inner
//! token, ignoring the Id**. Structural checks rely on this. We reproduce it
//! with a hand-written `PartialEq` on `Token`.

/// `newtype Id = Id Int`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id(pub i32);

/// `Quoted`: whether a here-document's delimiter is quoted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quoted {
    /// The delimiter is quoted and the body is literal.
    Quoted,
    /// The delimiter is unquoted and the body undergoes expansion.
    Unquoted,
}

/// `Dashed`: whether a here-document opens with `<<-`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dashed {
    /// `<<-`, with leading tabs stripped.
    Dashed,
    /// `<<`.
    Undashed,
}

/// `Piped`: the form of a ksh-style `${ ..; }` command expansion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Piped {
    /// `${| ..; }`.
    Piped,
    /// `${ ..; }`.
    Unpiped,
}

/// `AssignmentMode`: the operator of an assignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignmentMode {
    /// `=`.
    Assign,
    /// `+=`.
    Append,
}

/// `CaseType`: the terminator of a case clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaseType {
    /// `;;`, or no terminator before `esac`.
    CaseBreak,
    /// `;&`.
    CaseFallThrough,
    /// `;;&`.
    CaseContinue,
}

/// `ConditionType`: which test syntax a condition uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConditionType {
    /// `[[ ... ]]`.
    DoubleBracket,
    /// `[ ... ]`.
    SingleBracket,
}

/// `ShellCheck.AST.Annotation`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Annotation {
    /// `DisableComment from to` — half-open range `[from, to)`.
    DisableComment(i64, i64),
    /// `enable=name`: an optional check to enable.
    EnableComment(String),
    /// `source=file`: the file a `source` command reads.
    SourceOverride(String),
    /// `shell=name`: the shell dialect to assume.
    ShellOverride(String),
    /// `source-path=dir`: a directory to search for sourced files.
    SourcePath(String),
    /// `external-sources=bool`: whether to follow sourced files outside the input list.
    ExternalSources(bool),
    /// `extended-analysis=bool`: whether to run dataflow analysis.
    ExtendedAnalysis(bool),
}

/// One `(CaseType, patterns, body)` clause of a case expression.
pub type CaseClause = (CaseType, Vec<Token>, Vec<Token>);

/// A `(conditions, body)` clause of an if/elif chain.
pub type IfClause = (Vec<Token>, Vec<Token>);

/// `data Token = OuterToken Id (InnerToken Token)`.
///
/// Equality ignores `id` (see module docs).
///
/// The inner payload is behind an `Rc` rather than a `Box` purely for the cost
/// of `clone`.
///
/// Haskell's `Token` is an immutable graph node: `getPath`, `parentMap` and
/// every `Parameters` field hold the *same* nodes the tree holds, and copying
/// one is a pointer copy. A `Box` here made `Token: Clone` a deep copy of the
/// whole subtree, so the ancestor list `getPath` returns cost O(tree) per node
/// and the per-node check walk became quadratic. `Rc` restores the sharing the
/// original has; the few places that edit a tree go through
/// [`Token::inner_mut`], whose copy-on-write duplicates only the nodes it is
/// about to change.
#[derive(Debug, Clone)]
pub struct Token {
    /// The node's `Id`.
    pub id: Id,
    /// The node's `InnerToken` payload.
    pub inner: std::rc::Rc<InnerToken>,
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        // Mirrors `instance Eq Token where OuterToken _ a == OuterToken _ b = a == b`
        self.inner == other.inner
    }
}
impl Eq for Token {}

impl Token {
    /// `OuterToken id inner`.
    #[must_use]
    pub fn new(id: Id, inner: InnerToken) -> Self {
        Self {
            id,
            inner: std::rc::Rc::new(inner),
        }
    }

    /// The inner payload for editing, copy-on-write.
    ///
    /// Only the tree rewrites have any business calling this: the parser's
    /// fixups and `removeTransparentCommands`' local copy. Everything else
    /// reads through `&*t.inner`.
    #[inline]
    pub fn inner_mut(&mut self) -> &mut InnerToken {
        std::rc::Rc::make_mut(&mut self.inner)
    }

    /// `getId`.
    #[inline]
    #[must_use]
    pub const fn id(&self) -> Id {
        self.id
    }

    /// The inner payload.
    #[inline]
    #[must_use]
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
    /// `TA_Binary`: an arithmetic binary operation.
    TA_Binary {
        /// The operator, e.g. `+`.
        op: String,
        /// The left operand.
        lhs: Token,
        /// The right operand.
        rhs: Token,
    },
    /// `TA_Assignment`: an arithmetic assignment such as `x += 1`.
    TA_Assignment {
        /// The assignment operator, e.g. `+=`.
        op: String,
        /// The assigned variable.
        lhs: Token,
        /// The assigned value.
        rhs: Token,
    },
    /// `TA_Variable`: a variable in arithmetic context.
    TA_Variable {
        /// The variable name.
        name: String,
        /// The array subscripts.
        indices: Vec<Token>,
    },
    /// `TA_Expansion`: an arithmetic operand made of word parts, e.g. `$x`.
    TA_Expansion(Vec<Token>),
    /// `TA_Sequence`: comma-separated arithmetic expressions.
    TA_Sequence(Vec<Token>),
    /// `TA_Parenthesis`: a parenthesized arithmetic expression.
    TA_Parenthesis(Token),
    /// `TA_Trinary`: the `cond ? then : else` operator.
    TA_Trinary {
        /// The condition.
        cond: Token,
        /// The value when the condition is nonzero.
        then: Token,
        /// The value when the condition is zero.
        els: Token,
    },
    /// `TA_Unary`: an arithmetic unary operation.
    TA_Unary {
        /// The operator, where `++` and `--` carry a `|` on the operand's side.
        op: String,
        /// The operand.
        operand: Token,
    },

    // --- Test conditions (TC_*) ---
    /// `TC_And`: `&&` or `-a` in a test.
    TC_And {
        /// Which test syntax holds it.
        typ: ConditionType,
        /// The operator as written.
        op: String,
        /// The left operand.
        lhs: Token,
        /// The right operand.
        rhs: Token,
    },
    /// `TC_Binary`: a binary test such as `a = b`.
    TC_Binary {
        /// Which test syntax holds it.
        typ: ConditionType,
        /// The operator, e.g. `-eq`.
        op: String,
        /// The left operand.
        lhs: Token,
        /// The right operand.
        rhs: Token,
    },
    /// `TC_Group`: a parenthesized test.
    TC_Group {
        /// Which test syntax holds it.
        typ: ConditionType,
        /// The grouped test.
        token: Token,
    },
    /// `TC_Nullary`: a test of a single word with no operator.
    TC_Nullary {
        /// Which test syntax holds it.
        typ: ConditionType,
        /// The tested word.
        token: Token,
    },
    /// `TC_Or`: `||` or `-o` in a test.
    TC_Or {
        /// Which test syntax holds it.
        typ: ConditionType,
        /// The operator as written.
        op: String,
        /// The left operand.
        lhs: Token,
        /// The right operand.
        rhs: Token,
    },
    /// `TC_Unary`: a unary test such as `-f file`.
    TC_Unary {
        /// Which test syntax holds it.
        typ: ConditionType,
        /// The operator, e.g. `-f`.
        op: String,
        /// The operand.
        token: Token,
    },
    /// `TC_Empty`: a test with no expression, such as `[ ]`.
    TC_Empty {
        /// Which test syntax holds it.
        typ: ConditionType,
    },

    // --- Operator / keyword leaves ---
    /// `T_AND_IF`: the `&&` operator.
    T_AND_IF,
    /// `T_AndIf`: `lhs && rhs`.
    T_AndIf {
        /// The left command.
        lhs: Token,
        /// The right command.
        rhs: Token,
    },
    /// `T_Arithmetic`: an `(( ... ))` command.
    T_Arithmetic(Token),
    /// `T_Array`: an array literal `( ... )`.
    T_Array(Vec<Token>),
    /// `T_IndexedElement`: a `[index]=value` array element.
    T_IndexedElement {
        /// The subscripts.
        indices: Vec<Token>,
        /// The element value.
        value: Token,
    },
    /// Index stored as string, parsed later as arithmetic or string.
    T_UnparsedIndex {
        /// Where the index text starts.
        pos: crate::interface::Position,
        /// The raw index text.
        str: String,
    },
    /// `T_Assignment`: `var=value` or `var+=value`.
    T_Assignment {
        /// Whether it assigns or appends.
        mode: AssignmentMode,
        /// The variable name.
        var: String,
        /// The array subscripts on the variable.
        indices: Vec<Token>,
        /// The assigned value.
        value: Token,
    },
    /// `T_Backgrounded`: a command followed by `&`.
    T_Backgrounded(Token),
    /// `T_Backticked`: a `` `...` `` command substitution.
    T_Backticked(Vec<Token>),
    /// `T_Bang`: the `!` keyword.
    T_Bang,
    /// `T_Banged`: a pipeline negated with `!`.
    T_Banged(Token),
    /// `T_BraceExpansion`: a `{a,b}` brace expansion.
    T_BraceExpansion(Vec<Token>),
    /// `T_BraceGroup`: a `{ ...; }` command group.
    T_BraceGroup(Vec<Token>),
    /// `T_CLOBBER`: the `>|` operator.
    T_CLOBBER,
    /// `T_Case`: the `case` keyword.
    T_Case,
    /// `T_CaseExpression`: a `case ... esac` command.
    T_CaseExpression {
        /// The word being matched.
        word: Token,
        /// The clauses in order.
        cases: Vec<CaseClause>,
    },
    /// `T_Condition`: a `[ ... ]` or `[[ ... ]]` test.
    T_Condition {
        /// Which bracket form it uses.
        typ: ConditionType,
        /// The test expression.
        token: Token,
    },
    /// `T_DGREAT`: the `>>` operator.
    T_DGREAT,
    /// `T_DLESS`: the `<<` operator.
    T_DLESS,
    /// `T_DLESSDASH`: the `<<-` operator.
    T_DLESSDASH,
    /// `T_DSEMI`: the `;;` operator.
    T_DSEMI,
    /// `T_Do`: the `do` keyword.
    T_Do,
    /// `T_DollarArithmetic`: a `$(( ... ))` expansion.
    T_DollarArithmetic(Token),
    /// `T_DollarBraced`: a parameter expansion, `$x` or `${...}`.
    T_DollarBraced {
        /// Whether the expansion uses braces.
        braced: bool,
        /// The expansion's contents without the `$` and braces.
        op: Token,
    },
    /// `T_DollarBracket`: the obsolete `$[ ... ]` arithmetic expansion.
    T_DollarBracket(Token),
    /// `T_DollarDoubleQuoted`: a `$"..."` translated string.
    T_DollarDoubleQuoted(Vec<Token>),
    /// `T_DollarExpansion`: a `$( ... )` command substitution.
    T_DollarExpansion(Vec<Token>),
    /// `T_DollarSingleQuoted`: a `$'...'` string.
    T_DollarSingleQuoted(String),
    /// `T_DollarBraceCommandExpansion`: a ksh-style `${ ..; }` command expansion.
    T_DollarBraceCommandExpansion {
        /// Whether it is the `${| ..; }` form.
        pipe: Piped,
        /// The commands inside.
        list: Vec<Token>,
    },
    /// `T_Done`: the `done` keyword.
    T_Done,
    /// `T_DoubleQuoted`: a `"..."` string.
    T_DoubleQuoted(Vec<Token>),
    /// `T_EOF`: the end of input.
    T_EOF,
    /// `T_Elif`: the `elif` keyword.
    T_Elif,
    /// `T_Else`: the `else` keyword.
    T_Else,
    /// `T_Esac`: the `esac` keyword.
    T_Esac,
    /// `T_Extglob`: an extended glob such as `@(a|b)`.
    T_Extglob {
        /// The operator character such as `@`, or empty for a nested group.
        op: String,
        /// The alternatives.
        list: Vec<Token>,
    },
    /// `T_FdRedirect`: a redirection with its source descriptor.
    T_FdRedirect {
        /// The source descriptor as written, such as `2`, `{var}`, `&` or empty.
        fd: String,
        /// The redirection itself.
        target: Token,
    },
    /// `T_Fi`: the `fi` keyword.
    T_Fi,
    /// `T_For`: the `for` keyword.
    T_For,
    /// `T_ForArithmetic`: a `for (( init; cond; step ))` loop.
    T_ForArithmetic {
        /// The initializer.
        init: Token,
        /// The loop condition.
        cond: Token,
        /// The step expression.
        step: Token,
        /// The loop body.
        body: Vec<Token>,
    },
    /// `T_ForIn`: a `for var in items` loop.
    T_ForIn {
        /// The loop variable.
        var: String,
        /// The words to iterate over.
        items: Vec<Token>,
        /// The loop body.
        body: Vec<Token>,
    },
    /// `T_Function`: a function definition.
    T_Function {
        /// Whether it uses the `function` keyword.
        keyword: bool,
        /// Whether the name is followed by `()`.
        parens: bool,
        /// The function name.
        name: String,
        /// The function body.
        body: Token,
    },
    /// `T_GREATAND`: the `>&` operator.
    T_GREATAND,
    /// `T_Glob`: a glob wildcard such as `*` or `[ab]`.
    T_Glob(String),
    /// `T_Greater`: the `>` operator.
    T_Greater,
    /// `T_HereDoc`: a here-document.
    T_HereDoc {
        /// Whether it opens with `<<-`.
        dashed: Dashed,
        /// Whether the delimiter is quoted.
        quoted: Quoted,
        /// The delimiter with its quotes removed.
        delim: String,
        /// The document contents.
        body: Vec<Token>,
    },
    /// `T_HereString`: a `<<< word` here-string.
    T_HereString(Token),
    /// `T_If`: the `if` keyword.
    T_If,
    /// `T_IfExpression`: an `if ... fi` command.
    T_IfExpression {
        /// The `if` and `elif` branches as `(condition, body)` pairs.
        clauses: Vec<IfClause>,
        /// The `else` body.
        elses: Vec<Token>,
    },
    /// `T_In`: the `in` keyword.
    T_In,
    /// `T_IoFile`: a redirection to or from a file.
    T_IoFile {
        /// The operator token, e.g. `T_Greater`.
        op: Token,
        /// The file word.
        file: Token,
    },
    /// `T_IoDuplicate`: a descriptor duplication such as `>&2`.
    T_IoDuplicate {
        /// The operator token, `T_GREATAND` or `T_LESSAND`.
        op: Token,
        /// The target descriptor as written, e.g. `2` or `-`.
        num: String,
    },
    /// `T_LESSAND`: the `<&` operator.
    T_LESSAND,
    /// `T_LESSGREAT`: the `<>` operator.
    T_LESSGREAT,
    /// `T_Lbrace`: the `{` keyword.
    T_Lbrace,
    /// `T_Less`: the `<` operator.
    T_Less,
    /// `T_Literal`: a literal word fragment.
    T_Literal(String),
    /// `T_Lparen`: the `(` operator.
    T_Lparen,
    /// `T_NEWLINE`: a newline.
    T_NEWLINE,
    /// `T_NormalWord`: a shell word made of its parts.
    T_NormalWord(Vec<Token>),
    /// `T_OR_IF`: the `||` operator.
    T_OR_IF,
    /// `T_OrIf`: `lhs || rhs`.
    T_OrIf {
        /// The left command.
        lhs: Token,
        /// The right command.
        rhs: Token,
    },
    /// `T_ParamSubSpecialChar`: e.g. `%` in `${foo%bar}` or `/` in `${foo/bar/baz}`.
    T_ParamSubSpecialChar(String),
    /// `T_Pipeline`: commands joined by pipes.
    T_Pipeline {
        /// The pipe separators.
        separators: Vec<Token>,
        /// The commands.
        commands: Vec<Token>,
    },
    /// `T_ProcSub`: a `<( ... )` or `>( ... )` process substitution.
    T_ProcSub {
        /// The direction, `<` or `>`.
        op: String,
        /// The commands inside.
        list: Vec<Token>,
    },
    /// `T_Rbrace`: the `}` keyword.
    T_Rbrace,
    /// `T_Redirecting`: a command with its redirections.
    T_Redirecting {
        /// The redirections.
        redirs: Vec<Token>,
        /// The command.
        cmd: Token,
    },
    /// `T_Rparen`: the `)` operator.
    T_Rparen,
    /// `T_Script`: a whole script.
    T_Script {
        /// The shebang as a `T_Literal`.
        shebang: Token,
        /// The script's commands.
        commands: Vec<Token>,
    },
    /// `T_Select`: the `select` keyword.
    T_Select,
    /// `T_SelectIn`: a `select var in items` loop.
    T_SelectIn {
        /// The loop variable.
        var: String,
        /// The words to choose from.
        items: Vec<Token>,
        /// The loop body.
        body: Vec<Token>,
    },
    /// `T_Semi`: the `;` operator.
    T_Semi,
    /// `T_SimpleCommand`: a simple command.
    T_SimpleCommand {
        /// The leading variable assignments.
        assignments: Vec<Token>,
        /// The command name and arguments.
        words: Vec<Token>,
    },
    /// `T_SingleQuoted`: a `'...'` string.
    T_SingleQuoted(String),
    /// `T_Subshell`: a `( ... )` subshell.
    T_Subshell(Vec<Token>),
    /// `T_Then`: the `then` keyword.
    T_Then,
    /// `T_Until`: the `until` keyword.
    T_Until,
    /// `T_UntilExpression`: an `until ...; do ...; done` loop.
    T_UntilExpression {
        /// The loop condition.
        condition: Vec<Token>,
        /// The loop body.
        body: Vec<Token>,
    },
    /// `T_While`: the `while` keyword.
    T_While,
    /// `T_WhileExpression`: a `while ...; do ...; done` loop.
    T_WhileExpression {
        /// The loop condition.
        condition: Vec<Token>,
        /// The loop body.
        body: Vec<Token>,
    },
    /// `T_Annotation`: a token preceded by `# shellcheck` directives.
    T_Annotation {
        /// The directives.
        annotations: Vec<Annotation>,
        /// The annotated token.
        token: Token,
    },
    /// `T_Pipe`: a pipe separator, `|` or `|&`.
    T_Pipe(String),
    /// `T_CoProc`: a `coproc` command.
    T_CoProc {
        /// The coprocess name, if given.
        name: Option<Token>,
        /// The coprocess body.
        body: Token,
    },
    /// `T_CoProcBody`: the command a coprocess runs.
    T_CoProcBody(Token),
    /// `T_Include`: the parsed contents of a sourced file.
    T_Include(Token),
    /// `T_SourceCommand`: a `source` command with the script it read.
    T_SourceCommand {
        /// The `source` command.
        includer: Token,
        /// The `T_Include` of the sourced script.
        included: Token,
    },
    /// `T_BatsTest`: a Bats `@test` block.
    T_BatsTest {
        /// The test name.
        name: String,
        /// The test body.
        body: Token,
    },
}

macro_rules! children_of {
    ($inner:expr, $visit:ident) => {{
        use InnerToken::{
            T_AND_IF, T_AndIf, T_Annotation, T_Arithmetic, T_Array, T_Assignment, T_Backgrounded,
            T_Backticked, T_Bang, T_Banged, T_BatsTest, T_BraceExpansion, T_BraceGroup, T_CLOBBER,
            T_Case, T_CaseExpression, T_CoProc, T_CoProcBody, T_Condition, T_DGREAT, T_DLESS,
            T_DLESSDASH, T_DSEMI, T_Do, T_DollarArithmetic, T_DollarBraceCommandExpansion,
            T_DollarBraced, T_DollarBracket, T_DollarDoubleQuoted, T_DollarExpansion,
            T_DollarSingleQuoted, T_Done, T_DoubleQuoted, T_EOF, T_Elif, T_Else, T_Esac, T_Extglob,
            T_FdRedirect, T_Fi, T_For, T_ForArithmetic, T_ForIn, T_Function, T_GREATAND, T_Glob,
            T_Greater, T_HereDoc, T_HereString, T_If, T_IfExpression, T_In, T_Include,
            T_IndexedElement, T_IoDuplicate, T_IoFile, T_LESSAND, T_LESSGREAT, T_Lbrace, T_Less,
            T_Literal, T_Lparen, T_NEWLINE, T_NormalWord, T_OR_IF, T_OrIf, T_ParamSubSpecialChar,
            T_Pipe, T_Pipeline, T_ProcSub, T_Rbrace, T_Redirecting, T_Rparen, T_Script, T_Select,
            T_SelectIn, T_Semi, T_SimpleCommand, T_SingleQuoted, T_SourceCommand, T_Subshell,
            T_Then, T_UnparsedIndex, T_Until, T_UntilExpression, T_While, T_WhileExpression,
            TA_Assignment, TA_Binary, TA_Expansion, TA_Parenthesis, TA_Sequence, TA_Trinary,
            TA_Unary, TA_Variable, TC_And, TC_Binary, TC_Empty, TC_Group, TC_Nullary, TC_Or,
            TC_Unary,
        };
        match $inner {
            TA_Binary { lhs, rhs, .. }
            | TA_Assignment { lhs, rhs, .. }
            | TC_And { lhs, rhs, .. }
            | TC_Binary { lhs, rhs, .. }
            | TC_Or { lhs, rhs, .. }
            | T_AndIf { lhs, rhs }
            | T_OrIf { lhs, rhs } => {
                $visit(lhs)?;
                $visit(rhs)?;
            }
            TA_Variable { indices, .. } => {
                for child in indices {
                    $visit(child)?;
                }
            }
            TA_Expansion(l)
            | TA_Sequence(l)
            | T_Array(l)
            | T_Backticked(l)
            | T_BraceExpansion(l)
            | T_BraceGroup(l)
            | T_DollarDoubleQuoted(l)
            | T_DollarExpansion(l)
            | T_DoubleQuoted(l)
            | T_NormalWord(l)
            | T_Subshell(l) => {
                for child in l {
                    $visit(child)?;
                }
            }
            TA_Parenthesis(t)
            | T_Arithmetic(t)
            | T_Backgrounded(t)
            | T_Banged(t)
            | T_DollarArithmetic(t)
            | T_DollarBracket(t)
            | T_HereString(t)
            | T_CoProcBody(t)
            | T_Include(t) => $visit(t)?,
            TA_Trinary { cond, then, els } => {
                $visit(cond)?;
                $visit(then)?;
                $visit(els)?;
            }
            TA_Unary { operand, .. } => $visit(operand)?,
            TC_Group { token, .. }
            | TC_Nullary { token, .. }
            | TC_Unary { token, .. }
            | T_Condition { token, .. }
            | T_Annotation { token, .. } => $visit(token)?,
            T_IndexedElement { indices, value } | T_Assignment { indices, value, .. } => {
                for child in indices {
                    $visit(child)?;
                }
                $visit(value)?;
            }
            T_CaseExpression { word, cases } => {
                $visit(word)?;
                for (_, pats, body) in cases {
                    for child in pats {
                        $visit(child)?;
                    }
                    for child in body {
                        $visit(child)?;
                    }
                }
            }
            T_DollarBraced { op, .. } | T_IoDuplicate { op, .. } => $visit(op)?,
            T_DollarBraceCommandExpansion { list, .. }
            | T_Extglob { list, .. }
            | T_ProcSub { list, .. } => {
                for child in list {
                    $visit(child)?;
                }
            }
            T_FdRedirect { target, .. } => $visit(target)?,
            T_ForArithmetic {
                init,
                cond,
                step,
                body,
            } => {
                $visit(init)?;
                $visit(cond)?;
                $visit(step)?;
                for child in body {
                    $visit(child)?;
                }
            }
            T_ForIn { items, body, .. } | T_SelectIn { items, body, .. } => {
                for child in items {
                    $visit(child)?;
                }
                for child in body {
                    $visit(child)?;
                }
            }
            // Haskell declares `Inner_T_CoProc (Maybe Token) t`: the name is a
            // plain `Token`, not the recursive parameter, so the derived
            // `Traversable` (and with it `analyze`) never visits it. Checks
            // therefore see nothing inside `coproc $(cmd) { ..; }`'s name.
            T_Function { body, .. } | T_CoProc { body, .. } | T_BatsTest { body, .. } => {
                $visit(body)?;
            }
            T_HereDoc { body, .. } => {
                for child in body {
                    $visit(child)?;
                }
            }
            T_IfExpression { clauses, elses } => {
                for (cond, body) in clauses {
                    for child in cond {
                        $visit(child)?;
                    }
                    for child in body {
                        $visit(child)?;
                    }
                }
                for child in elses {
                    $visit(child)?;
                }
            }
            T_IoFile { op, file } => {
                $visit(op)?;
                $visit(file)?;
            }
            T_Pipeline {
                separators,
                commands,
            } => {
                for child in separators {
                    $visit(child)?;
                }
                for child in commands {
                    $visit(child)?;
                }
            }
            T_Redirecting { redirs, cmd } => {
                for child in redirs {
                    $visit(child)?;
                }
                $visit(cmd)?;
            }
            T_Script { shebang, commands } => {
                $visit(shebang)?;
                for child in commands {
                    $visit(child)?;
                }
            }
            T_SimpleCommand { assignments, words } => {
                for child in assignments {
                    $visit(child)?;
                }
                for child in words {
                    $visit(child)?;
                }
            }
            T_UntilExpression { condition, body } | T_WhileExpression { condition, body } => {
                for child in condition {
                    $visit(child)?;
                }
                for child in body {
                    $visit(child)?;
                }
            }
            T_SourceCommand { includer, included } => {
                $visit(includer)?;
                $visit(included)?;
            }

            // Leaves with no token children.
            TC_Empty { .. }
            | T_AND_IF
            | T_Bang
            | T_Case
            | T_CLOBBER
            | T_DGREAT
            | T_DLESS
            | T_DLESSDASH
            | T_DSEMI
            | T_Do
            | T_DollarSingleQuoted(_)
            | T_Done
            | T_Elif
            | T_Else
            | T_EOF
            | T_Esac
            | T_Fi
            | T_For
            | T_Glob(_)
            | T_GREATAND
            | T_Greater
            | T_If
            | T_In
            | T_Lbrace
            | T_Less
            | T_LESSAND
            | T_LESSGREAT
            | T_Literal(_)
            | T_Lparen
            | T_NEWLINE
            | T_OR_IF
            | T_ParamSubSpecialChar(_)
            | T_Pipe(_)
            | T_Rbrace
            | T_Rparen
            | T_Select
            | T_Semi
            | T_SingleQuoted(_)
            | T_Then
            | T_UnparsedIndex { .. }
            | T_Until
            | T_While => {}
        }
        std::ops::ControlFlow::Continue(())
    }};
}

impl InnerToken {
    /// Visit immediate children in traversal order without allocating a list.
    pub fn for_each_child<'a>(&'a self, mut visit: impl FnMut(&'a Token)) {
        let _ = self.try_for_each_child(|child| {
            visit(child);
            std::ops::ControlFlow::<()>::Continue(())
        });
    }

    /// Visit immediate children until the visitor breaks, without allocating.
    pub fn try_for_each_child<'a, B>(
        &'a self,
        mut visit: impl FnMut(&'a Token) -> std::ops::ControlFlow<B>,
    ) -> std::ops::ControlFlow<B> {
        children_of!(self, visit)
    }

    /// Immediate child tokens, in Haskell `Traversable` order (fields
    /// left-to-right, list elements in order). Used by pre-order traversal.
    #[must_use]
    pub fn children(&self) -> Vec<&Token> {
        let mut out = Vec::new();
        self.for_each_child(|child| out.push(child));
        out
    }
}

impl InnerToken {
    /// Mutable immediate child tokens, in the same order as [`children`](Self::children).
    pub fn children_mut(&mut self) -> Vec<&mut Token> {
        let mut out = Vec::new();
        let _ = self.try_for_each_child_mut(|child| {
            out.push(child);
            std::ops::ControlFlow::<()>::Continue(())
        });
        out
    }

    fn try_for_each_child_mut<'a, B>(
        &'a mut self,
        mut visit: impl FnMut(&'a mut Token) -> std::ops::ControlFlow<B>,
    ) -> std::ops::ControlFlow<B> {
        children_of!(self, visit)
    }
}

impl Token {
    /// Immediate children of this token.
    #[must_use]
    pub fn children(&self) -> Vec<&Self> {
        self.inner.children()
    }

    /// Pre-order visit (parent before children), matching `doAnalysis f`.
    pub fn visit_preorder<F: FnMut(&Self)>(&self, f: &mut F) {
        f(self);
        self.inner.for_each_child(|c| c.visit_preorder(f));
    }

    /// Pre-order traversal that stops immediately when the visitor breaks.
    pub fn try_visit_preorder<B>(
        &self,
        visit: &mut impl FnMut(&Self) -> std::ops::ControlFlow<B>,
    ) -> std::ops::ControlFlow<B> {
        visit(self)?;
        self.inner
            .try_for_each_child(|child| child.try_visit_preorder(visit))
    }

    /// Stack analysis: `start` pre-order, recurse, `end` post-order —
    /// matching `doStackAnalysis`.
    pub fn visit_stack<S: FnMut(&Self), E: FnMut(&Self)>(&self, start: &mut S, end: &mut E) {
        start(self);
        self.inner.for_each_child(|c| c.visit_stack(start, end));
        end(self);
    }
}

#[cfg(test)]
mod sharing_tests {
    use super::*;

    #[test]
    fn visitors_preserve_field_order_and_stop_before_later_siblings() {
        let leaf = |id| Token::new(Id(id), InnerToken::T_Literal(id.to_string()));
        let mut tree = Token::new(
            Id(0),
            InnerToken::T_Redirecting {
                redirs: vec![leaf(1), leaf(2)],
                cmd: Token::new(Id(3), InnerToken::T_NormalWord(vec![leaf(4), leaf(5)])),
            },
        );
        let mut ids = Vec::new();
        tree.visit_preorder(&mut |t| ids.push(t.id()));
        assert_eq!(ids, (0..6).map(Id).collect::<Vec<_>>());
        ids.clear();
        let result = tree.try_visit_preorder(&mut |t| {
            ids.push(t.id());
            if t.id() == Id(4) {
                std::ops::ControlFlow::Break(42)
            } else {
                std::ops::ControlFlow::Continue(())
            }
        });
        assert_eq!(result, std::ops::ControlFlow::Break(42));
        assert_eq!(ids, (0..5).map(Id).collect::<Vec<_>>());
        assert_eq!(
            tree.children().iter().map(|t| t.id()).collect::<Vec<_>>(),
            vec![Id(1), Id(2), Id(3)]
        );
        let mutable_ids: Vec<_> = tree
            .inner_mut()
            .children_mut()
            .iter()
            .map(|t| t.id())
            .collect();
        assert_eq!(mutable_ids, vec![Id(1), Id(2), Id(3)]);
        let events = std::cell::RefCell::new(Vec::new());
        tree.visit_stack(
            &mut |t| events.borrow_mut().push((true, t.id())),
            &mut |t| events.borrow_mut().push((false, t.id())),
        );
        assert_eq!(
            events.into_inner(),
            vec![
                (true, Id(0)),
                (true, Id(1)),
                (false, Id(1)),
                (true, Id(2)),
                (false, Id(2)),
                (true, Id(3)),
                (true, Id(4)),
                (false, Id(4)),
                (true, Id(5)),
                (false, Id(5)),
                (false, Id(3)),
                (false, Id(0)),
            ]
        );
    }

    fn word(s: &str) -> Token {
        Token::new(
            Id(1),
            InnerToken::T_NormalWord(vec![Token::new(
                Id(2),
                InnerToken::T_Literal(s.to_string()),
            )]),
        )
    }

    /// Cloning a `Token` shares the subtree rather than copying it. This is
    /// what makes `getPath`, `idMap` and the parent map affordable: the check
    /// walk asks for a node's ancestors at every node, and a copying clone made
    /// that O(tree) each time.
    #[test]
    fn clone_shares_the_subtree() {
        let a = word("hello");
        let b = a.clone();
        assert!(std::rc::Rc::ptr_eq(&a.inner, &b.inner));
        assert_eq!(a, b);
    }

    /// Editing through `inner_mut` is copy-on-write: the other holder of the
    /// subtree keeps what it had.
    #[test]
    fn inner_mut_does_not_disturb_other_holders() {
        let original = word("hello");
        let mut edited = original.clone();
        if let InnerToken::T_NormalWord(parts) = edited.inner_mut() {
            parts.clear();
        }
        assert!(!std::rc::Rc::ptr_eq(&original.inner, &edited.inner));
        assert_eq!(original.children().len(), 1);
        assert_eq!(edited.children().len(), 0);
        // Ids survive an edit, as `doTransform` requires.
        assert_eq!(edited.id(), Id(1));
    }
}
