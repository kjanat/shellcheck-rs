# Parity notes: upstream diagnostics that are wrong, or merely strange

Findings about **ShellCheck 0.11.0's own diagnostics**, collected while building a
faithful port and gating it against the Haskell binary as an oracle.

Every item here is reproduced by the port **on purpose**, except where an entry's
**Port** line says otherwise. Parity is the goal, so a reader who spots one of
these in the port's output and files it as a port bug would be wrong — and a
"fix" would show up as a conformance divergence. That is what this file is for:
to say which oddities are inherited, what a user actually experiences, and why
upstream behaves that way.

Each entry is runnable. `shellcheck` below is the Haskell binary; every output
block is verbatim from 0.11.0 with no shebang in the input, so the SC2148 line
("add a shebang") is omitted for brevity where it appears.

Two groups:

- **Looks like a bug** — the diagnostic misinforms the reader, or a diagnostic
  the code clearly intends to emit cannot fire. Worth reporting upstream.
- **Consistent but surprising** — behaviour that follows from Parsec or from a
  deliberate design choice, but that will read as a defect to anyone who hits it.

---

## Looks like a bug

### 1. The syntax error is attributed to the wrong production

**Reproduce**

```sh
printf '%s' '${ ' | shellcheck -
printf '%s' '((())' | shellcheck -
```

**You get**

```
-:1:1: error: Couldn't parse this ksh-style ${ ..; } command expansion. Fix to allow more checks. [SC1073]
-:1:1: note: The mentioned syntax error was in this simple command. [SC1009]
-:1:4: error: Expected a command. Fix any mentioned problems and try again. [SC1072]
```

```
-:1:1: error: Couldn't parse this ((..)) command. Fix to allow more checks. [SC1073]
-:1:1: note: The mentioned syntax error was in this ((..)) command. [SC1009]
-:1:5: error:  Fix any mentioned problems and try again. [SC1072]
```

**What's wrong.** SC1073 and SC1009 are meant to bracket the failure: "the
construct that failed" and "the construct the error was inside". In the first
case there is no simple command anywhere in `${ ` — the SC1009 line names a
production that was attempted and abandoned. In the second, both lines name the
same `((..))` command, so the pair tells the reader nothing they did not already
have from one line.

For a user, this is the difference between "your `${ ..; }` is unterminated" and
being pointed at a nonexistent simple command in a three-character file. On real
scripts the misattribution lands on whatever the parser tried on the way down,
which can be several constructs away from the actual typo.

**Why.** `contextStack` lives in the `StateT` *outside* Parsec, so no
backtracking touches it. `parsecBracket` (used by `called`) pops a frame only
when the production succeeded, or failed *without consuming input*. A production
that gives up part-way leaves its frame on the stack, and `notesForContext` then
reports that residue as if it were live nesting.

**Port.** `((())` matches. `${ ` does **not** yet: the port names "parameter
expansion" in SC1073 and the `${ ..; }` expansion in SC1009, i.e. it leaves a
different pair of frames behind. Reproducing the exact residue here is an open
divergence, not a decision to differ.

---

### 2. `!` followed by a comment: the intended error never fires, and the position is past the comment

**Reproduce**

```sh
printf '%s' '! # negate what, exactly'  | shellcheck -
printf '%s\n' "''" '!#' | shellcheck -
```

**You get**

```
-:1:25: error: Expected a command. Fix any mentioned problems and try again. [SC1072]
```

```
-:2:3: error: Expected whitespace. Fix any mentioned problems and try again. [SC1072]
```

**What's wrong.** `g_Bang` contains an error message written precisely for this
input — SC1035 *"You are missing a required space after the !."* — and it cannot
fire when a comment follows the `!`. The user is told "Expected a command" at
column 25, i.e. at the end of the comment, or "Expected whitespace" at the end
of the line. Neither mentions the `!` that is the actual problem, and the column
points at whitespace the user cannot see.

**Why.** The code is `void spacing1 <|> parseProblemAt pos ErrorC 1035 ...`.
`spacing` happily consumes a trailing comment while returning no whitespace, so
`spacing1` fails *having consumed input* — and Parsec's `<|>` cannot reach the
right-hand side of an alternation once the left side consumed. The recovery arm
is dead code for exactly the input it was written for.

---

### 3. Arithmetic containing a unicode dash is reported as a command substitution

**Reproduce**

```sh
printf 'echo $((1 \xe2\x80\x93 2))\n' | shellcheck -   # en dash instead of minus
```

**You get**

```
-:1:6: error: Shells disambiguate $(( differently or not at all. For $(command substitution), add space after $( . For $((arithmetics)), fix parsing errors. [SC1102]
-:1:6: warning: Quote this to prevent word splitting. [SC2046]
-:1:6: note: Useless echo? Instead of 'echo $(cmd)', just use 'cmd'. [SC2005]
```

**What's wrong.** The script is arithmetic with a typo'd minus sign — an en dash
pasted from a document or an editor's smart-punctuation. All three diagnostics
describe a command substitution the user did not write, and the advice
("just use 'cmd'") is actively misleading. ShellCheck already has the right
message for this character, SC1100 *"This is a unicode dash. Delete and retype
as ASCII minus."*, but `weirdDash` is only consulted when reading a test
operator, not inside `$((..))`.

**Why.** `$((` is read through `readAmbiguous`, which falls back to
`readDollarExpansion` when the arithmetic parse fails, and then reports SC1102.
Once it is a command substitution, the ordinary command-substitution checks fire
on it. Nothing on that path looks at *why* the arithmetic failed.

---

## Consistent but surprising

### 4. An error positioned inside quotes that were never quotes

**Reproduce**

```sh
printf '%s' "[* '" | shellcheck -
```

**You get**

```
-:1:1: error: You need a space after the [ and before the ]. [SC1035]
-:1:1: error: Couldn't parse this test expression. Fix to allow more checks. [SC1073]
-:1:5: error: Expected comparison operator (don't wrap commands in []/[[]]). Fix any mentioned problems and try again. [SC1072]
```

**What a reader sees.** The input is four characters; the error is at column 5,
i.e. one past the end, and the message asks for a comparison operator at a point
where the user wrote a single quote.

**Why.** ShellCheck supports quoted test operators (`[ 1 '-eq' 2 ]`) through
`readEscaped`'s `withQuotes`: it consumes the quote and then runs the operator
parser *inside* it. So the `fail "Expected comparison operator"` is positioned
after the opening quote. Reasonable for `'-eq'`; confusing when the quote was
meant as a string or was simply unterminated.

---

### 5. Column of a failed multi-character token is where the token started

**Reproduce**

```sh
printf '%s' '((())' | shellcheck -
```

**You get**

```
-:1:5: error:  Fix any mentioned problems and try again. [SC1072]
```

**What a reader sees.** Column 5 is the last `)`, which is a perfectly good
character; the parser actually ran out of input at column 6. Also note the
message is empty — two spaces after `error:` — because the failure carries no
explicit text.

**Why.** Parsec's `tokens` (`string "))"`) reports a mismatch at the position the
string *started*, however far into it the mismatch occurred. The same rule makes
`optional (string "SC")` in a `# shellcheck disable=` directive blame the `S`.

---

### 6. Parser notes are zero-width, at the `$`, not on the thing they describe

**Reproduce**

```sh
printf 'echo $10\n'     | shellcheck -f json1 -
printf 'echo $arr[0]\n' | shellcheck -f json1 -
```

**You get** (relevant fields)

```
SC1037  column 6, endColumn 6     "Braces are required for positionals over 9, e.g. ${10}."
SC2086  column 6, endColumn 8     (the expansion itself)

SC1087  column 6, endColumn 6     "Use braces when expanding arrays, e.g. ${array[idx]} ..."
SC2154  column 6, endColumn 10    (the expansion itself)
```

**What a reader sees.** In a terminal the caret is a single column under the `$`,
while the analysis codes on the same line underline the whole expansion. Any
tool that renders spans — an editor's squiggle, a diff view, a fixer — gets a
zero-width range for a diagnostic about a multi-character construct.

**Why.** These are `parseNoteAt pos`, and `pos` was captured before the name was
read. `parseNoteAt` has no end position, so start and end coincide.

---

### 7. A parse note disappears if the parse fails later in the file

**Reproduce**

```sh
printf 'echo $10\n'      | shellcheck -   # SC1037 reported
printf 'echo $10\nif\n'  | shellcheck -   # SC1037 gone
```

**You get**

```
-:1:6: error: Braces are required for positionals over 9, e.g. ${10}. [SC1037]
```

```
-:2:1: error: Couldn't parse this if expression. Fix to allow more checks. [SC1073]
-:3:1: error: Expected a command. Fix any mentioned problems and try again. [SC1072]
```

**What a reader sees.** Line 1 did not change, but the diagnostic about it comes
and goes depending on whether something *further down* the file parses. Fix the
`if` and SC1037 reappears — which reads as flakiness, and makes "did my edit fix
this warning?" unanswerable without looking at the rest of the file.

**Why.** Deliberate: `parseNote` buffers into Parsec's state and is discarded
when the parse fails, while `parseProblem` is emitted unconditionally. The
intent is to avoid drowning a syntax error in notes derived from a
misunderstanding of the code. The cost is that which SC1xxx you see depends on
unrelated lines.

---

## Reporting upstream

Items 1 and 2 are defects with no upside: a misattributed context and an
unreachable error message. Item 3 is a missing hint on a path that already knows
the right words for it. Those three are worth a bug report against
[koalaman/shellcheck](https://github.com/koalaman/shellcheck).

Items 4–7 are working as designed, or as Parsec dictates. Changing them would
change output that existing users, tests and editor integrations depend on, so
they belong here rather than in an upstream issue.
