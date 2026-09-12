# Parity notes: upstream diagnostics that are wrong, or merely strange

Findings about **ShellCheck 0.11.0's own diagnostics**, collected while building a
faithful port and gating it against the Haskell binary as an oracle.

Most items here are reproduced by the port **on purpose**; an entry's **Port**
line says when it is not. A fix that makes the port better than the oracle needs
a *sanctioned deviation* — a class the conformance harness can justify from
evidence it gathers while comparing, not a blessed list of scripts. Today there
is one class, `upstream-false-parse-error`: the oracle rejects the file, the port
does not, and `<shell> -n` agrees with the port. See
`rust/crates/conformance/src/deviations.rs`; no shell to ask means the difference
counts as a divergence, so it fails closed.

Everything else is inherited on purpose, so a reader who spots one of these in
the port's output and files it as a port bug would be wrong — and "fixing" it
would show up as a conformance divergence. That is what this file is for: to say
which oddities are inherited, which are not, what a user actually experiences,
and why upstream behaves that way.

Each entry is runnable. `shellcheck` below is the Haskell binary; every output
block is verbatim from 0.11.0 with no shebang in the input, so the SC2148 line
("add a shebang") is omitted for brevity where it appears.

Every entry was also run through the shells themselves — **bash 5.2.21** and
**dash 0.5.12** — and says what they do with the same input. That comparison is
the arbiter here: a diagnostic that disagrees with the shell it is checking is a
defect, and one that merely reads oddly while describing real shell behaviour is
not.

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

**What the shells do**

```
bash: line 1: unexpected EOF while looking for matching `}'      # ${
bash: line 3: syntax error: unexpected end of file               # ((())
```

Both are genuine syntax errors, so ShellCheck is right to fail — the complaint
is only about which construct it blames.

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

### 2. `! # comment` is valid bash, and ShellCheck refuses to parse the file

**Reproduce**

```sh
printf '#!/bin/bash\n! # negate what, exactly\n' | bash;       echo "bash: $?"
printf '#!/bin/bash\n! # negate what, exactly\n' | shellcheck -
```

**What the shells do**

```
bash: 1            # accepted: ! negates the null command, so the script exits 1
```

dash rejects it (`Syntax error: newline unexpected`), so for a POSIX target
ShellCheck complaining is correct. For a bash target it is not.

**You get**

```
-:2:25: error: Expected a command. Fix any mentioned problems and try again. [SC1072]
```

**What's wrong.** Two things, and the second is the serious one.

1. `g_Bang` contains an error message written precisely for a missing space after
   `!` — SC1035 *"You are missing a required space after the !."* — and it cannot
   fire when a comment follows, so the user never sees the one message that would
   explain the problem.
2. With a bash shebang, this is a **fatal** SC1072 at column 25: the file does
   not parse, so nothing in it is analysed. A script bash runs fine gets no
   checking at all, and the reported column points at the end of a comment rather
   than at the `!`.

**Port: fixed, not reproduced.** Deviation `upstream-false-parse-error`. The
port follows the shells: a `!` with nothing to negate parses when the dialect is
bash, so the rest of the file is analysed —

```
-:3:6: warning: undefined is referenced but not assigned. [SC2154]
-:3:6: note: Double quote to prevent globbing and word splitting. [SC2086]
```

— and still fails for `sh`, `dash`, `ksh` and `busybox`, where dash's error is
the correct one. It also still fails for every shape bash itself rejects: `! &`,
`! ;;`, `! | true`, `! && true`, `( ! )`. This is the port's only dialect-aware
parse decision; the parser learns the dialect from `--shell`, else a file-wide
`shell=` directive, else the shebang, else bash.

**Why.** The code is `void spacing1 <|> parseProblemAt pos ErrorC 1035 ...`.
`spacing` consumes a trailing comment while returning no whitespace, so
`spacing1` fails *having consumed input* — and Parsec's `<|>` cannot reach the
right-hand side of an alternation once the left side consumed. The recovery arm
is dead code for exactly the input it was written for, and the failure escalates
to a parse error instead.

**Not this, though:** `!#` on its own line.

```sh
printf '!#\n' | bash          # bash: !#: command not found  (exit 127)
printf '!#\n' | dash          # dash: !#: not found          (exit 127)
```

`#` only opens a comment at the start of a word, so `!#` is a single word and
both shells treat it as a command *name*. ShellCheck reads the `!` as the
negation operator and then errors — a heuristic ("you meant `! foo`"), not a
misreading of shell grammar, and defensible as such.

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

**What the shell does**

```
bash: line 1: 1 – 2: syntax error: invalid arithmetic operator (error token is "– 2")
```

bash keeps it as arithmetic and names the offending token. ShellCheck is the only
one of the two that decides it was a command substitution.

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

**What the shell does**

```
bash: line 1: unexpected EOF while looking for matching `''
```

bash names the real problem: the quote is never closed. Close it and bash reports
`[*: command not found`, i.e. it never reads `[*` as a test at all.

**What a reader sees.** The input is four characters; the error is at column 5,
i.e. one past the end, and the message asks for a comparison operator at a point
where the user wrote a single quote. The unterminated quote — the thing bash
leads with — is not mentioned.

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

**What the shell does** — the checks themselves are exactly right:

```sh
bash -c 'set -- A B C; echo "[$10]" "[${10}]" "[${1}0]"'
# [A0] [] [A0]
```

`$10` is `${1}` followed by a literal `0`, never positional parameter 10, which
is what SC1037 says. With no arguments set, `echo $10` prints `0` — the empty
`$1` plus the `0` — which is why it looks like it "worked". SC1087 is the same
story for `$arr[0]`. Nothing about the diagnoses is in question here.

**What a reader sees.** Only the *span*. In a terminal the caret is a single
column under the `$`, while the analysis codes on the same line underline the
whole expansion. Any tool that renders ranges — an editor's squiggle, a diff
view, a fixer — gets a zero-width range for a diagnostic about a
multi-character construct.

**Why, and the case for it.** These are `parseNoteAt pos`, whose `pos` was
captured before the name was read; `parseNoteAt` takes no end position, so start
and end coincide. There is a reading in which the `$` is the *best* single
column to point at: the fix is to insert `{` right there. So this is filed as
surprising rather than wrong — it only bites tools that expect a span to cover
the construct it describes.

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

## Measuring this: `conformance shells`

The entries above were found one at a time. `conformance shells` measures the
same question in bulk: for every script in the corpus plus generated shell, it
compares each tool's idea of "this parses" (no SC1073/SC1009/SC1072) against the
real interpreter's (`<shell> -n`), per dialect — bash, dash for `sh`, **AT&T
ksh93** for `ksh` (not mksh, which is a different shell), and `busybox sh`.

2326 scripts per dialect, port vs oracle:

| dialect | rejects-valid (port / oracle) | accepts-invalid (port / oracle) |
| ------- | ----------------------------- | ------------------------------- |
| bash    | 33 / 33                       | 60 / 61                         |
| sh      | 30 / 30                       | 279 / 280                       |
| ksh     | 37 / 37                       | 82 / 83                         |
| busybox | 30 / 30                       | 253 / 254                       |

**rejects-valid** is the expensive direction: the shell runs the script, the
tool refuses to parse it, and the user gets no analysis at all. The port matches
upstream exactly there, so every one of those is inherited rather than
introduced. The smallest example is `{}` — a valid command word in all four
shells, which both tools reject. Item 2 above is the same shape, and the only
one the port currently fixes.

**accepts-invalid** is a syntax error the tool does not report. The counts are
high for `sh` and `busybox` because ShellCheck deliberately parses bash syntax
in every dialect and reports it as SC3xxx ("In dash, X is not supported")
instead of refusing the file — that is a feature, not a miss, and the number
should be read as "how much bash-only syntax the generator produced", not as a
defect count.

Neither column gates anything yet. They are a baseline: the port must not drift
above upstream in either, and `rejects-valid` is the list to mine for further
sanctioned deviations.

## Reporting upstream

Item 2 is the one with real consequences: bash runs `! # comment`, ShellCheck
declares the file unparseable and checks none of it. Item 1 is a misattributed
context on input that genuinely is a syntax error, and item 3 is a missing hint
on a path that already has the right words for it — both cosmetic next to 2.
Those three are worth a bug report against
[koalaman/shellcheck](https://github.com/koalaman/shellcheck).

Items 4–7 are working as designed, or as Parsec dictates. Changing them would
change output that existing users, tests and editor integrations depend on, so
they belong here rather than in an upstream issue.
