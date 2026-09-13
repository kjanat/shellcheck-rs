# Open divergences

Every input where the Rust port and the Haskell oracle still disagree, as of the
last `fuzz` run. These are **port defects**, not inherited quirks — for the
quirks the port reproduces on purpose, and the one place it deliberately does
not, see `PARITY-NOTES.md`.

Reproduce the whole set (deterministic, seed 0):

```sh
cargo conformance-fuzz --max-findings 40
# fuzz: 2000 inputs checked, 12 distinct divergences
# oracle crashed on 1 input(s) -- an upstream defect, not a divergence
```

The crash line is not one of these: the oracle dies on it and has no answer to
compare against (`PARITY-NOTES.md` items 4 and 5, and **Z3** below). The harness
re-runs such a batch one script at a time, so the crash costs that one input and
nothing else.

A seed covers what it happens to generate. Two entries below (A3, B1) were found
by other seeds and are still open under this one; a run at `--seed 1013
--iterations 4000` finds around 40, the extra ones being further spellings of
the classes already listed here.

Reproduce one entry: run its command against both binaries. `shellcheck` is the
oracle, `rshellcheck` the port.

```sh
printf '%s' '<the script>' | shellcheck  -s <dialect> -f gcc -
printf '%s' '<the script>' | rshellcheck -s <dialect> -f gcc -
```

The `gate` is clean, so none of these is exposed by the extracted upstream
`prop_` corpus under full-pipeline comparison — which is the point of the
fuzzer. That is a weaker statement than "no upstream test covers them": the gate
replays the *script* each property names through the whole pipeline, not the
isolated helper (`verifyTree`, `verifyCodes`, …) the property originally called,
and it only covers the properties whose script it can extract — 2026 of 2252
definitions, which the gate now prints on every run rather than leaving implied.
The other 226 test the Fixer, the Checker's IO, `ASTLib` helpers and the like,
and have no shell snippet to replay.

Where an entry's port-side half can be checked without the oracle, it also has a
`#[should_panic]` test in `rust/crates/shellcheck-rs/src/parser/tests.rs`
("known divergences"), which asserts what upstream does. Fixing the port makes
the assertion pass, which makes the test *fail* — the reminder to delete the
marker and the entry here in the same commit.

Grouped by cause, worst user impact first.

**A divergence is not a verdict.** "The port differs here" and "the port is worse
here" are separate claims, and most entries below are only the first. For a
drop-in replacement, direction does not matter: a *nicer* message that differs
breaks a golden file, an editor integration or a tuned `# shellcheck disable=`
line exactly as hard as a worse one, so every entry is a defect regardless.
Where one side is genuinely the better diagnostic, the entry says so — including
the cases where that side is this port, listed in **Z** below. Fixing those
means deliberately making the port's output less useful, because agreement is
the contract.

## Z. Where the port's own output is the better one

Recorded so the trade is explicit, not so it is kept. Each is still a divergence
and each is still due to be matched to upstream.

### Z1. An empty SC1072 message where the port has a real one

```sh
printf '%s' '[#' | shellcheck -s sh -f gcc -
```

|        |                                                                                |
| ------ | ------------------------------------------------------------------------------ |
| oracle | `1:3: error:  Fix any mentioned problems and try again. [SC1072]` — no message |
| port   | `1:3: error: Expected test to end here (don't wrap commands in []/[[]]). ...`  |

Upstream's SC1072 carries the empty string here, so the rendered line has two
spaces after `error:` and tells the reader nothing. The port names the actual
expectation. Same class as the `S=('` / `y=("` pair in **D1**, where the two
tools name different-but-equally-true expectations; this is the sub-case where
one of them names none at all.

### Z2. A whole file discarded over one unterminated directive value

```sh
printf '#shellcheck disable="\nfor f in $();do t$(d)"" $n;done\nx=(*)\n' | shellcheck -s sh -f gcc -
```

|        |                                                                               |
| ------ | ----------------------------------------------------------------------------- |
| oracle | SC1073 + SC1072 and nothing else: the file is unparseable, no analysis at all |
| port   | SC1125 (invalid key=value pair) and then the file's 10 real findings          |

A stray quote in a comment costs the user every diagnostic in the file upstream.
The port reports the malformed directive and analyses the script anyway, which
is what a person would want. It is still **B2**, and still has to be matched.

### Z3. Two inputs that kill upstream outright

`x=$(coproc foo)` and `$'\U110000'` end the Haskell process with a pattern-match
failure and a partial `chr` — no diagnostics, no JSON, every other file in the
invocation lost. The port analyses both. There is no oracle output to agree
with, so these are not divergences at all; see `PARITY-NOTES.md` items 4 and 5,
and the harness counts them separately as `oracle crashed on N input(s)`.

### Z4. `! # comment`

The one *sanctioned* deviation: upstream declares the file unparseable, bash
runs it, and `bash -n` agrees with the port. Unlike Z1–Z3 this one is kept,
because the harness can justify it from a shell's verdict rather than from
taste. See `PARITY-NOTES.md` item 2 and
`rust/crates/conformance/src/deviations.rs`.

## A. The port gives up where upstream carries on

The expensive class: a parse failure costs the file its whole analysis, so the
user loses every real finding in it.

### A2. `!` glued to a keyword inside a loop

```sh
printf '%s' 'until x; !do y;done' | shellcheck -s sh -f gcc -
```

|        |                                                                                          |
| ------ | ---------------------------------------------------------------------------------------- |
| oracle | SC1057 "Did you forget the 'do'", SC1035, SC1010, SC1058 "Expected 'do'", SC1073, SC1072 |
| port   | SC1073, SC1035, SC1072                                                                   |

Shrunk from `printf $r\ncoproc E {until [[ ?() ]];!do $@;done`, where it costs
10 findings — including every finding on line 1, which is syntactically fine.
Both sides fail, but upstream fails *later* and reports the loop diagnostics
(SC1057/SC1058) on the way; the port commits at the `!do` and never reaches
them. Related to `g_Bang`: `!do` has no space, so SC1035 fires and the `do`
should then be read as a word (SC1010).

### A3. `function` used as a command name

```sh
printf '%s' 'function | { x; }' | shellcheck -s dash -f gcc -
```

|        |                                                   |
| ------ | ------------------------------------------------- |
| oracle | nothing: it parses                                |
| port   | `SC1073` "Couldn't parse this function", `SC1072` |

Shrunk from a three-line generated script where it costs 13 findings.

In dash `function` is not a keyword, so this is a command named `function` piped
into a brace group, and `dash -n` accepts it. (bash, where `function` *is* a
keyword, rejects it — which is why this entry is dialect-specific.) Upstream's
`try readFunctionSignature` rewinds cleanly when the name turns out to be `|`;
the port's attempt consumes and commits, so the pipeline reading is never
tried.

## B. The port accepts what upstream rejects

The port is too lenient here, so it reports analysis findings on a file upstream
refuses outright. Whether upstream or the port is *right* is a separate
question — the shells accept neither — but they must agree.

### B1. `[[#` … `]]`

```sh
printf '%s' '[[# =x ]]' | shellcheck -s ksh -f gcc -
```

|        |                                                                |
| ------ | -------------------------------------------------------------- |
| oracle | SC1035, `SC1073` "Couldn't parse this test expression", SC1072 |
| port   | SC1035, **SC2050** "This expression is constant", SC1035       |

The port reads `#` as a word and carries on; upstream's test-expression parser
rejects it.

### B2. An unterminated quoted directive value

```sh
printf '#shellcheck disable="\nfor f in $();do $(d)$n;done\nfor f in ${}$@;do $[1] ; done\n' | shellcheck -s ksh -f gcc -
```

|        |                                                                            |
| ------ | -------------------------------------------------------------------------- |
| oracle | `SC1073` "Couldn't parse this shellcheck directive" at 1:1, SC1072 at 1:22 |
| port   | SC1125, then SC2046, SC2154, SC2086, SC2034, SC2068, SC2007                |

`disable="` with no closing quote is a parse error upstream. The port's
`plain_or_quoted` falls back to the unquoted reading, emits SC1125 and analyses
the file.

## C. The wrong production is named on a parse failure

SC1073 names the construct that failed and SC1009 the one it was inside. The
port picks different frames than upstream. Same class as `PARITY-NOTES.md` item
1 — upstream's pairing is itself residue from abandoned productions, which is
why matching it exactly is fiddly.

### C1. ksh-style `${ ..; }`

```sh
printf '%s' '${ '                 | shellcheck -s sh   -f gcc -
printf '%s' "select x in ''\${ "  | shellcheck -s dash -f gcc -
```

|                |                                                                                                             |
| -------------- | ----------------------------------------------------------------------------------------------------------- |
| oracle (`${ `) | SC1073 "ksh-style `${ ..; }` command expansion", SC1009 "simple command", SC1072 "Expected a command"       |
| port           | SC1073 "parameter expansion", SC1009 "ksh-style `${ ..; }` command expansion", SC1072 with an empty message |

The `select` variant differs further: upstream names the select loop in SC1009
and the port emits no SC1009 at all.

### C2. Regex grouping in `[ .. =~ .. ]`

```sh
printf '%s' '[x =~""("' | shellcheck -f gcc -
```

|        |                                                                              |
| ------ | ---------------------------------------------------------------------------- |
| oracle | SC1009 "in this regex grouping" at 1:8, SC1073 "double quoted string" at 1:9 |
| port   | SC1009 "in this regex" at 1:6, SC1073 "regex grouping" at 1:8                |

`[o =~ $"` is the same entry with a translated string in place of the grouping:
upstream names the regex in SC1009 and the double quoted string in SC1073, the
port names the test expression and the regex.

### C4. A failed subshell inside a backtick expansion

```sh
printf '%s' '`(){``' | shellcheck -f gcc -
```

|        |                                                                                                                                                           |
| ------ | --------------------------------------------------------------------------------------------------------------------------------------------------------- |
| oracle | SC1009 "backtick expansion", SC1009 "simple command", SC1073 "explicit subshell" at 1:2, SC1072 at 1:4, SC1073 "backtick expansion" at 1:6, SC1072 at 1:7 |
| port   | SC1009 "simple command", **SC1070** "Parsing stopped here" at 1:4, SC1073 "backtick expansion", SC1072                                                    |

The port loses the inner failure's own SC1073/SC1009 pair — the subshell frame
is gone by the time the backtick expansion reports — and emits SC1070 instead,
which upstream only uses when nothing better is known.

### C3. Array assignment vs the simple command around it

```sh
printf '%s' 'S[]=$"' | shellcheck -s sh -f gcc -
```

|        |                                                               |
| ------ | ------------------------------------------------------------- |
| oracle | SC1073 "variable assignment", SC1009 "simple command", SC1072 |
| port   | SC1073 "simple command", **no SC1009**, SC1072                |

## D. Which failure wins, and what it says

The port and the oracle fail on the same input, at nearly the same place, but
disagree about the position by one column or about whether the message is the
explicit one or Parsec's empty one. Cosmetic for a human, fatal for the gate.

### D1. Empty message where upstream has an explicit one

```sh
printf '%s' 'x=((`'     | shellcheck -s ksh  -f gcc -   # oracle: empty  / port: "Expected ) to close array assignment"
printf '%s' '$((())'    | shellcheck -s dash -f gcc -   # oracle: "Expected a double )) to end the $((..))" / port: empty
printf '%s' "<<'"       | shellcheck -s sh   -f gcc -   # oracle: "Expected end of single quoted string" at 1:4 / port: empty at 1:3
printf '%s' 'y=("'      | shellcheck -f gcc -           # oracle: "Expected end of double quoted string" / port: "Expected ) to close array assignment"
printf '%s' "S=('"      | shellcheck -s ksh  -f gcc -   # oracle: "Expected end of single quoted string" / port: "Expected ) to close array assignment"
printf '%s' '[#'        | shellcheck -s sh   -f gcc -   # oracle: empty / port: "Expected test to end here (don't wrap commands in []/[[]])"
```

Instances in *both* directions, so the cause is not one missing message: it is
which recorded failure wins the ranking. The port ranks by (position,
has-a-message, explicit, consumed); Parsec merges by position alone and drops
empty-message errors when merging at equal positions. The `y=("` and `S=('`
pair shows the shape: at the same column the port keeps the outer array
assignment's expectation, upstream the inner string's.

### D2. Off-by-one column

```sh
printf '%s' 'until ];do ];do ' | shellcheck -f gcc -            # oracle 1:17 "Unexpected keyword/token" / port 1:16, empty
printf '%s' '(} '              | shellcheck -s busybox -f gcc -  # oracle 1:3 / port 1:4
printf '%s' 'while e;done'     | shellcheck -f gcc -             # oracle 1:13 "Unexpected keyword/token" / port 1:11 "Expected whitespace"
```

## E. A check the port has not got

### ~~E1. SC3051 on `source`~~ — fixed

Closed by the source resolver: `source /dev/null` under `-s sh` now gives
SC3046 **and** SC3051 on both sides, and the two entries this moved in
`rust/snapshot.txt` are both that. Kept here only so the numbering does not
shift; the original text follows for the record.

<details><summary>Original entry</summary>

### E1. SC3051 on `source`

```sh
printf '%s' 'source /dev/null' | shellcheck -s dash -f gcc -
```

|        |                                                                                   |
| ------ | --------------------------------------------------------------------------------- |
| oracle | SC3046 **and** SC3051, both "In dash, 'source' in place of '.' is not supported." |
| port   | SC3046 only                                                                       |

Upstream emits the same text twice, from two different checks: `checkBashisms`
(SC3046) and the source-following path (SC3051), which needs `T_SourceCommand`
— i.e. the source resolver (`-x`/`-P`/`-a`), tracked as task #24 and not yet
ported. Not a parser bug.

</details>

## Fixed since this file was started

Kept so a reader can tell a closed entry from a missed one.

- `t<<foo\n$((\nfoo` and `t<<foo\n$(\nfoo` — the port recovered inside a here
  document body where `many doubleQuotedPart` must fail. Fixed by making the
  three hand-rolled `many doubleQuotedPart` loops a real alternation (`84bd3ad`).
- `''\n!#` — a spurious SC1035, because `void spacing1 <|> …` is unreachable
  once the comment is consumed (`df11df5`).
- `(function -{(e)} )`, `while 2;do(-(){""``;} )done`, `[[$(()) =0 ] ` — spans
  a character too wide, from `endSpan` running after the trailing `spacing`
  rather than before it (`df11df5`).
- `((())` — column of a failed `string "))"`, which Parsec reports where the
  string started (`df11df5`).
- `[* '` — the "Expected comparison operator" message was never recorded, so a
  weaker failure won (`df11df5`).
- `! &` — `readIoSource` consumes the `&` before its `lookAhead` turns the
  source down, and that error outlives the `try`, so the reported position is
  past the `&` (fixed in the commit that added this file).
- `!/env -` and `#!n<TAB>env bash` — SC1008 fired on the first and not on the
  second, because `executable_from_shebang` treated the word `env` *anywhere*
  in the shebang as the env form, and its `fromEnvArgs` did not drop leading
  flags. Now the `/env +(-S|--split-string=?)? *(.*)` regex decides, exactly as
  `ASTLib.hs` does, and all 11 `prop_executableFromShebang` cases are tests.
- `declare "f"=""` — no SC3044 (nor SC3043 for `local`), because the port
  suppressed both when the last word looked like an assignment. Upstream has no
  such condition.
- `echo a` / `|| echo b` on the next line — SC1133 was not ported at all, so
  every "you meant to put the operator at the end of the previous line" case was
  silently missing. `checkBadBreak` now runs after `readNewlineList` and
  `readLineBreak`.
- `readonly f=(` — `readModifierSuffix`'s assignment failure consumed input and
  was retried as a word, giving SC1036/SC1088 where upstream fails the command.
