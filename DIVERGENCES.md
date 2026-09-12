# Open divergences

Every input where the Rust port and the Haskell oracle still disagree, as of the
last `fuzz` run. These are **port defects**, not inherited quirks — for the
quirks the port reproduces on purpose, and the one place it deliberately does
not, see `PARITY-NOTES.md`.

Reproduce the whole set (deterministic, seed 0):

```sh
cargo run --release -p conformance -- fuzz --max-findings 40
# fuzz: 2000 inputs checked, 15 distinct divergences
```

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

## A. The port gives up where upstream carries on

The expensive class: a parse failure costs the file its whole analysis, so the
user loses every real finding in it.

### A1. A bare `time` before a pipe

```sh
printf '%s' 'time |y' | shellcheck -s dash -f gcc -
```

|        |                                                         |
| ------ | ------------------------------------------------------- |
| oracle | nothing: it parses                                      |
| port   | `SC1073` "Couldn't parse this simple command", `SC1072` |

Shrunk from `${a/}$()\|time \|s{,}``$(e>t)`, where it costs 11 findings.

In dash `time` is an ordinary command name, and `dash -n` accepts this; bash,
where `time` is a keyword, rejects it. So upstream is right to parse it for a
POSIX target, and the port's `read_command` rejects it and commits, losing the
pipeline and everything after it.

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
```

Three instances, and they point in *both* directions, so the cause is not one
missing message: it is which recorded failure wins the ranking. The port ranks
by (position, has-a-message, explicit, consumed); Parsec merges by position
alone and drops empty-message errors when merging at equal positions.

### D2. Off-by-one column

```sh
printf '%s' 'until ];do ];do ' | shellcheck -f gcc -            # oracle 1:17 "Unexpected keyword/token" / port 1:16, empty
printf '%s' '(} '              | shellcheck -s busybox -f gcc -  # oracle 1:3 / port 1:4
```

## F. Optional checks the port has not got

### F1. `check-set-e-suppressed` and `check-extra-masked-returns`

```sh
shellcheck --list-optional | grep -c '^name:'    # oracle: 11, port: 9
```

Nine of upstream's eleven optional checks are ported and agree with the oracle
on the full json1 payload, `--enable` and `enable=` alike. Two are not:
`check-set-e-suppressed` (SC2310/SC2311) and `check-extra-masked-returns`
(SC2312). They need `doTransform` and the declaring-command machinery.

Until they exist the port leaves them out of `--list-optional` as well, so the
catalog never advertises a name that silently does nothing — which is how this
gap stayed invisible in the first place. The cost is that
`--list-optional` differs from the oracle's, and `--enable` on either name is
accepted and ignored (upstream ignores unknown names too, so that part matches).

Nothing in `gate` or `fuzz` can see any of this: neither ever passes `--enable`,
so both tools stay silent and agree. That is the hole to close next, not just
the two checks.

## E. A check the port has not got

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
