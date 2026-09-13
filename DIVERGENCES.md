# Open divergences

Every input where the Rust port and the Haskell oracle still disagree, as of the
last `fuzz` run. These are **port defects**, not inherited quirks — for the
quirks the port reproduces on purpose, and the one place it deliberately does
not, see `PARITY-NOTES.md`.

Reproduce the whole set (deterministic, seed 0):

```sh
cargo conformance-fuzz --max-findings 40
# fuzz: 2000 inputs checked, 0 distinct divergences
# oracle crashed on 1 input(s) -- an upstream defect, not a divergence
```

The crash line is not one of these: the oracle dies on it and has no answer to
compare against (`PARITY-NOTES.md` items 4 and 5, and **Z3** below). The harness
re-runs such a batch one script at a time, so the crash costs that one input and
nothing else.

A seed covers what it happens to generate, and seed 0 is now clean. Wider runs
are not, and CI fuzzes with a fresh seed every run (`--seed $GITHUB_RUN_NUMBER
--iterations 4000`), so this file lists what the last two wide runs found:

```sh
cargo run --release -p conformance -- fuzz --oracle .cache/shellcheck-oracle \
    --seed 1013 --iterations 4000 --max-findings 60
# fuzz: 4000 inputs checked, 13 distinct divergences
cargo run --release -p conformance -- fuzz --oracle .cache/shellcheck-oracle \
    --seed 148 --iterations 4000
# fuzz: 4000 inputs checked, 1 distinct divergences
```

Those 14 are in **G** below. Do not read the seed-0 count as the size of the
problem.

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

Where an entry's port-side half can be checked without the oracle, it gets a
`#[should_panic]` test in `rust/crates/shellcheck-rs/src/parser/tests.rs`, which
asserts what upstream does. Fixing the port makes the assertion pass, which
makes the test *fail* — the reminder to delete the marker and the entry here in
the same commit. That is how A1, A3, B1, B2 and E1 came to be closed. There are
no markers at the moment: the entries in **G** were found by a wide run and have
not been dug into yet, so nothing can be asserted about them beyond the
oracle's output.

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

### Z3. Two inputs that kill upstream outright

`x=$(coproc foo)` and `$'\U110000'` end the Haskell process with a pattern-match
failure and a partial `chr` — no diagnostics, no JSON, every other file in the
invocation lost. The port analyses both. There is no oracle output to agree
with, so these are not divergences at all; see `PARITY-NOTES.md` items 4 and 5,
and the harness counts them separately as `oracle crashed on N input(s)`.

### Z4. `! # comment`

The one *sanctioned* deviation: upstream declares the file unparseable, bash
runs it, and `bash -n` agrees with the port. Unlike Z3 this one is kept, because
the harness can justify it from a shell's verdict rather than from taste — and
only from a shell's verdict: for `-s dash`, which rejects `! # c`, the sanction
is refused and the divergence stands. See `PARITY-NOTES.md` item 2 and
`rust/crates/conformance/src/deviations.rs`.

## G. Found by the wide runs, not yet dug into

Sections A through F are gone; their entries are all in **Fixed** below. This
one keeps a fresh letter so a closed `A1` and an open one never share a name.
Each row is one shrunk reproducer as the fuzzer printed it; the dialect is the
`-s` it was found under, and `none` means no `-s` and no shebang.

| dialect | script                                          | what differs                                                        |
| ------- | ----------------------------------------------- | ------------------------------------------------------------------- |
| bash    | `case "" in x)while[$() ]do '';done\n""!()""\n` | SC1072 message: upstream `Expected a command`, port none            |
| ksh     | `case } in *)t\n`                               | same shape as the row above                                         |
| sh      | `e<;<<$`                                        | port adds SC1044 for a here document the failed parse never got to  |
| sh      | `['' =~$"e\n"$`                                 | port misses SC1078/SC1079 on the suspicious quote                   |
| none    | `a[$(echo $))]=`                                | port misses SC2116 inside an array index                            |
| none    | `"${a[]s[]}"`                                   | port adds SC2180 for an index that is not two-dimensional           |
| none    | `for((i;{ `                                     | SC1072: upstream `1:10 Unexpected .`, port `1:9` with no message    |
| none    | `o{1..$n}\t`                                    | SC2051 span: upstream the whole brace expansion, port one character |
| sh      | `(read _ '');$_`                                | port adds SC3028 for `$_`                                           |
| sh      | `#shellcheck shell= d`                          | SC1072: upstream `1:19` with no message, port `1:21 Expected '='..` |
| dash    | `<<foo $('\nfoo`                                | SC1072 at `2:4` upstream, `2:1` port                                |
| dash    | `case - in[)for x in '' do eval(`               | port misses SC1098 from `eval(`                                     |
| sh      | `{coproc { for((;;))do c """`                   | SC1073/SC1009 name different frames, and different positions        |
| busybox | `coproc $COPROC`                                | port adds SC3028 for `COPROC`                                       |

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

- `time |y`, `time ||cd` (was **A1**) — `readTimeSuffix` sits under `option []`,
  and on a pipe `readPipeline` fails without consuming, so bare `time` is a
  command. The port took its mark before the space after the name, which
  `readCmdWord`'s `<* spacing` has already eaten, so a suffix that had only
  stepped over that space looked like it had consumed. A whole file's analysis.
- `until x; !do y;done` (was **A2**) — fixed by the same round; upstream fails
  later and reports the loop diagnostics on the way.
- `function | { x; }` (was **A3**) — `functionSignature <- try
  readFunctionSignature` covers everything up to the body, so a word that cannot
  be a function name rewinds to the keyword and `function` is the command name
  it is in a POSIX shell. The port propagated the name failure instead.
- `[[# =x ]]`, `[ -x# ]` (was **B1**) — `condSpacing` reads `allspacing`, which
  ends in `optional readComment`, so the `#` opens a comment and the `-x` is
  left with no argument. The port read it as a word and carried on.
- `#shellcheck disable="` (was **B2** and **Z2**) — `quoted` reads the opening
  quote before `many1 (noneOf (c:"\n"))` and `char c`, so both failures have
  consumed and `plainOrQuoted`'s `<|>` cannot fall back to the unquoted reading.
  The wiki's SC1072 page documents an incomplete directive as a parse error, so
  upstream's behaviour here is intended rather than incidental. The port emitted
  SC1125 and analysed the file.
- `${ `, `select x in ''${ ` (was **C1**) — `readDollarBraceCommandExpansion`
  consumes `${` and the space inside its own `try`, so past that the `<|>` has
  no `readDollarBraced` to fall back to. The port fell through and stacked a
  second frame, and SC1073 named the wrong one.
- `[x =~""("`, `[1 =~ .(` (was **C2**) — `many1 readPart` in a regex takes a
  consuming failure down with it, and `readLiteralString ")"` records an error
  where it stood. The port did neither.
- ``` `(){``` `` (was **C4**) — `readSubshell`'s body is `readCompoundList`, a
  non-empty term, so `()` is a subshell missing its command rather than an empty
  one. The port parsed it and then tripped over the leftover `{` with SC1070.
- `S[]=$"` (was **C3**) — `value <- readArray <|> readNormalWord` has nothing
  after it, so a word that failed having consumed takes the assignment with it
  and the `called "variable assignment"` frame names the failure.
- `x=((` ` `` `, `y=("`, `S=('` (was **D1**) — `readElement `reluctantlyTill` char ')'` ends on `<|> return []`, out of reach of a consuming failure, so the
  element's own error stands rather than "Expected ) to close array assignment".
- `$((())` (was **D1**) — the message was in the port as a comment and never
  passed to the failure.
- `<<'`, `<<>`, `<<$(` (was **D1**) — `readStringForParser` restored the outer
  failure over the inner one. `parseForgettingContext` fails with `fail ""` and
  the `<|>` above it merges, so the further of the two stands.
- `[#` (was **D1** and **Z1**) — same cause; upstream's empty message is what
  the merge leaves, and the port's own expectation is not what Parsec reports.
- `until ];do ];do `, `(} `, `while e;done`, `f(){:;until :;done` (was **D2**) —
  two causes. `g_Rbrace` is a bare `char '}'` while every other keyword token is
  a `tryToken`/`tryWordToken` that ends `spacing`, so `}` must not take the
  spacing with it; and a `try` that fails merges its error with the one before
  it rather than dropping it, which `consume_keyword`'s rewound reads were not
  doing, so the `do` inside `done` buried `readPipeline`'s complaint.
- ``for f in "``, ``for i in ""$()"`` — `readInClause <|> (optional readSequentialSep
  >> return [])``recovers only while``g_In``has not matched; past the keyword a
  >> failed word list has consumed. The port went looking for``do` and invented an
  >> SC1058.
- `a[$(` — `readArrayIndex` was a second, stale copy of `readStringForParser`
  that also forgot to restore the commitment, so the parse ended committed with
  no failure recorded and **reported nothing at all**. It now calls the one
  definition.
- `builtin ` `` ` `` , `"";builtin {d}>` — the `builtin` first-argument peek is
  `ignoreProblemsOf . optionMaybe . try . lookAhead`, and `optionMaybe` makes it
  total, so `p <* put systemState` always runs and puts back the problems and
  the context frames. The port kept both.
- `{c|}` — `unexpecting readKeyword` belongs at the top of `readPipeline`, once
  per statement. Hoisted into `read_command` it also rejected the command after
  a `|`, so the `}` was never read as the word it is.
- `if[ ]{` — Parsec records an error for running out of input like any other,
  and the port returned a bare failure, so the furthest position reached was
  short and a nearer error won.
- `[o ">`, `[x '>`, `until['' '-g` (was **F1**) — `readEscaped`'s `withQuotes`
  reads the quote and the operator and then fails on `char c` at the end of
  the input; the `try` around it rewinds the cursor, not the error, and
  nothing later gets further. The port recorded nothing there, so its own
  "Expected test to end here" at the operator won instead. Not a redirection
  at all, whatever the earlier entry guessed.
- `[(z "` — same `try`, the other direction: a `try` that fails *merges* its
  error with the one before it, so the "Expected comparison operator" left at
  the same position by the operator attempt survives `readEscaped (string
  ")")`. The port's quote read had dropped it.
- `[ ` — `readConditionContents <|> (guard ..; lookAhead (string "]"); ..)`:
  with nothing where the bracket belongs the alternative fails too, and the
  `fail "Expected test to end here"` a line later is never reached. The port
  built an empty condition and went on to ask for the bracket.
- `[-z$('` — `option Nothing $ Just <$> readCmdName` cannot recover from a
  name that consumed, and the cursor stays past it. The port rewound, so the
  `called "simple command"` around it took the failure for a clean one and
  popped the frame the single quoted string had left, and SC1073 named the
  wrong production.
- `echo >#` then a newline — `readFilename`'s `many1` reading nothing is a
  failure Parsec records at the newline. The port recorded nothing, ended the
  parse committed with no failure to report, and **reported nothing at all**.
- `let "`, `let '` — `readLetSuffix = many1 (readIoRedirect <|> try
  readLetExpression <|> readCmdWord)`: only the expression is behind a `try`,
  so the word's consuming failure is the command's. The port dropped the
  argument and analysed a `let` with none.
- `let $(source x)` — `subParse` runs on the same parser state, so the SC1090
  that `readSource` notes inside the arithmetic stays noted. The port's
  arithmetic sub-parser kept only the tree.
- `r= $()`, `r[]=x $()` — `checkSpuriousExpansion` matches `T_SimpleCommand _
  _ [T_NormalWord _ [word]]` and never looks at the assignments. The port
  required there to be none.
- `while [[ -e foo ]]$ do ..` — `isFollowedBy readNormalWord`: when the word
  reads, `lookAhead` replies with an unknown error at its own position, which
  loses the merge against what stood before, so the failures the word ran into
  finding its end are not the furthest one. Same for the `builtin` peek.
