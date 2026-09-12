//! Ported check batch y. See rust/PORTING.md.
//!
//! Faithful ports of:
//!   * SC2070 — checkUnquotedN (Analytics.hs): `[ -n $foo ]` with an unquoted,
//!     word-splitting argument in a single-bracket test.
//!   * SC2240 — checkSourceArgs (Checks/Commands.hs): the `.`/`source` dot
//!     command given arguments under sh/dash, which do not support them.
//!
//! Helpers are private to this module (ported from ASTLib / AnalyzerLib), so
//! the module does not touch shared files that parallel agents also edit.
use crate::analyzer_lib::arguments;
use crate::analyzer_lib::is_array_expansion;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::get_word_parts;
use crate::astlib::is_command_substitution;
use crate::astlib::will_split;
use crate::checks::batch_t::dispatch_exactly;
use crate::interface::Shell;

pub fn register(c: &mut Checker) {
    c.node(check_unquoted_n);
    c.node(check_source_args);
    c.node(check_source_not_followed);
}

// ===========================================================================
// Shared local helpers (ported from ASTLib).
// ===========================================================================

// ===========================================================================
// SC2070 — checkUnquotedN
// ===========================================================================
//
// checkUnquotedN _ (TC_Unary _ SingleBracket "-n" t) | willSplit t =
//     unless (any isArrayExpansion $ getWordParts t) $ -- There's SC2198 for these
//        err (getId t) 2070 "-n doesn't work with unquoted arguments. Quote or use [[ ]]."
// checkUnquotedN _ _ = return ()

fn check_unquoted_n(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Unary { typ, op, token } = &*t.inner {
        if *typ == ConditionType::SingleBracket
            && op == "-n"
            && will_split(token)
            && !get_word_parts(token).iter().any(|p| is_array_expansion(p))
        {
            err(
                out,
                token.id(),
                2070,
                "-n doesn't work with unquoted arguments. Quote or use [[ ]].",
            );
        }
    }
}

// ===========================================================================
// SC2240 — checkSourceArgs
// ===========================================================================
//
// checkSourceArgs = CommandCheck (Exactly ".") f
//   where
//     f t = whenShell [Sh, Dash] $
//         case arguments t of
//             (file:arg1:_) -> warn (getId arg1) 2240 $
//                 "The dot command does not support arguments in sh/dash. Set them as variables."
//             _ -> return ()

fn check_source_args(params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, ".") {
        Some(x) => x,
        None => return,
    };
    // whenShell [Sh, Dash]
    if !matches!(params.shell, Shell::Sh | Shell::Dash) {
        return;
    }
    let args = arguments(&te);
    if args.len() >= 2 {
        // (file:arg1:_)
        let arg1 = &args[1];
        warn(
            out,
            arg1.id(),
            2240,
            "The dot command does not support arguments in sh/dash. Set them as variables.",
        );
    }
}

// ===========================================================================
// SC1090 / SC1091 — readSource (Parser.hs)
// ===========================================================================
//
// In the Haskell implementation these are emitted by the parser's `readSource`
// when it encounters a `.`/`source` command (`isCommand ["source", "."] cmd`,
// i.e. a command whose name is a single `T_Literal` equal to `source` or `.`):
//
//   readSource t@(T_Redirecting _ _ (T_SimpleCommand cmdId _ (cmd:args'))) = do
//       let file = getFile args'
//       override <- getSourceOverride
//       let literalFile = do
//           name <- override `mplus` (getLiteralString =<< file)
//                            `mplus` (stripDynamicPrefix =<< file)
//           guard . not $ "~/" `isPrefixOf` name   -- avoid literal tilde
//           return name
//       let fileId = fromMaybe (getId cmd) (getId <$> file)
//       case literalFile of
//           Nothing -> parseNoteAtId fileId WarningC 1090
//               "ShellCheck can't follow non-constant source. Use a directive to specify location."
//           Just filename -> ...
//               -- /dev/null is always readable as ""
//               -- otherwise siFindSource / siReadFile try to resolve+read; on
//               -- failure: parseNoteAtId fileId InfoC 1091 ("Not following: " ++ err)
//
// This port does not follow/parse sourced files. For the corpus (stdin only,
// external sources off, no source paths, target not on disk) resolution always
// fails: `findSourceFile` returns the literal name unchanged and `siReadFile`
// (the CLI's `ioInterface`) rejects it because it is not an input, producing
//     "<file> was not specified as input (see shellcheck -x)."
// So we faithfully replicate that decision: SC1090 for a non-constant target,
// SC1091 (with that exact message) for a constant one, and nothing for
// /dev/null. Following, recursion (SC1093) and parse-failure (SC1094) never
// arise here because no external file is ever read.

/// `isCommand ["source", "."] cmd`: the command word is a single `T_Literal`
/// equal to `source` or `.`. (`builtin`/slash forms are deliberately excluded,
/// matching the parser — unlike SC2240's dispatch.)
fn is_source_command_word(cmd: &Token) -> bool {
    if let InnerToken::T_NormalWord(parts) = &*cmd.inner {
        if let [only] = &parts[..] {
            if let InnerToken::T_Literal(s) = &*only.inner {
                return s == "source" || s == ".";
            }
        }
    }
    false
}

/// `getFile args'`: the token naming the sourced file, honouring `--` and `-p`.
fn get_source_file(args: &[Token]) -> Option<&Token> {
    let (first, rest) = args.split_first()?;
    match astlib::get_literal_string(first).as_deref() {
        Some("--") => rest.first(),
        Some("-p") => rest.get(1),
        _ => Some(first),
    }
}

/// `isStringExpansion`.
fn is_string_expansion(t: &Token) -> bool {
    use InnerToken::*;
    is_command_substitution(t)
        || match &*t.inner {
            T_DollarArithmetic(_) => true,
            T_DollarBraced { .. } => !is_array_expansion(t),
            _ => false,
        }
}

/// `stripDynamicPrefix`: for `$foo/bar` (a single leading string expansion
/// followed by a literal `/...`), yield `"." ++ "/bar"`.
fn strip_dynamic_prefix(word: &Token) -> Option<String> {
    let parts = get_word_parts(word);
    let (first, rest) = parts.split_first()?;
    if !is_string_expansion(first) {
        return None;
    }
    let rest_word = Token::new(
        Id(0),
        InnerToken::T_NormalWord(rest.iter().map(|t| (*t).clone()).collect()),
    );
    let str = astlib::get_literal_string(&rest_word)?;
    if !str.starts_with('/') {
        return None;
    }
    Some(format!(".{str}"))
}

/// `getSourceOverride`: the innermost in-scope `# shellcheck source=...`
/// directive (stopping at a source frame, mirroring `takeWhile isSameFile`).
fn get_source_override(params: &Parameters, t: &Token) -> Option<String> {
    for a in crate::analyzer_lib::get_path(params, t) {
        match &*a.inner {
            InnerToken::T_SourceCommand { .. } => return None,
            InnerToken::T_Annotation { annotations, .. } => {
                for ann in annotations {
                    if let Annotation::SourceOverride(s) = ann {
                        return Some(s.clone());
                    }
                }
            }
            _ => {}
        }
    }
    None
}

fn check_source_not_followed(params: &Parameters, t: &Token, out: &mut Out) {
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return,
    };
    let cmd = &words[0];
    if !is_source_command_word(cmd) {
        return;
    }
    let args = &words[1..];
    let file = get_source_file(args);

    // literalFile: override `mplus` literal `mplus` stripDynamicPrefix, then
    // reject a literal `~/` prefix.
    let literal_file = get_source_override(params, t)
        .or_else(|| file.and_then(astlib::get_literal_string))
        .or_else(|| file.and_then(strip_dynamic_prefix))
        .filter(|name| !name.starts_with("~/"));

    // fileId = fromMaybe (getId cmd) (getId <$> file)
    let file_id = file.map_or_else(|| cmd.id(), |f| f.id());

    match literal_file {
        None => warn(
            out,
            file_id,
            1090,
            "ShellCheck can't follow non-constant source. Use a directive to specify location.",
        ),
        Some(filename) => {
            // /dev/null is always readable as "" and yields no note.
            if filename == "/dev/null" {
                return;
            }
            info(
                out,
                file_id,
                1091,
                &format!(
                    "Not following: {filename} was not specified as input (see shellcheck -x)."
                ),
            );
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::analyzer_lib::make_parameters;
    use crate::parser::parse_script;

    fn params_for(script: &str) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, None, None)
    }

    fn produces(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }

    // checkUnquotedN (SC2070)
    #[test]
    fn prop_checkUnquotedN() {
        assert!(produces(
            check_unquoted_n,
            "if [ -n $foo ]; then echo cow; fi"
        ));
    }
    #[test]
    fn prop_checkUnquotedN2() {
        assert!(produces(check_unquoted_n, "[ -n $cow ]"));
    }
    #[test]
    fn prop_checkUnquotedN3() {
        assert!(!produces(check_unquoted_n, "[[ -n $foo ]] && echo cow"));
    }
    #[test]
    fn prop_checkUnquotedN4() {
        assert!(produces(check_unquoted_n, "[ -n $cow -o -t 1 ]"));
    }
    #[test]
    fn prop_checkUnquotedN5() {
        assert!(!produces(check_unquoted_n, "[ -n \"$@\" ]"));
    }

    // checkSourceArgs (SC2240)
    #[test]
    fn prop_checkSourceArgs1() {
        assert!(produces(check_source_args, "#!/bin/sh\n. script arg"));
    }
    #[test]
    fn prop_checkSourceArgs2() {
        assert!(!produces(check_source_args, "#!/bin/sh\n. script"));
    }
    #[test]
    fn prop_checkSourceArgs3() {
        assert!(!produces(check_source_args, "#!/bin/bash\n. script arg"));
    }

    // readSource: SC1090 (non-constant) / SC1091 (constant, not followed).
    fn only_code(f: fn(&Parameters, &Token, &mut Out), s: &str) -> Vec<i32> {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out.iter().map(|c| c.comment.code as i32).collect()
    }
    fn only_msg(f: fn(&Parameters, &Token, &mut Out), s: &str) -> Vec<String> {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out.iter().map(|c| c.comment.message.clone()).collect()
    }

    #[test]
    fn prop_source_dot_not_followed() {
        // prop_checkCommandWithTrailingSymbol7 corpus input.
        assert_eq!(only_code(check_source_not_followed, ". foo.sh"), vec![1091]);
        assert_eq!(
            only_msg(check_source_not_followed, ". foo.sh"),
            vec!["Not following: foo.sh was not specified as input (see shellcheck -x)."]
        );
    }
    #[test]
    fn prop_source_keyword_not_followed() {
        // prop_checkBashisms5 corpus input.
        assert_eq!(
            only_code(check_source_not_followed, "source file"),
            vec![1091]
        );
        assert_eq!(
            only_msg(check_source_not_followed, "source file"),
            vec!["Not following: file was not specified as input (see shellcheck -x)."]
        );
    }
    #[test]
    fn prop_source_args_still_not_followed() {
        // prop_checkSourceArgs1/3 corpus inputs: file arg is followed by more args.
        assert_eq!(
            only_msg(check_source_not_followed, "#!/bin/sh\n. script arg"),
            vec!["Not following: script was not specified as input (see shellcheck -x)."]
        );
    }
    #[test]
    fn prop_devnull_is_not_flagged() {
        // prop_canParseDevNull / prop_checkBashisms110: /dev/null yields no note.
        assert!(only_code(check_source_not_followed, "source /dev/null").is_empty());
        assert!(only_code(check_source_not_followed, ". /dev/null").is_empty());
    }
    #[test]
    fn prop_cant_source_dynamic() {
        // prop_cantSourceDynamic: a non-constant target is SC1090, not SC1091.
        assert_eq!(only_code(check_source_not_followed, ". \"$1\""), vec![1090]);
    }
    #[test]
    fn prop_cant_source_tilde() {
        // prop_cantSourceDynamic2: literal `~/` is treated as non-constant.
        assert_eq!(
            only_code(check_source_not_followed, "source ~/foo"),
            vec![1090]
        );
    }
    #[test]
    fn prop_source_override_directive_is_followed_constant() {
        // A `source=` directive supplies a constant target -> SC1091, not SC1090.
        assert_eq!(
            only_msg(
                check_source_not_followed,
                "# shellcheck source=lib\n. \"$1\""
            ),
            vec!["Not following: lib was not specified as input (see shellcheck -x)."]
        );
    }
    #[test]
    fn prop_not_a_source_command() {
        // A plain command is untouched; `builtin source` is not the parser form.
        assert!(only_code(check_source_not_followed, "echo foo").is_empty());
        assert!(only_code(check_source_not_followed, "builtin source lib").is_empty());
    }
}
