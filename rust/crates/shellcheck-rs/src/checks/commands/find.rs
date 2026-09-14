//! `find` checks from `ShellCheck.Checks.Commands`.
use super::common::*;
use super::{CommandCheck, CommandName::*};
use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::ast_lib::get_literal_string_def;
use crate::ast_lib::is_glob;
use crate::ast_lib::{get_literal_string, only_literal_string};

pub(super) fn check_find_name_glob() -> CommandCheck {
    CommandCheck::new(Basename("find"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        let args = word_args(words);
        // Consecutive pairs (a, b): warn on b when a is a glob-accepting flag and b
        // is a glob.
        for pair in args.windows(2) {
            let a = &pair[0];
            let b = &pair[1];
            if let Some(s) = get_literal_string(a) {
                if find_accepts_glob(&s) && is_glob(b) {
                    warn(
                        out,
                        b.id(),
                        2061,
                        &format!(
                            "Quote the parameter to {} so the shell won't interpret it.",
                            s
                        ),
                    );
                }
            }
        }
    })
}

pub(super) fn check_find_exec_with_single_argument() -> CommandCheck {
    CommandCheck::new(Basename("find"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        let args = word_args(words);
        // mapMaybe check . tails
        for i in 0..args.len() {
            let window = &args[i..];
            if window.len() < 3 {
                continue;
            }
            let exec = &window[0];
            let arg = &window[1];
            let term = &window[2];
            let exec_s = match get_literal_string(exec) {
                Some(s) => s,
                None => continue,
            };
            let term_s = match get_literal_string(term) {
                Some(s) => s,
                None => continue,
            };
            let cmd_s = get_literal_string_def(" ", arg);
            if !matches!(exec_s.as_str(), "-exec" | "-execdir" | "-ok" | "-okdir") {
                continue;
            }
            if !matches!(term_s.as_str(), ";" | "+") {
                continue;
            }
            if !cmd_s.chars().any(|c| c == ' ' || c == '|' || c == ';') {
                continue;
            }
            warn(
                out,
                exec.id(),
                2150,
                &format!(
                    "{0} does not invoke a shell. Rewrite or use {0} sh -c .. .",
                    exec_s
                ),
            );
        }
    })
}

pub(super) fn check_injectable_find_sh() -> CommandCheck {
    CommandCheck::new(Basename("find"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        let id_strings: Vec<(Id, String)> = word_args(words)
            .iter()
            .map(|x| (x.id(), only_literal_string(x)))
            .collect();
        injectable_match(0, &id_strings, out);
    })
}

pub(super) fn check_find_action_precedence() -> CommandCheck {
    CommandCheck::new(Basename("find"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        let list: Vec<&Token> = word_args(words).iter().collect();
        // pattern = [isMatch, const True, isParam ["-o","-or"], isMatch, const True, isAction]
        const PLEN: usize = 6;
        let mut start = 0;
        while start + PLEN <= list.len() {
            let w = &list[start..start + PLEN];
            if fap_is_match(w[0])
                && fap_is_param(w[2], &["-o", "-or"])
                && fap_is_match(w[3])
                && fap_is_action(w[5])
            {
                warn(
                    out,
                    w[5].id(),
                    2146,
                    "This action ignores everything before the -o. Use \\( \\) to group.",
                );
                return;
            }
            start += 1;
        }
    })
}

pub(super) fn check_find_without_path() -> CommandCheck {
    CommandCheck::new(Basename("find"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        let cmd = &words[0];
        let args = word_args(words);
        if !(word_has_flag(words, "help") || find_has_path(args)) {
            info(
                out,
                cmd.id(),
                2185,
                "Some finds don't have a default path. Specify '.' explicitly.",
            );
        }
    })
}

pub(super) fn check_find_redirections() -> CommandCheck {
    CommandCheck::new(Basename("find"), |params, t, out| {
        let redirecting = match get_closest_command(params, t) {
            Some(r) => r,
            None => return,
        };
        if let InnerToken::T_Redirecting { redirs, cmd } = &*redirecting.inner {
            if redirs.is_empty() {
                return;
            }
            if let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner {
                if words.len() < 2 {
                    return;
                }
                let min_redir = redirs.iter().map(|r| r.id().0).min().unwrap();
                let max_arg = words.iter().map(|w| w.id().0).max().unwrap();
                if min_redir < max_arg {
                    let min_id = redirs.iter().min_by_key(|r| r.id().0).unwrap().id();
                    warn(
                        out,
                        min_id,
                        2227,
                        "Redirection applies to the find command itself. Rewrite to work per action (or move to end).",
                    );
                }
            }
        }
    })
}

pub(super) fn word_has_flag(words: &[Token], flag: &str) -> bool {
    word_flags(words).iter().any(|(_, f)| f == flag)
}

fn find_accepts_glob(s: &str) -> bool {
    matches!(
        s,
        "-ilname"
            | "-iname"
            | "-ipath"
            | "-iregex"
            | "-iwholename"
            | "-lname"
            | "-name"
            | "-path"
            | "-regex"
            | "-wholename"
    )
}

fn find_has_path(args: &[Token]) -> bool {
    match args.split_first() {
        None => false,
        Some((first, rest)) => {
            let flag = get_literal_string_def("___", first);
            !flag.starts_with('-') || (find_is_leading_flag(&flag) && find_has_path(rest))
        }
    }
}

fn find_is_leading_flag(flag: &str) -> bool {
    const LEADING: &str = "-EHLPXdfsxO0123456789";
    flag.chars().count() <= 2 || flag.chars().all(|c| LEADING.contains(c))
}

fn injectable_pred(idx: usize, arg: &str) -> bool {
    match idx {
        0 => matches!(arg, "-exec" | "-execdir" | "-ok" | "-okdir"),
        1 => matches!(arg, "sh" | "bash" | "dash" | "ksh"),
        2 => arg == "-c",
        _ => false,
    }
}

const INJECTABLE_PATTERN_LEN: usize = 3;

/// Faithful port of the recursive `match` in checkInjectableFindSh.
fn injectable_match(test_idx: usize, items: &[(Id, String)], out: &mut Out) {
    if items.is_empty() {
        return;
    }
    if test_idx >= INJECTABLE_PATTERN_LEN {
        // Pattern fully consumed: `action` on the current head.
        let (id, arg) = &items[0];
        if arg.contains("{}") {
            warn(
                out,
                *id,
                2156,
                "Injecting filenames is fragile and insecure. Use parameters.",
            );
        }
        return;
    }
    let (_, arg) = &items[0];
    if injectable_pred(test_idx, arg) {
        injectable_match(test_idx + 1, &items[1..], out);
    }
    injectable_match(test_idx, &items[1..], out);
}

fn fap_is_param(t: &Token, strs: &[&str]) -> bool {
    match get_literal_string(t) {
        Some(s) => strs.contains(&s.as_str()),
        None => false,
    }
}

fn fap_is_match(t: &Token) -> bool {
    fap_is_param(
        t,
        &[
            "-name",
            "-regex",
            "-iname",
            "-iregex",
            "-wholename",
            "-iwholename",
        ],
    )
}

fn fap_is_action(t: &Token) -> bool {
    fap_is_param(
        t,
        &[
            "-exec", "-execdir", "-delete", "-print", "-print0", "-fls", "-fprint", "-fprint0",
            "-fprintf", "-ls", "-ok", "-okdir", "-printf",
        ],
    )
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::test_support::*;

    #[test]
    fn prop_checkFindNameGlob1() {
        assert!(emits(check_find_name_glob(), "find / -name *.php"));
    }

    #[test]
    fn prop_checkFindNameGlob2() {
        assert!(emits(
            check_find_name_glob(),
            "find / -type f -ipath *(foo)"
        ));
    }

    #[test]
    fn prop_checkFindNameGlob3() {
        assert!(!emits(check_find_name_glob(), "find * -name '*.php'"));
    }

    // ---- SC2062/2063/2022 checkGrepRe ----

    #[test]
    fn prop_checkFindWithoutPath1() {
        assert!(emits(check_find_without_path(), "find -type f"));
    }

    #[test]
    fn prop_checkFindWithoutPath2() {
        assert!(emits(check_find_without_path(), "find"));
    }

    #[test]
    fn prop_checkFindWithoutPath3() {
        assert!(!emits(check_find_without_path(), "find . -type f"));
    }

    #[test]
    fn prop_checkFindWithoutPath4() {
        assert!(!emits(
            check_find_without_path(),
            "find -H -L \"$path\" -print"
        ));
    }

    #[test]
    fn prop_checkFindWithoutPath5() {
        assert!(!emits(check_find_without_path(), "find -O3 ."));
    }

    #[test]
    fn prop_checkFindWithoutPath6() {
        assert!(!emits(check_find_without_path(), "find -D exec ."));
    }

    #[test]
    fn prop_checkFindWithoutPath7() {
        assert!(!emits(check_find_without_path(), "find --help"));
    }

    #[test]
    fn prop_checkFindWithoutPath8() {
        assert!(!emits(check_find_without_path(), "find -Hx . -print"));
    }

    // ---- SC2253 checkChmodDashr ----

    #[test]
    fn prop_checkFindExecWithSingleArgument1() {
        assert!(emits(
            check_find_exec_with_single_argument(),
            "find . -exec 'cat {} | wc -l' \\;"
        ));
    }

    #[test]
    fn prop_checkFindExecWithSingleArgument2() {
        assert!(emits(
            check_find_exec_with_single_argument(),
            "find . -execdir 'cat {} | wc -l' +"
        ));
    }

    #[test]
    fn prop_checkFindExecWithSingleArgument3() {
        assert!(!emits(
            check_find_exec_with_single_argument(),
            "find . -exec wc -l {} \\;"
        ));
    }

    // ---- SC2156 checkInjectableFindSh ----

    #[test]
    fn prop_checkInjectableFindSh1() {
        assert!(emits(
            check_injectable_find_sh(),
            "find . -exec sh -c 'echo {}' \\;"
        ));
    }

    #[test]
    fn prop_checkInjectableFindSh2() {
        assert!(emits(
            check_injectable_find_sh(),
            "find . -execdir bash -c 'rm \"{}\"' ';'"
        ));
    }

    #[test]
    fn prop_checkInjectableFindSh3() {
        assert!(!emits(
            check_injectable_find_sh(),
            "find . -ok sh -c 'rm \"$@\"' _ {} \\;"
        ));
    }

    // ---- SC2146 checkFindActionPrecedence ----

    #[test]
    fn prop_checkFindActionPrecedence1() {
        assert!(emits(
            check_find_action_precedence(),
            "find . -name '*.wav' -o -name '*.au' -exec rm {} +"
        ));
    }

    #[test]
    fn prop_checkFindActionPrecedence2() {
        assert!(!emits(
            check_find_action_precedence(),
            "find . -name '*.wav' -o \\( -name '*.au' -exec rm {} + \\)"
        ));
    }

    #[test]
    fn prop_checkFindActionPrecedence3() {
        assert!(!emits(
            check_find_action_precedence(),
            "find . -name '*.wav' -o -name '*.au'"
        ));
    }

    // ---- SC2227 checkFindRedirections ----

    #[test]
    fn prop_checkFindRedirections1() {
        assert!(emits(
            check_find_redirections(),
            "find . -exec echo {} > file \\;"
        ));
    }

    #[test]
    fn prop_checkFindRedirections2() {
        assert!(!emits(
            check_find_redirections(),
            "find . -exec echo {} \\; > file"
        ));
    }

    #[test]
    fn prop_checkFindRedirections3() {
        assert!(!emits(
            check_find_redirections(),
            "find . -execdir sh -c 'foo > file' \\;"
        ));
    }

    // ---- SC2176/2177 checkTimedCommand ----
}
