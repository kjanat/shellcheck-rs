//! Privilege-elevation checks (sudo/doas/run0) from `ShellCheck.Checks.Commands`.
use super::{CommandCheck, CommandName::*};
use crate::analyzer_lib::arguments;
use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::ast_lib;
use crate::ast_lib::oversimplify_concat;
use crate::cfg::get_bsd_opts;

pub(super) fn check_sudo_args(cmd: &'static str) -> CommandCheck {
    CommandCheck::new(Basename(cmd), move |_params, te, out| {
        let opts = match get_bsd_opts("vAknSbEHPa:g:h:p:u:c:T:r:", arguments(te)) {
            Some(o) => o,
            None => return,
        };
        // find (null . fst) opts  -> first operand
        if let Some((_, (command_arg, _))) = opts.iter().find(|(name, _)| name.is_empty()) {
            if let Some(command) = ast_lib::get_literal_string(command_arg) {
                if SUDO_BUILTINS.contains(&command.as_str()) {
                    warn(
                        out,
                        te.id(),
                        2232,
                        &format!(
                            "Can't use sudo/doas/run0 with builtins like {}. Did you want sudo/doas/run0 sh -c .. instead?",
                            command
                        ),
                    );
                }
            }
        }
    })
}

/// `checkSudoRedirect cmd` for each of `privilegeElevationCommands`: a
/// redirect on the enclosing `T_Redirecting` applies to the shell, not the
/// elevated command.
pub(super) fn check_sudo_redirect(cmd: &'static str) -> CommandCheck {
    CommandCheck::new(Basename(cmd), move |params, t, out| {
        let Some(t_redir) = get_closest_command(params, t) else {
            return;
        };
        if let InnerToken::T_Redirecting { redirs, .. } = &*t_redir.inner {
            for redir in redirs {
                sudo_redirect_warn_about(redir, out);
            }
        }
    })
}

const SUDO_BUILTINS: [&str; 25] = [
    "cd", "command", "declare", "eval", "exec", "exit", "export", "hash", "history", "local",
    "popd", "pushd", "read", "readonly", "return", "set", "source", "trap", "type", "typeset",
    "ulimit", "umask", "unset", "wait", "builtin",
];

fn sudo_redirect_warn_about(redir: &Token, out: &mut Out) {
    use InnerToken::*;
    let T_FdRedirect { fd, target } = &*redir.inner else {
        return;
    };
    let T_IoFile { op, file } = &*target.inner else {
        return;
    };
    // special file = concat (oversimplify file) == "/dev/null"
    if !(fd.is_empty() || fd == "&") || oversimplify_concat(file) == "/dev/null" {
        return;
    }
    match &*op.inner {
        T_Less => info(
            out,
            op.id(),
            2024,
            "sudo/doas/run0 doesn't affect redirects. Use sudo cat file | ..",
        ),
        T_Greater => warn(
            out,
            op.id(),
            2024,
            "sudo/doas/run0 doesn't affect redirects. Use ..| sudo tee file",
        ),
        T_DGREAT => warn(
            out,
            op.id(),
            2024,
            "sudo/doas/run0 doesn't affect redirects. Use .. | sudo tee -a file",
        ),
        _ => {}
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::test_support::*;

    #[test]
    fn prop_checkSudoRedirect1() {
        assert!(produces(
            check_sudo_redirect("sudo"),
            "sudo echo 3 > /proc/file"
        ));
    }

    #[test]
    fn prop_checkSudoRedirect2() {
        assert!(produces(check_sudo_redirect("doas"), "doas cmd < input"));
    }

    #[test]
    fn prop_checkSudoRedirect3() {
        assert!(produces(check_sudo_redirect("run0"), "run0 cmd >> file"));
    }

    #[test]
    fn prop_checkSudoRedirect4() {
        assert!(produces(check_sudo_redirect("sudo"), "sudo cmd &> file"));
    }

    #[test]
    fn prop_checkSudoRedirect5() {
        assert!(!produces(check_sudo_redirect("sudo"), "sudo cmd 2>&1"));
    }

    #[test]
    fn prop_checkSudoRedirect6() {
        assert!(!produces(check_sudo_redirect("doas"), "doas cmd 2> log"));
    }

    #[test]
    fn prop_checkSudoRedirect7() {
        assert!(!produces(
            check_sudo_redirect("run0"),
            "run0 cmd > /dev/null 2>&1"
        ));
    }

    // checkSudoArgs

    #[test]
    fn prop_checkSudoArgs1() {
        assert!(produces(check_sudo_args("sudo"), "sudo cd /root"));
    }

    #[test]
    fn prop_checkSudoArgs2() {
        assert!(produces(check_sudo_args("run0"), "run0 export x=3"));
    }

    #[test]
    fn prop_checkSudoArgs3() {
        assert!(!produces(
            check_sudo_args("sudo"),
            "sudo ls /usr/local/protected"
        ));
    }

    #[test]
    fn prop_checkSudoArgs4() {
        assert!(!produces(check_sudo_args("doas"), "doas ls && export x=3"));
    }

    #[test]
    fn prop_checkSudoArgs5() {
        assert!(!produces(check_sudo_args("sudo"), "sudo echo ls"));
    }

    #[test]
    fn prop_checkSudoArgs6() {
        assert!(!produces(check_sudo_args("sudo"), "sudo -n -u export ls"));
    }

    #[test]
    fn prop_checkSudoArgs7() {
        assert!(!produces(check_sudo_args("sudo"), "sudo docker export foo"));
    }

    // checkWhileGetoptsCase
}
