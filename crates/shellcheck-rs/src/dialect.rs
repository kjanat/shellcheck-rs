//! The shells a script is checked as: upstream's five and the ones the
//! validity matrix runs, each checked with the rules of its upstream floor.

use crate::interface::Shell;

/// A shell the port can check a script as.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dialect {
    /// `sh`.
    Sh,
    /// `bash`.
    Bash,
    /// `dash`.
    Dash,
    /// `ksh`.
    Ksh,
    /// `busybox sh`.
    BusyboxSh,
    /// `zsh`, checked as bash.
    Zsh,
    /// `mksh`, checked as ksh.
    Mksh,
    /// `oksh`, checked as ksh.
    Oksh,
    /// `loksh`, checked as ksh.
    Loksh,
    /// `yash`, checked as sh.
    Yash,
    /// `posh`, checked as sh.
    Posh,
    /// `bosh`, checked as sh.
    Bosh,
    /// `osh`, checked as bash.
    Osh,
    /// `brush`, checked as bash.
    Brush,
    /// FreeBSD `sh`, checked as sh.
    FreebsdSh,
    /// NetBSD `sh`, checked as sh.
    NetbsdSh,
}

impl Dialect {
    /// Every dialect, in declaration order.
    pub const ALL: [Self; 16] = [
        Self::Sh,
        Self::Bash,
        Self::Dash,
        Self::Ksh,
        Self::BusyboxSh,
        Self::Zsh,
        Self::Mksh,
        Self::Oksh,
        Self::Loksh,
        Self::Yash,
        Self::Posh,
        Self::Bosh,
        Self::Osh,
        Self::Brush,
        Self::FreebsdSh,
        Self::NetbsdSh,
    ];

    /// Every name [`Dialect::from_name`] accepts: each [`Dialect::name`], then
    /// upstream's aliases.
    pub const NAMES: [&'static str; 22] = [
        "sh",
        "bash",
        "dash",
        "ksh",
        "busybox",
        "zsh",
        "mksh",
        "oksh",
        "loksh",
        "yash",
        "posh",
        "bosh",
        "osh",
        "brush",
        "freebsd-sh",
        "netbsd-sh",
        "bats",
        "ash",
        "ksh88",
        "ksh93",
        "busybox sh",
        "busybox ash",
    ];

    /// The upstream shell whose checks run for this dialect.
    #[must_use]
    pub const fn floor(self) -> Shell {
        match self {
            Self::Sh | Self::Yash | Self::Posh | Self::Bosh | Self::FreebsdSh | Self::NetbsdSh => {
                Shell::Sh
            }
            Self::Bash | Self::Zsh | Self::Osh | Self::Brush => Shell::Bash,
            Self::Dash => Shell::Dash,
            Self::Ksh | Self::Mksh | Self::Oksh | Self::Loksh => Shell::Ksh,
            Self::BusyboxSh => Shell::BusyboxSh,
        }
    }

    /// The key naming this dialect in `validity/sources.toml`, `--shell` and
    /// `shell=`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Sh => "sh",
            Self::Bash => "bash",
            Self::Dash => "dash",
            Self::Ksh => "ksh",
            Self::BusyboxSh => "busybox",
            Self::Zsh => "zsh",
            Self::Mksh => "mksh",
            Self::Oksh => "oksh",
            Self::Loksh => "loksh",
            Self::Yash => "yash",
            Self::Posh => "posh",
            Self::Bosh => "bosh",
            Self::Osh => "osh",
            Self::Brush => "brush",
            Self::FreebsdSh => "freebsd-sh",
            Self::NetbsdSh => "netbsd-sh",
        }
    }

    /// Whether the port adds this dialect to upstream's five shells.
    #[must_use]
    pub const fn is_added(self) -> bool {
        !matches!(
            self,
            Self::Sh | Self::Bash | Self::Dash | Self::Ksh | Self::BusyboxSh
        )
    }

    /// The dialect a `--shell` value, a `shell=` directive or a shebang names:
    /// every [`Dialect::name`], then upstream's `shellForExecutable` aliases.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "zsh" => Self::Zsh,
            "mksh" => Self::Mksh,
            "oksh" => Self::Oksh,
            "loksh" => Self::Loksh,
            "yash" => Self::Yash,
            "posh" => Self::Posh,
            "bosh" => Self::Bosh,
            "osh" => Self::Osh,
            "brush" => Self::Brush,
            "freebsd-sh" => Self::FreebsdSh,
            "netbsd-sh" => Self::NetbsdSh,
            _ => return crate::data::shell_for_executable(name).map(Self::from),
        })
    }
}

impl From<Shell> for Dialect {
    fn from(shell: Shell) -> Self {
        match shell {
            Shell::Sh => Self::Sh,
            Shell::Bash => Self::Bash,
            Shell::Dash => Self::Dash,
            Shell::Ksh => Self::Ksh,
            Shell::BusyboxSh => Self::BusyboxSh,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_name_round_trips_every_name() {
        for dialect in Dialect::ALL {
            assert_eq!(Dialect::from_name(dialect.name()), Some(dialect));
        }
    }

    #[test]
    fn each_added_dialect_floors_to_its_upstream_shell() {
        for (dialect, floor) in [
            (Dialect::Zsh, Shell::Bash),
            (Dialect::Osh, Shell::Bash),
            (Dialect::Brush, Shell::Bash),
            (Dialect::Mksh, Shell::Ksh),
            (Dialect::Oksh, Shell::Ksh),
            (Dialect::Loksh, Shell::Ksh),
            (Dialect::Yash, Shell::Sh),
            (Dialect::Posh, Shell::Sh),
            (Dialect::Bosh, Shell::Sh),
            (Dialect::FreebsdSh, Shell::Sh),
            (Dialect::NetbsdSh, Shell::Sh),
        ] {
            assert_eq!(dialect.floor(), floor, "{}", dialect.name());
            assert!(dialect.is_added(), "{}", dialect.name());
        }
    }

    #[test]
    fn upstream_dialects_floor_to_themselves() {
        for shell in [
            Shell::Sh,
            Shell::Bash,
            Shell::Dash,
            Shell::Ksh,
            Shell::BusyboxSh,
        ] {
            let dialect = Dialect::from(shell);
            assert_eq!(dialect.floor(), shell);
            assert!(!dialect.is_added());
        }
    }

    #[test]
    fn is_added_means_the_floor_names_another_dialect() {
        for dialect in Dialect::ALL {
            assert_eq!(
                dialect.is_added(),
                Dialect::from(dialect.floor()) != dialect
            );
        }
    }

    #[test]
    fn upstream_aliases_agree_with_shell_for_executable() {
        for alias in [
            "sh",
            "bash",
            "bats",
            "dash",
            "ash",
            "ksh",
            "ksh88",
            "ksh93",
            "busybox",
            "busybox sh",
            "busybox ash",
        ] {
            assert_eq!(
                Dialect::from_name(alias).map(Dialect::floor),
                crate::data::shell_for_executable(alias),
                "{alias}"
            );
        }
        assert_eq!(Dialect::from_name("oksh"), Some(Dialect::Oksh));
        assert_eq!(
            crate::data::shell_for_executable("oksh"),
            Some(Dialect::Oksh.floor())
        );
    }

    #[test]
    fn names_lists_every_accepted_name() {
        for name in Dialect::NAMES {
            assert!(Dialect::from_name(name).is_some(), "{name}");
        }
        for dialect in Dialect::ALL {
            assert!(
                Dialect::NAMES.contains(&dialect.name()),
                "{}",
                dialect.name()
            );
        }
        for name in ["bats", "ash", "ksh88", "ksh93", "busybox sh", "busybox ash"] {
            assert!(crate::data::shell_for_executable(name).is_some(), "{name}");
        }
    }

    #[test]
    fn tcsh_and_unknown_names_are_rejected() {
        for name in ["tcsh", "csh", "fish", "zsh5", "", "Bash"] {
            assert_eq!(Dialect::from_name(name), None, "{name}");
        }
    }
}
