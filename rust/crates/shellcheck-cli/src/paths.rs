//! The `System.FilePath.Posix` and `System.Directory` behaviour the driver
//! relies on, on path strings.

use std::path::{Component, Path, PathBuf};

/// `System.FilePath.combine` (`</>`).
pub fn combine(dir: &str, file: &str) -> String {
    if file.starts_with('/') || dir.is_empty() {
        return file.to_string();
    }
    if file.is_empty() {
        return dir.to_string();
    }
    if dir.ends_with('/') {
        format!("{dir}{file}")
    } else {
        format!("{dir}/{file}")
    }
}

/// `dropFileName`: everything up to and including the last separator, or `./`
/// when there is none.
pub fn drop_file_name(path: &str) -> String {
    match path.rfind('/') {
        Some(i) => path[..=i].to_string(),
        None => "./".to_string(),
    }
}

/// `takeFileName`: everything after the last separator.
pub fn take_file_name(path: &str) -> &str {
    path.rsplit('/').next().unwrap_or(path)
}

/// `takeDirectory`: `dropFileName` without its trailing separators, unless
/// they are all there is.
pub fn take_directory(path: &str) -> String {
    let dir = drop_file_name(path);
    let trimmed = dir.trim_end_matches('/');
    if trimmed.is_empty() {
        dir
    } else {
        trimmed.to_string()
    }
}

/// `doesFileExist`: something other than a directory is at `path`.
pub fn does_file_exist(path: &str) -> bool {
    std::fs::metadata(path).is_ok_and(|m| !m.is_dir())
}

/// `getXdgDirectory XdgConfig`: `$XDG_CONFIG_HOME` when it is absolute, else
/// `.config` in the home directory.
pub fn xdg_config_home() -> Option<String> {
    match std::env::var("XDG_CONFIG_HOME") {
        Ok(dir) if dir.starts_with('/') => Some(dir),
        _ => std::env::var("HOME")
            .ok()
            .map(|home| combine(&home, ".config")),
    }
}

/// `normalize`: `canonicalizePath`, falling back to making the path absolute
/// and removing `.` / `..` lexically when it cannot be resolved.
pub fn normalize(path: &str) -> String {
    if let Ok(p) = std::fs::canonicalize(path) {
        return p.to_string_lossy().into_owned();
    }
    let mut out = PathBuf::new();
    let joined = if Path::new(path).is_absolute() {
        PathBuf::from(path)
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(path)
    };
    for c in joined.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out.to_string_lossy().into_owned()
}

/// `show (ex :: IOException)` for what `openBinaryFile` throws, which is the
/// text that reaches the user after "Not following: " and after a failing
/// input's name.
pub fn io_error_message(file: &str, e: &std::io::Error) -> String {
    use std::io::ErrorKind;
    let detail = match e.kind() {
        ErrorKind::NotFound => "does not exist (No such file or directory)".to_string(),
        ErrorKind::PermissionDenied => "permission denied (Permission denied)".to_string(),
        ErrorKind::IsADirectory => "inappropriate type (is a directory)".to_string(),
        // `read_to_string` on a directory reports this on some platforms.
        _ if Path::new(file).is_dir() => "inappropriate type (is a directory)".to_string(),
        ErrorKind::InvalidData => "invalid byte sequence".to_string(),
        _ => e.to_string(),
    };
    format!("{file}: openBinaryFile: {detail}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn combine_follows_haskell() {
        assert_eq!(combine("dir", "file"), "dir/file");
        assert_eq!(combine("dir/", "file"), "dir/file");
        assert_eq!(combine("", "file"), "file");
        assert_eq!(combine("dir", ""), "dir");
        // An absolute second half wins outright.
        assert_eq!(combine("dir", "/file"), "/file");
        assert_eq!(combine("/", "file"), "/file");
    }

    #[test]
    fn drop_file_name_follows_haskell() {
        assert_eq!(drop_file_name("psrc.sh"), "./");
        assert_eq!(drop_file_name("dir/myscript"), "dir/");
        assert_eq!(drop_file_name("/abs/script.sh"), "/abs/");
    }

    #[test]
    fn take_file_name_and_directory_follow_haskell() {
        assert_eq!(take_file_name("dir/foo.sh"), "foo.sh");
        assert_eq!(take_file_name("-"), "-");
        assert_eq!(take_file_name("dir/"), "");
        assert_eq!(take_directory("foo"), ".");
        assert_eq!(take_directory("-"), ".");
        assert_eq!(take_directory("foo/bar/baz"), "foo/bar");
        assert_eq!(take_directory("foo/bar/baz/"), "foo/bar/baz");
        assert_eq!(take_directory("/foo"), "/");
        assert_eq!(take_directory("/"), "/");
        assert_eq!(take_directory("//foo"), "//");
    }

    #[test]
    fn io_error_message_reads_like_the_haskell_exception() {
        let e = std::io::Error::from(std::io::ErrorKind::NotFound);
        assert_eq!(
            io_error_message("./missing.sh", &e),
            "./missing.sh: openBinaryFile: does not exist (No such file or directory)"
        );
        let e = std::io::Error::from(std::io::ErrorKind::PermissionDenied);
        assert_eq!(
            io_error_message("x", &e),
            "x: openBinaryFile: permission denied (Permission denied)"
        );
    }
}
