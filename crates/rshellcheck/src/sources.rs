use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::io::Read;
use std::os::unix::fs::FileTypeExt;
use std::path::{Component, Path, PathBuf};

pub struct IoFailure {
    file: String,
    location: &'static str,
    kind: &'static str,
    description: String,
}

impl IoFailure {
    pub fn new(file: &str, location: &'static str, error: &std::io::Error) -> Self {
        let (kind, description) = match error.raw_os_error() {
            Some(errno) => (kind(errno), strerror(errno)),
            None => ("failed", error.to_string()),
        };
        IoFailure {
            file: file.to_string(),
            location,
            kind,
            description,
        }
    }
}

impl fmt::Display for IoFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}: {}", self.file, self.location, self.kind)?;
        if !self.description.is_empty() {
            write!(f, " ({})", self.description)?;
        }
        Ok(())
    }
}

fn strerror(errno: i32) -> String {
    let text = std::io::Error::from_raw_os_error(errno).to_string();
    match text.strip_suffix(&format!(" (os error {errno})")) {
        Some(description) => description.to_string(),
        None => text,
    }
}

// Mirrors the errno table of GHC's Foreign.C.Error.errnoToIOError.
fn kind(errno: i32) -> &'static str {
    match errno {
        libc::E2BIG
        | libc::EAGAIN
        | libc::EMFILE
        | libc::EMLINK
        | libc::EMSGSIZE
        | libc::ENFILE
        | libc::ENOBUFS
        | libc::ENOLCK
        | libc::ENOMEM
        | libc::ENOSPC
        | libc::ENOSR
        | libc::ETOOMANYREFS
        | libc::EUSERS => "resource exhausted",
        libc::EACCES | libc::EDQUOT | libc::EFBIG | libc::EPERM | libc::EROFS => {
            "permission denied"
        }
        libc::EADDRINUSE | libc::EBUSY | libc::EDEADLK | libc::ETXTBSY => "resource busy",
        libc::EADDRNOTAVAIL
        | libc::EAFNOSUPPORT
        | libc::EMULTIHOP
        | libc::ENODEV
        | libc::ENOPROTOOPT
        | libc::ENOSYS
        | libc::EOPNOTSUPP
        | libc::EPFNOSUPPORT
        | libc::ERANGE
        | libc::ESOCKTNOSUPPORT
        | libc::ESPIPE
        | libc::EXDEV => "unsupported operation",
        libc::EALREADY | libc::EEXIST | libc::EINPROGRESS | libc::EISCONN => "already exists",
        libc::EBADF
        | libc::EDESTADDRREQ
        | libc::EDOM
        | libc::EILSEQ
        | libc::EINVAL
        | libc::ELOOP
        | libc::ENAMETOOLONG
        | libc::ENOEXEC
        | libc::ENOSTR
        | libc::ENOTBLK
        | libc::ENOTCONN
        | libc::ENOTSOCK => "invalid argument",
        libc::EBADMSG | libc::EISDIR | libc::ENOTDIR => "inappropriate type",
        libc::ECHILD
        | libc::ECONNREFUSED
        | libc::EHOSTDOWN
        | libc::EHOSTUNREACH
        | libc::ENETUNREACH
        | libc::ENODATA
        | libc::ENOENT
        | libc::ENOMSG
        | libc::ENONET
        | libc::ENXIO
        | libc::ESRCH => "does not exist",
        libc::ECOMM
        | libc::ECONNRESET
        | libc::EIDRM
        | libc::ENETDOWN
        | libc::ENETRESET
        | libc::ENOLINK
        | libc::EPIPE
        | libc::EREMCHG
        | libc::ESTALE => "resource vanished",
        libc::ENOTEMPTY | libc::ESRMNT => "unsatisfied constraints",
        libc::EINTR => "interrupted",
        libc::EIO => "hardware fault",
        libc::ENOTTY | libc::EREMOTE | libc::ESHUTDOWN => "illegal operation",
        libc::EPROTO | libc::EPROTONOSUPPORT | libc::EPROTOTYPE => "protocol error",
        libc::ETIME | libc::ETIMEDOUT => "timeout",
        _ => "failed",
    }
}

pub fn latin1(bytes: &[u8]) -> String {
    bytes.iter().map(|&byte| char::from(byte)).collect()
}

pub fn input_file(file: &str) -> Result<(String, bool), IoFailure> {
    let mut bytes = Vec::new();
    if file == "-" {
        std::io::stdin()
            .lock()
            .read_to_end(&mut bytes)
            .map_err(|error| IoFailure::new("<stdin>", "hGetContents", &error))?;
        return Ok((latin1(&bytes), true));
    }
    let mut handle = std::fs::File::open(file)
        .map_err(|error| IoFailure::new(file, "openBinaryFile", &error))?;
    let kind = handle
        .metadata()
        .map_err(|error| IoFailure::new(file, "openBinaryFile", &error))?
        .file_type();
    if kind.is_dir() {
        return Err(IoFailure {
            file: file.to_string(),
            location: "openBinaryFile",
            kind: "inappropriate type",
            description: "is a directory".into(),
        });
    }
    handle
        .read_to_end(&mut bytes)
        .map_err(|error| IoFailure::new(file, "hGetContents", &error))?;
    Ok((latin1(&bytes), !(kind.is_file() || kind.is_block_device())))
}

pub fn canonical(path: &str) -> PathBuf {
    let Ok(absolute) = std::path::absolute(path) else {
        return PathBuf::from(path);
    };
    let parts: Vec<Component> = absolute.components().collect();
    (1..=parts.len())
        .rev()
        .find_map(|split| {
            let prefix: PathBuf = parts[..split].iter().collect();
            std::fs::canonicalize(prefix).ok().map(|real| {
                parts[split..]
                    .iter()
                    .fold(real, |path, part| path.join(part))
            })
        })
        .unwrap_or(absolute)
}

// Matches filepath's POSIX `combine`.
fn combine(directory: &str, file: &str) -> String {
    if file.starts_with('/') || directory.is_empty() {
        file.to_string()
    } else if file.is_empty() {
        directory.to_string()
    } else if directory.ends_with('/') {
        format!("{directory}{file}")
    } else {
        format!("{directory}/{file}")
    }
}

fn drop_file_name(path: &str) -> String {
    match path.rfind('/') {
        Some(end) => path[..=end].to_string(),
        None => "./".to_string(),
    }
}

fn adjust_path(script_directory: &str, path: &str) -> String {
    let mut parts = path.split('/').filter(|part| !part.is_empty());
    if !path.starts_with('/') && parts.next() == Some("SCRIPTDIR") {
        combine(script_directory, &parts.collect::<Vec<_>>().join("/"))
    } else {
        path.to_string()
    }
}

pub struct Sources {
    external: bool,
    inputs: Vec<PathBuf>,
    paths: Vec<String>,
    cache: RefCell<HashMap<String, String>>,
}

impl Sources {
    pub fn new(external: bool, files: &[String], paths: Vec<String>) -> Self {
        Sources {
            external,
            inputs: files.iter().map(|file| canonical(file)).collect(),
            paths,
            cache: RefCell::default(),
        }
    }

    fn allowable(&self, external: Option<bool>, file: &str) -> bool {
        external.unwrap_or(self.external) || self.inputs.contains(&canonical(file))
    }

    pub fn read(&self, external: Option<bool>, file: &str) -> Result<String, String> {
        if let Some(text) = self.cache.borrow().get(file) {
            return Ok(text.clone());
        }
        if !self.allowable(external, file) {
            return Err(if external == Some(false) {
                format!(
                    "{file} was not specified as input, and external files were disabled via directive."
                )
            } else {
                format!("{file} was not specified as input (see shellcheck -x).")
            });
        }
        let (text, reusable) = input_file(file).map_err(|failure| failure.to_string())?;
        if reusable {
            self.cache
                .borrow_mut()
                .insert(file.to_string(), text.clone());
        }
        Ok(text)
    }

    pub fn find(
        &self,
        current: &str,
        external: Option<bool>,
        annotations: &[String],
        original: &str,
    ) -> String {
        let relative = original.trim_start_matches('/');
        let script_directory = drop_file_name(current);
        let adjust = |path: &str| adjust_path(&script_directory, path);
        std::iter::once(adjust(relative))
            .chain(
                self.paths
                    .iter()
                    .chain(annotations)
                    .map(|directory| combine(&adjust(directory), relative)),
            )
            .find(|candidate| self.allowable(external, candidate) && Path::new(candidate).is_file())
            .unwrap_or_else(|| original.to_string())
    }
}

pub type RcFile = (String, String);

struct Lookup {
    directory: PathBuf,
    found: Option<RcFile>,
}

pub struct Config {
    rcfile: Option<String>,
    cache: RefCell<Option<Lookup>>,
}

impl Config {
    pub fn new(rcfile: Option<String>) -> Self {
        Config {
            rcfile,
            cache: RefCell::default(),
        }
    }

    pub fn lookup(&self, script: &str) -> Option<RcFile> {
        let directory = match &self.rcfile {
            Some(_) => PathBuf::from("/"),
            None => canonical(script)
                .parent()
                .map_or_else(|| PathBuf::from("/"), Path::to_path_buf),
        };
        if let Some(cached) = &*self.cache.borrow()
            && cached.directory == directory
        {
            return cached.found.clone();
        }
        let result = match &self.rcfile {
            Some(file) => {
                let result = read_config(file);
                if result.is_none() {
                    eprintln!("Warning: unable to read --rcfile {file}");
                }
                result
            }
            None => candidates(&directory)
                .into_iter()
                .find_map(|file| read_config(&file)),
        };
        *self.cache.borrow_mut() = Some(Lookup {
            directory,
            found: result.clone(),
        });
        result
    }
}

fn candidates(directory: &Path) -> Vec<String> {
    let home = std::env::home_dir();
    let xdg = std::env::var_os("XDG_CONFIG_HOME")
        .map(PathBuf::from)
        .filter(|path| path.is_absolute())
        .or_else(|| home.as_ref().map(|home| home.join(".config")));
    let defaults = home.map(|home| {
        [
            home.join(".shellcheckrc"),
            xdg.unwrap_or_default().join("shellcheckrc"),
        ]
    });
    directory
        .ancestors()
        .flat_map(|directory| {
            [
                directory.join(".shellcheckrc"),
                directory.join("shellcheckrc"),
            ]
        })
        .chain(defaults.into_iter().flatten())
        .map(|path| path.display().to_string())
        .collect()
}

fn read_config(file: &str) -> Option<RcFile> {
    if !Path::new(file).is_file() {
        return None;
    }
    Some(match input_file(file) {
        Ok((text, _)) => (file.to_string(), text),
        Err(failure) => {
            eprintln!("{file}: {failure}");
            (file.to_string(), String::new())
        }
    })
}

#[cfg(test)]
mod tests {
    use super::{adjust_path, combine, drop_file_name};

    #[test]
    fn combines_like_filepath() {
        assert_eq!(combine("dir", "file"), "dir/file");
        assert_eq!(combine("dir/", "file"), "dir/file");
        assert_eq!(combine("", "file"), "file");
        assert_eq!(combine("dir", ""), "dir");
        assert_eq!(combine("dir", "/abs"), "/abs");
    }

    #[test]
    fn drops_file_names_like_filepath() {
        assert_eq!(drop_file_name("dir/script.sh"), "dir/");
        assert_eq!(drop_file_name("script.sh"), "./");
        assert_eq!(drop_file_name("/script.sh"), "/");
    }

    #[test]
    fn scriptdir_expands_to_the_script_directory() {
        assert_eq!(adjust_path("dir/", "SCRIPTDIR/lib"), "dir/lib");
        assert_eq!(adjust_path("./", "SCRIPTDIR"), "./");
        assert_eq!(adjust_path("dir/", "SCRIPTDIR//a/./b/"), "dir/a/./b");
        assert_eq!(adjust_path("dir/", "lib/SCRIPTDIR"), "lib/SCRIPTDIR");
        assert_eq!(adjust_path("dir/", "/SCRIPTDIR/x"), "/SCRIPTDIR/x");
    }
}
