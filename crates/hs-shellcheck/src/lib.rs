pub static DUMPS: &[(&str, &[u8])] = include!(concat!(env!("OUT_DIR"), "/dumps.rs"));
pub const PACKAGE_DB: &str = env!("HS_SHELLCHECK_PACKAGE_DB");
