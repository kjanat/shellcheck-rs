use std::fs;
use std::path::Path;

use anyhow::{Result, bail};

use super::{Tools, files_under};

pub fn compare(tools: &Tools, installed: &Path, rebuilt: &Path, declared: &[String]) -> Result<()> {
    let mut same = 0;
    let mut different = 0;
    let mut expected = 0;
    let scratch = rebuilt.join(".interfaces");
    for interface in files_under(installed)? {
        if interface
            .extension()
            .is_none_or(|extension| extension != "hi")
        {
            continue;
        }
        let relative = interface
            .strip_prefix(installed)?
            .to_string_lossy()
            .into_owned();
        if declared.contains(&relative) {
            println!("declared to differ: {relative}");
            expected += 1;
            continue;
        }
        let counterpart = rebuilt.join(&relative);
        if !counterpart.is_file() {
            println!("missing: {relative}");
            different += 1;
            continue;
        }
        let left = normalize(tools, &interface)?;
        let right = normalize(tools, &counterpart)?;
        if left == right {
            same += 1;
            continue;
        }
        different += 1;
        fs::create_dir_all(&scratch)?;
        let (left_file, right_file) = (scratch.join("installed"), scratch.join("rebuilt"));
        fs::write(&left_file, left)?;
        fs::write(&right_file, right)?;
        let status = tools
            .command("diff")
            .arg("-u")
            .arg(format!("--label=installed/{relative}"))
            .arg(format!("--label=rebuilt/{relative}"))
            .arg(&left_file)
            .arg(&right_file)
            .status()?;
        if status.code() != Some(1) {
            bail!("diff of {relative} failed with {status}");
        }
    }
    super::remove_dir(&scratch)?;
    println!("interfaces: {same} identical, {different} different, {expected} declared to differ");
    if different != 0 {
        bail!("{different} rebuilt interfaces differ from the installed ones");
    }
    Ok(())
}

fn normalize(tools: &Tools, interface: &Path) -> Result<String> {
    let shown = tools.output(tools.command("ghc").arg("--show-iface").arg(interface))?;
    let mut skip = false;
    let mut normalized = String::with_capacity(shown.len());
    for line in shown.lines() {
        if line == "docs:" {
            skip = true;
        }
        if line == "extensible fields:" {
            skip = false;
        }
        if skip
            || line.starts_with("addDependentFile ")
            || line.starts_with("plugin package dependencies:")
        {
            continue;
        }
        normalized.push_str(&without_hashes(line));
        normalized.push('\n');
    }
    Ok(normalized)
}

fn without_hashes(line: &str) -> String {
    let bytes = line.as_bytes();
    let mut kept = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        let run = bytes[index..]
            .iter()
            .take_while(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
            .count();
        if run == 0 {
            kept.push(bytes[index]);
            index += 1;
            continue;
        }
        let removed = run - run % 32;
        kept.extend_from_slice(&bytes[index + removed..index + run]);
        index += run;
    }
    String::from_utf8(kept).expect("only ASCII hex digits were removed")
}

#[cfg(test)]
mod tests {
    use super::without_hashes;

    #[test]
    fn hashes_are_removed_in_whole_thirty_two_digit_runs() {
        let hash = "0123456789abcdef0123456789abcdef";
        assert_eq!(without_hashes(&format!("x {hash} y")), "x  y");
        assert_eq!(without_hashes(&format!("{hash}{hash}ab")), "ab");
        assert_eq!(without_hashes("deadbeef"), "deadbeef");
        assert_eq!(without_hashes(&format!("{hash}G")), "G");
    }
}
