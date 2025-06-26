use std::{
    io::Write,
    process::{Command, Stdio},
};

use anyhow::bail;

pub fn rustfmt(s: &str) -> String {
    match rustfmt_raw(s) {
        Ok(s) => s,
        Err(_) => s.replace("}", "}\n"),
    }
}
fn rustfmt_raw(s: &str) -> anyhow::Result<String> {
    let child = Command::new("rustfmt")
        .args(["--config", "normalize_doc_attributes=true"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    child.stdin.as_ref().unwrap().write_all(s.as_bytes())?;
    let o = child.wait_with_output()?;
    if o.status.success() {
        Ok(std::str::from_utf8(&o.stdout)?.to_string())
    } else {
        bail!("{}", std::str::from_utf8(&o.stderr)?);
    }
}
