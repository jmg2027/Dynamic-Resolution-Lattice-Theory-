//! `verify-citations` — sanity-check whitelist.toml against lean/E213/.
//!
//! Phase 0 scope: confirm each `lean = "..."` entry's *namespace path*
//! resolves to a file under `lean/E213/`.  Stops short of `#print
//! axioms` invocation (Phase 4+ adds `lake env lean` integration).
//!
//! Exit 0 = clean; non-zero = at least one citation unresolved.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

#[derive(serde::Deserialize)]
struct Whitelist { #[serde(rename = "op")] ops: Vec<Op> }

#[derive(serde::Deserialize)]
struct Op { rust: String, lean: String }

fn main() -> ExitCode {
    let repo = std::env::var("DRLT_REPO_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(".."));
    let wl_path = repo.join("rust-engine/whitelist.toml");
    let lean_root = repo.join("lean");

    let text = match std::fs::read_to_string(&wl_path) {
        Ok(t)  => t,
        Err(e) => { eprintln!("read {:?}: {e}", wl_path); return ExitCode::from(2); }
    };
    let wl: Whitelist = match toml::from_str(&text) {
        Ok(w)  => w,
        Err(e) => { eprintln!("parse whitelist.toml: {e}"); return ExitCode::from(2); }
    };

    let mut bad = 0usize;
    for op in &wl.ops {
        if !lemma_file_exists(&lean_root, &op.lean) {
            eprintln!("UNRESOLVED  rust={}  lean={}", op.rust, op.lean);
            bad += 1;
        }
    }

    if bad == 0 {
        println!("OK: {} citation(s) resolve to a Lean file.", wl.ops.len());
        ExitCode::SUCCESS
    } else {
        eprintln!("FAIL: {bad} unresolved.");
        ExitCode::from(1)
    }
}

/// `E213.Kernel.Term.eval` ⇒ check `lean/E213/Kernel/Term.lean`
/// exists.  We accept any prefix match: namespace path's leading
/// segments must form a real `.lean` file path.
fn lemma_file_exists(lean_root: &Path, lemma: &str) -> bool {
    let parts: Vec<&str> = lemma.split('.').collect();
    // Try progressively shorter prefixes as file paths.
    for end in (1..=parts.len()).rev() {
        let mut p = lean_root.to_path_buf();
        for seg in &parts[..end] { p.push(seg); }
        p.set_extension("lean");
        if p.is_file() { return true; }
    }
    false
}
