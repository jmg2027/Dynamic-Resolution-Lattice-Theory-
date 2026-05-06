//! `verify-citations` — sanity-check whitelist.toml against lean/E213/.
//!
//! Phase 0 scope: for each `lean = "X.Y...Z.theorem"` entry,
//!   1. find the deepest path-prefix that resolves to a `.lean` file
//!      under `lean/`.  Reject the trivial `E213.lean` root fallback
//!      (depth ≥ 2 required) so module-level cites can't masquerade
//!      as resolved.
//!   2. confirm the trailing segment (theorem/lemma/def name) appears
//!      as `theorem|lemma|def <name>` in that file.  Best-effort
//!      grep — does NOT replace `lake env lean #print axioms`, but
//!      catches typos and orphaned cites.
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
    let mut weak = 0usize;
    for op in &wl.ops {
        match resolve(&lean_root, &op.lean) {
            Resolution::Missing => {
                eprintln!("UNRESOLVED  rust={}  lean={}", op.rust, op.lean);
                bad += 1;
            }
            Resolution::RootFallback => {
                eprintln!("WEAK (root fallback)  rust={}  lean={}", op.rust, op.lean);
                weak += 1;
            }
            Resolution::FileOnly(p) => {
                eprintln!("WEAK (no theorem id) rust={}  lean={}  file={:?}",
                    op.rust, op.lean, p);
                weak += 1;
            }
            Resolution::Ok => {}
        }
    }

    if bad == 0 && weak == 0 {
        println!("OK: {} citation(s) resolve with theorem id.", wl.ops.len());
        ExitCode::SUCCESS
    } else {
        eprintln!("FAIL: {bad} unresolved, {weak} weak.");
        ExitCode::from(1)
    }
}

enum Resolution { Ok, FileOnly(PathBuf), RootFallback, Missing }

/// `E213.Lib.Physics.AlphaEM137.inv_full_upper` →
///   1. find deepest path prefix matching a `.lean` file (depth ≥ 2)
///   2. require trailing segment to occur as a top-level identifier.
fn resolve(lean_root: &Path, lemma: &str) -> Resolution {
    let parts: Vec<&str> = lemma.split('.').collect();
    for end in (2..=parts.len()).rev() {
        let mut p = lean_root.to_path_buf();
        for seg in &parts[..end] { p.push(seg); }
        p.set_extension("lean");
        if !p.is_file() { continue; }
        let trailing = parts[end..].join(".");
        return if trailing.is_empty() {
            Resolution::FileOnly(p)
        } else if has_theorem(&p, &trailing) {
            Resolution::Ok
        } else {
            Resolution::FileOnly(p)
        };
    }
    if parts.first().map(|s| {
        let mut p = lean_root.to_path_buf();
        p.push(s);
        p.set_extension("lean");
        p.is_file()
    }).unwrap_or(false) { Resolution::RootFallback } else { Resolution::Missing }
}

fn has_theorem(path: &Path, name: &str) -> bool {
    let Ok(text) = std::fs::read_to_string(path) else { return false };
    let kws = ["theorem", "lemma", "def", "abbrev", "instance"];
    let term = |c: char| matches!(c, ' ' | '\t' | '\n' | '{' | '(' | ':' | '[' | '|');
    // 1+2. top-level decl: `<kw> [<dotted>.]<name><term>`
    for line in text.lines() {
        let t = line.trim_start();
        for kw in kws {
            let prefix = format!("{kw} ");
            if !t.starts_with(&prefix) { continue; }
            let rest = &t[prefix.len()..];
            // find first non-identifier char
            let end = rest.find(term).unwrap_or(rest.len());
            let head = &rest[..end];
            if head == name || head.ends_with(&format!(".{name}")) { return true; }
        }
    }
    // 3. inductive constructor: `| <name>` then term char
    let pat3a = format!("| {name} ");
    let pat3b = format!("| {name}\n");
    let pat3c = format!("| {name}:");
    if text.contains(&pat3a) || text.contains(&pat3b) || text.contains(&pat3c) {
        return true;
    }
    // 4. structure field: indented `<name> :` after `where`
    if text.contains("where") {
        for line in text.lines() {
            let t = line.trim_start();
            if t.starts_with(&format!("{name} :")) || t.starts_with(&format!("{name}:")) {
                return true;
            }
        }
    }
    false
}
