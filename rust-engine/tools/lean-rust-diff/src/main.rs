//! lean-rust-diff — Lean ↔ Rust differential equivalence harness.
//!
//! For each registered (Lean expression, Rust function, N values),
//! invoke `lake env lean` with a generated `#eval` and compare the
//! BigUint output against the Rust result for EXACT equality.
//!
//! On every push: re-runs all cases.  Drift between the two
//! implementations becomes a CI failure, not silent.
//!
//! Usage:
//!   cargo run --release --manifest-path tools/lean-rust-diff/Cargo.toml
//!
//! Adding a new case: append to `cases()` below.  The set grows
//! monotonically — sample-coverage extends per push.

use num_bigint::BigUint;
use std::process::{Command, ExitCode};
use std::str::FromStr;

type Q = (BigUint, BigUint);

struct DiffCase {
    name: &'static str,
    lean_module: &'static str,
    lean_expr: &'static str,
    rust_call: fn(u64) -> Q,
    n_values: &'static [u64],
}

/// Parse "(num, den)" Lean tuple output into Q.
fn parse_q(s: &str) -> Option<Q> {
    let s = s.trim();
    let inside = s.strip_prefix('(')?.strip_suffix(')')?;
    let mut parts = inside.split(',');
    let n = parts.next()?.trim();
    let d = parts.next()?.trim();
    Some((BigUint::from_str(n).ok()?, BigUint::from_str(d).ok()?))
}

/// Run `lake env lean` with #eval'ing case.lean_expr at N.
/// Returns parsed (num, den).
fn lean_eval(case: &DiffCase, n: u64) -> Result<Q, String> {
    let lean_src = format!(
        "import {}\n#eval ({} {})\n",
        case.lean_module, case.lean_expr, n
    );
    let tmp = std::env::temp_dir().join(format!(
        "diff_{}_{}.lean", case.name, n));
    std::fs::write(&tmp, lean_src).map_err(|e| e.to_string())?;
    let out = Command::new("lake")
        .args(["env", "lean", tmp.to_str().unwrap()])
        .current_dir("../../../lean")
        .output()
        .map_err(|e| format!("lake spawn failed: {e}"))?;
    if !out.status.success() {
        return Err(format!("lean exit {:?}\n{}",
            out.status.code(), String::from_utf8_lossy(&out.stderr)));
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    parse_q(stdout.trim()).ok_or_else(||
        format!("parse failed: {stdout:?}"))
}

/// Compare two Q via cross-mult exact equality.
fn q_eq(a: &Q, b: &Q) -> bool { &a.0 * &b.1 == &b.0 * &a.1 }

fn cases() -> Vec<DiffCase> {
    vec![
        DiffCase {
            name: "basel_S",
            lean_module: "E213.Physics.BaselBound",
            lean_expr: "E213.Physics.Basel.S",
            rust_call: drlt_app::basel::s_partial,
            n_values: &[0, 1, 2, 3, 5, 10, 20],
        },
        DiffCase {
            name: "basel_upper",
            lean_module: "E213.Physics.BaselBound",
            lean_expr: "E213.Physics.Basel.upper",
            rust_call: drlt_app::basel::upper,
            n_values: &[1, 2, 3, 5, 10, 20],
        },
    ]
}

fn main() -> ExitCode {
    let cases = cases();
    let mut total = 0usize;
    let mut failed: Vec<String> = Vec::new();
    println!("=== Lean ↔ Rust differential equivalence ===\n");
    for case in &cases {
        for &n in case.n_values {
            total += 1;
            let rust_v = (case.rust_call)(n);
            match lean_eval(case, n) {
                Ok(lean_v) => {
                    if q_eq(&lean_v, &rust_v) {
                        println!("✓ {} N={} both = ({}, {})",
                            case.name, n, lean_v.0, lean_v.1);
                    } else {
                        let msg = format!("✗ {} N={}: Lean ({}, {}) vs Rust ({}, {})",
                            case.name, n,
                            lean_v.0, lean_v.1, rust_v.0, rust_v.1);
                        println!("{msg}");
                        failed.push(msg);
                    }
                }
                Err(e) => {
                    let msg = format!("✗ {} N={}: lean_eval error: {e}",
                        case.name, n);
                    println!("{msg}");
                    failed.push(msg);
                }
            }
        }
    }
    println!();
    println!("Total: {total} cases.  Failed: {}", failed.len());
    if failed.is_empty() {
        println!("OK — Lean ↔ Rust exact equality across all N.");
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
