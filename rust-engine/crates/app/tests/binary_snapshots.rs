//! Headline-snapshot tests for representative certified binaries.
//!
//! Asserts that key numeric substrings remain stable across changes
//! to shared helpers (basel::s_partial, gap_explorer::decimal, ℕ-pair
//! arithmetic).  Numeric prefixes are chosen wide enough to remain
//! valid as N is increased (precision can only improve).
//!
//! Maps to gaps-and-todos.md §6.  Companion to `binary_smoke.rs`.

use std::process::Command;

fn bin(name: &str) -> String {
    let key = format!("CARGO_BIN_EXE_{name}");
    std::env::var(&key).unwrap_or_else(|_| panic!("env {key} missing"))
}

fn run(name: &str, args: &[&str]) -> String {
    let out = Command::new(bin(name)).args(args).output()
        .unwrap_or_else(|e| panic!("spawn {name}: {e}"));
    assert!(out.status.success(), "{name} failed");
    String::from_utf8(out.stdout).expect("utf8")
}

fn assert_contains(stdout: &str, needle: &str, label: &str) {
    assert!(stdout.contains(needle),
        "{label}: missing substring `{needle}`\n--- stdout ---\n{stdout}");
}

/// `simplex-inventory` — exact atomic counts on K_{3,2}^{(2)}.
/// Lean: SubSimplexInventory.total_non_empty.  Counts are EXACT
/// integers; any drift = real bug.
#[test]
fn simplex_inventory_atomic_counts() {
    let out = run("simplex-inventory", &[]);
    // 31 = 2^d - 1 total non-empty sub-simplices.
    assert_contains(&out, "31", "total count");
    // (1,1) A-B edges = 6 = NS·NT.
    assert_contains(&out, "(1,1) |     6", "AB edges");
    // (3,0) AAA triangle = 1 = C(NS, NS).
    assert_contains(&out, "(3,0) |     1", "AAA triangle");
}

/// `triple-coupling` — atomic integer coefficients of 1/α_em.
/// Lean: TripleCoupling.triple_skeleton_bundle.  Integer parts
/// (60, 30, 8 from 25/3) are EXACT; ζ(2) precision varies with N.
#[test]
fn triple_coupling_atomic_integers() {
    let out = run("triple-coupling", &["100"]);
    assert_contains(&out, "60·ζ(2)", "60·ζ(2) edge term");
    assert_contains(&out, "30", "chiral split disc");
    assert_contains(&out, "25/3", "d²/NS projection");
    assert_contains(&out, "α_GUT/4", "Dyson tail");
    assert_contains(&out, "α_GUT/45", "cross 10C2");
}

/// `mu-electron` — m_μ/m_e at N=100 must already match CODATA's
/// "206.7683..." prefix (precision improves with N).
#[test]
fn mu_electron_206_7683_prefix() {
    let out = run("mu-electron", &["100"]);
    assert_contains(&out, "206.7683", "m_μ/m_e headline");
    assert_contains(&out, "ppb", "precision report unit");
}
