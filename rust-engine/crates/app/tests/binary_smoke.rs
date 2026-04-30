//! Binary smoke tests — every certified binary in `src/bin/` must
//! exit 0 and produce non-empty stdout.  Catches the most common
//! regression: a shared helper change that crashes one binary while
//! the rest still build.
//!
//! Maps to gaps-and-todos.md §6 ("no per-binary unit tests").  Does
//! *not* assert numeric output (binaries print at different
//! precisions); pair with `binary_snapshots.rs` for fixed-headline
//! assertions on representative cases.

use std::process::Command;

const BINS: &[(&str, &[&str])] = &[
    ("alpha-em-bracket", &["20"]),
    ("alpha-em-decompose", &["20"]),
    ("asymptotic-freedom", &[]),
    ("atomic-correspondences", &[]),
    ("bond-angles", &[]),
    ("cabibbo-angle", &[]),
    ("cf-generator", &[]),
    ("ckm-wolfenstein", &[]),
    ("color-confinement", &[]),
    ("dark-energy", &["100"]),
    ("deuteron-binding", &[]),
    ("drlt-zero-parameters", &[]),
    ("fibonacci-atomic", &[]),
    ("finite-resonance", &[]),
    ("gap-explorer", &["100"]),
    ("generations", &[]),
    ("golden-ratio", &[]),
    ("hierarchy-towers", &[]),
    ("higgs-master", &[]),
    ("higgs-quartic", &[]),
    ("higgs-vacuum", &[]),
    ("hop-hypothesis", &[]),
    ("horizon-info", &[]),
    ("hydrogen-atom", &[]),
    ("ie-capstone", &[]),
    ("impedance-search", &["50"]),
    ("k32-inspect", &[]),
    ("lambda-qcd-search", &[]),
    ("m-proton", &["100"]),
    ("m-tau-mu", &["100"]),
    ("magic-numbers", &[]),
    ("massless-particles", &[]),
    ("master-catalog", &[]),
    ("mu-electron", &["100"]),
    ("muon-lifetime", &[]),
    ("neutrino-mixing", &[]),
    ("neutron-proton", &[]),
    ("nuclear-binding", &[]),
    ("overlap-series", &["20"]),
    ("parity-check", &[]),
    ("propagator-form", &[]),
    ("quark-hierarchy", &["100"]),
    ("series-truncation", &["50"]),
    ("simplex-inventory", &[]),
    ("theta-qcd", &[]),
    ("triple-coupling", &["100"]),
    ("weinberg-angle", &[]),
    ("why-basel", &["20"]),
    ("wz-bosons", &[]),
];

fn bin_path(name: &str) -> String {
    let key = format!("CARGO_BIN_EXE_{name}");
    std::env::var(&key).unwrap_or_else(|_| panic!("env {key} missing"))
}

fn run(name: &str, args: &[&str]) -> Result<(), String> {
    let path = bin_path(name);
    let out = Command::new(&path).args(args).output()
        .map_err(|e| format!("spawn {name}: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "{name} exit {:?}\nstderr: {}",
            out.status.code(), String::from_utf8_lossy(&out.stderr)));
    }
    if out.stdout.is_empty() {
        return Err(format!("{name} produced empty stdout"));
    }
    Ok(())
}

#[test]
fn all_binaries_smoke() {
    let mut failed = Vec::new();
    for (name, args) in BINS {
        if let Err(e) = run(name, args) { failed.push(e); }
    }
    assert!(failed.is_empty(),
        "{} of {} failed:\n{}",
        failed.len(), BINS.len(), failed.join("\n"));
}
