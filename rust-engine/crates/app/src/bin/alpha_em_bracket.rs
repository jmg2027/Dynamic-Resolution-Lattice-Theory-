//! `alpha-em-bracket` — re-execute Lean's `bracket_137_in_at_*_tight`
//! and emit a certificate JSON for Lean ingestion.
//!
//! Default N = 20 (matches Lean's `capstone_n20`).

use drlt_app::alpha_em::bracket_137_at;
use drlt_app::basel::{s_partial, upper};
use drlt_app::certificate::{Certificate, Cmp, Step};
use num_bigint::BigUint;

fn nat(n: u64) -> BigUint { BigUint::from(n) }

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(20);
    let result = bracket_137_at(n);
    let cert = build_certificate(n, &result);

    println!("=== α_em bracket re-execution at N = {n} ===");
    println!("S({n})         = ({}, {})", s_partial(n).0, s_partial(n).1);
    println!("upper({n})     = ({}, {})", upper(n).0, upper(n).1);
    println!("inv_lower_tight = ({}, {})", result.lo.0, result.lo.1);
    println!("inv_full_upper  = ({}, {})", result.hi.0, result.hi.1);
    println!("contains 137: {}   excludes 138: {}",
        result.contains_137, result.excludes_138);

    if !result.contains_137 || !result.excludes_138 {
        eprintln!("FAIL: bracket condition not met at N = {n}");
        std::process::exit(1);
    }
    println!("\n--- certificate.json ---");
    println!("{}", cert.to_json());
    println!("OK: bracket_137_in_at_{n}_tight reproduced ({} steps).",
        cert.steps.len());
}

fn build_certificate(
    n: u64, r: &drlt_app::alpha_em::BracketResult,
) -> Certificate {
    let mut c = Certificate::new();
    let s = s_partial(n);
    let u = upper(n);
    c.push(Step::Cite { lemma: "E213.Physics.Basel.S".into() });
    c.push(Step::Apply {
        op: "S".into(), args: vec![(nat(n), nat(1))], result: s.clone(),
    });
    c.push(Step::Cite { lemma: "E213.Physics.Basel.upper".into() });
    c.push(Step::Apply {
        op: "upper".into(), args: vec![(nat(n), nat(1))], result: u.clone(),
    });
    c.push(Step::Cite {
        lemma: "E213.Physics.AlphaEM137Tight.inv_lower_tight".into() });
    c.push(Step::Apply {
        op: "inv_lower_tight".into(),
        args: vec![(nat(n), nat(1))], result: r.lo.clone(),
    });
    c.push(Step::Cite {
        lemma: "E213.Physics.AlphaEM137.inv_full_upper".into() });
    c.push(Step::Apply {
        op: "inv_full_upper".into(),
        args: vec![(nat(n), nat(1))], result: r.hi.clone(),
    });
    c.push(Step::Bound {
        lhs: r.lo.clone(), cmp: Cmp::Lt,
        rhs: (&nat(137) * &r.lo.1, BigUint::from(1u32)),
    });
    c.push(Step::Bound {
        lhs: (&nat(137) * &r.hi.1, BigUint::from(1u32)),
        cmp: Cmp::Lt, rhs: r.hi.clone(),
    });
    c.push(Step::Cite {
        lemma: format!("E213.Physics.AlphaEM137Tight.bracket_137_in_at_{n}_tight"),
    });
    c
}
