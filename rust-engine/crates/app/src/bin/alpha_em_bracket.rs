//! `alpha-em-bracket` — re-execute Lean's `bracket_137_in_at_*_tight`
//! and emit a certificate JSON for Lean ingestion.
//!
//! Default N = 20 (matches Lean's `capstone_n20`).

use drlt_app::alpha_em::{bracket_137_at, bracket_137036_at, bracket_candidate_at};
use drlt_app::alpha_em_with_tail::{
    bracket_137036_with_tail_at, bracket_candidate_with_tail_at,
    inv_lower_with_tail, inv_upper_with_tail,
};
use drlt_app::basel::{s_partial, upper, Q};
use drlt_app::certificate::{Certificate, Cmp, Step};
use num_bigint::BigUint;

fn nat(n: u64) -> BigUint { BigUint::from(n) }

/// Print `q.0 / q.1` as integer.fractional with `scale` decimal digits.
/// ℕ-only — no floats.  Pretty-print only.
fn dec(label: &str, q: &Q, scale: u32) {
    let big = BigUint::from(10u64).pow(scale);
    let scaled = &q.0 * &big / &q.1;
    let int_part = &scaled / &big;
    let frac_part = &scaled % &big;
    println!("  {label} ≈ {int_part}.{:0>w$}", frac_part, w = scale as usize);
}

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(20);
    let result = bracket_137_at(n);
    let cert = build_certificate(n, &result);

    println!("=== α_em bracket re-execution at N = {n} ===");
    dec("S(N)            ", &s_partial(n), 9);
    dec("upper(N)        ", &upper(n),     9);
    dec("inv_lower_tight ", &result.lo,    9);
    dec("inv_full_upper  ", &result.hi,    9);
    let hi_x_lod = &result.hi.0 * &result.lo.1;
    let lo_x_hid = &result.lo.0 * &result.hi.1;
    let width = if hi_x_lod >= lo_x_hid { &hi_x_lod - &lo_x_hid } else { BigUint::from(0u32) };
    let width_den = &result.lo.1 * &result.hi.1;
    dec("bracket width   ", &(width, width_den), 9);
    println!("  -- no-tail bracket --");
    println!("  contains 137:        {}", result.contains_137);
    println!("  contains 137.036:    {}  (observed)",  bracket_137036_at(n));
    println!("  contains 137.0354:   {}  (candidate)", bracket_candidate_at(n));
    println!("  excludes 138:        {}", result.excludes_138);
    if n >= 1 {
        println!("  -- with Dyson tail α_GUT/(NS+1) --");
        dec("inv_lower_with_tail", &inv_lower_with_tail(n), 9);
        dec("inv_upper_with_tail", &inv_upper_with_tail(n), 9);
        println!("  contains 137.036:    {}  (observed)",  bracket_137036_with_tail_at(n));
        println!("  contains 137.0354:   {}  (candidate)", bracket_candidate_with_tail_at(n));
    }

    // Note rotation: differentiate "needs tail" vs "structural gap".
    let no_tail = bracket_137036_at(n);
    let with_tail = n >= 1 && bracket_137036_with_tail_at(n);
    match (no_tail, with_tail) {
        (true,  _)     => {} // baseline ok
        (false, true)  => eprintln!(
            "NOTE: at N={n}, observed needs Dyson tail α_GUT/(NS+1) \
             to lie inside the bracket."),
        (false, false) => eprintln!(
            "NOTE: at N={n}, observed is OUTSIDE even the with-tail \
             bracket — structural gap (~5.4×10⁻⁴) is visible \
             (cf. AlphaEMStructuralGap Open Problem #1b)."),
    }
    println!("\n--- certificate.json ---");
    println!("{}", cert.to_json());
    println!("OK: certificate emitted ({} steps).", cert.steps.len());
}

fn build_certificate(
    n: u64, r: &drlt_app::alpha_em::BracketResult,
) -> Certificate {
    let mut c = Certificate::new();
    let s = s_partial(n);
    let u = upper(n);
    c.push(Step::Cite { lemma: "E213.Lib.Physics.Basel.S".into() });
    c.push(Step::Apply {
        op: "S".into(), args: vec![(nat(n), nat(1))], result: s.clone(),
    });
    c.push(Step::Cite { lemma: "E213.Lib.Physics.Basel.upper".into() });
    c.push(Step::Apply {
        op: "upper".into(), args: vec![(nat(n), nat(1))], result: u.clone(),
    });
    c.push(Step::Cite {
        lemma: "E213.Lib.Physics.AlphaEM137Tight.inv_lower_tight".into() });
    c.push(Step::Apply {
        op: "inv_lower_tight".into(),
        args: vec![(nat(n), nat(1))], result: r.lo.clone(),
    });
    c.push(Step::Cite {
        lemma: "E213.Lib.Physics.AlphaEM137.inv_full_upper".into() });
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
        lemma: format!("E213.Lib.Physics.AlphaEM137Tight.bracket_137_in_at_{n}_tight"),
    });
    c
}
