//! `atomic-hunter` — automated search for atomic identities in
//! dimensionless physics ratios.
//!
//! Strategy: take a target ratio R (rational input).  Search the
//! space of candidate forms
//!
//!   integer · π^a · ζ(2)^b · (1 + α_GUT·k)?
//!
//! over small integers and atomic combinations of (NS, NT, d, c).
//! Report top-N best matches sorted by |R − candidate| / R.
//!
//! Uses 213-internal brackets (Leibniz π via wallis, Basel ζ(2)
//! via s_partial).  Outputs in ppm.
//!
//! Curated targets list at the end of main(): runs hunter on each
//! and prints best atomic candidate.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};
use drlt_app::wallis::pi_bracket;
use num_bigint::BigUint;

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }

/// Atomic integer candidates (NS=3, NT=2, d=5, c=2 derivatives).
fn atomic_ints() -> Vec<(&'static str, u64)> {
    vec![
        ("1",      1),  ("NT",      2),  ("NS",       3),  ("NT²",      4),
        ("d",      5),  ("NS·NT",   6),  ("NS²−1",    8),  ("NS²",      9),
        ("NT·d",  10),  ("c·NS·NT",12),  ("F_7",     13),  ("NS·d",    15),
        ("NT^d",  32),  ("d²",     25),  ("d²−1",    24),  ("d+1",      6),
        ("NS²·d", 45),  ("E·d=60", 60),  ("(NS²−1)·(d²−1)=192", 192),
        ("NS·NT·d²=150", 150), ("d·NT^d=160", 160),
    ]
}

/// (label, π exponent, ζ(2) exponent) — small fractional powers.
fn transcendental_combos() -> Vec<(&'static str, u32, u32)> {
    vec![
        ("",          0, 0), ("·ζ(2)",     0, 1), ("·ζ(2)²",   0, 2),
        ("·π",        1, 0), ("·π·ζ(2)",   1, 1), ("·π²",      2, 0),
        ("·π³",       3, 0), ("·π·ζ(2)²",  1, 2), ("·π²·ζ(2)", 2, 1),
        ("·π⁴",       4, 0), ("·π⁵",       5, 0), ("·π·ζ(2)³", 1, 3),
    ]
}

/// q_pow(q, n): q^n via repeated multiplication.
fn q_pow(q: &Q, n: u32) -> Q {
    if n == 0 { return (nat(1), nat(1)); }
    let mut acc = q.clone();
    for _ in 1..n { acc = mul_q(&acc, q); }
    acc
}

/// Compute candidate value as Q, given (k, π^a, ζ(2)^b).
fn candidate(k: u64, pi_pow: u32, zeta_pow: u32, pi: &Q, zeta: &Q) -> Q {
    let base: Q = (nat(k), nat(1));
    let p = q_pow(pi, pi_pow);
    let z = q_pow(zeta, zeta_pow);
    mul_q(&mul_q(&base, &p), &z)
}

/// |target − candidate| / target, returned as ppm-scaled Nat.
fn ppm_diff(target: &Q, cand: &Q) -> u64 {
    let l = &target.0 * &cand.1; let r = &cand.0 * &target.1;
    let dn: BigUint = if l > r { &l - &r } else { &r - &l };
    // ppm = 10^6 · |Δ| / target = 10^6 · dn · target.1 / (target.0 · cand.1·target.1)
    // Simplify: ppm ≈ (dn * 10^6 / (target.0 * cand.1)) — use u128 to avoid overflow
    let scaled = dn * BigUint::from(1_000_000u64);
    let den = &target.0 * &cand.1;
    if den == BigUint::from(0u32) { return u64::MAX; }
    let q = scaled / den;
    q.to_u64_digits().first().copied().unwrap_or(0).min(u64::MAX)
}

fn hunt(label: &str, target: &Q, pi: &Q, zeta: &Q) {
    let mut best: Vec<(u64, String, Q)> = Vec::new();
    for (k_lab, k) in atomic_ints() {
        for (t_lab, pi_p, ze_p) in transcendental_combos() {
            let cand = candidate(k, pi_p, ze_p, pi, zeta);
            let ppm = ppm_diff(target, &cand);
            best.push((ppm, format!("{k_lab}{t_lab}"), cand));
        }
    }
    best.sort_by_key(|(p, _, _)| *p);
    println!("--- {label} ---");
    println!("  target = {}", decimal(target, 9));
    for (ppm, lab, val) in best.iter().take(3) {
        println!("  {:<24} = {} ({} ppm)",
            lab, decimal(val, 9), ppm);
    }
    println!();
}

fn main() {
    let n_pi: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(2000);
    let n_z:  u64 = std::env::args().nth(2)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);

    // π midpoint from Leibniz bracket
    let (pi_lo, pi_hi) = pi_bracket(n_pi);
    let pi: Q = ((&pi_lo.0 * &pi_hi.1 + &pi_hi.0 * &pi_lo.1),
                  nat(2) * &pi_lo.1 * &pi_hi.1);

    // ζ(2) midpoint from Basel partial + 1/(N+1)
    let s = s_partial(n_z);
    let np1 = nat(n_z + 1);
    let zeta: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);

    println!("=== atomic-hunter — auto search for atomic identities ===\n");
    println!("brackets: π midpoint (Leibniz N={n_pi}), ζ(2) tight (Basel N={n_z})\n");

    // Target list: dimensionless physics ratios with CODATA values.
    // m_p/m_e = 1836.15267343 (CODATA 2022)
    let mp_me: Q = (nat(183615267343u64), nat(100_000_000));
    hunt("m_p/m_e", &mp_me, &pi, &zeta);

    // m_n/m_p = 1.001378
    let mn_mp: Q = (nat(1001378u64), nat(1_000_000));
    hunt("m_n/m_p", &mn_mp, &pi, &zeta);

    // proton g-factor g_p = 5.5856946893
    let g_p: Q = (nat(55856946893u64), nat(10_000_000_000u64));
    hunt("g_p (proton)", &g_p, &pi, &zeta);

    // r_p · m_p / (ℏc) = 4.0008 (already discovered: NT² = 4)
    let r_p_ratio: Q = (nat(40008), nat(10_000));
    hunt("r_p·m_p/(ℏc)", &r_p_ratio, &pi, &zeta);

    // m_τ / m_e = 1777/0.5110 ≈ 3477.6 ; or m_τ/m_e_actual = 3477.15
    let mt_me: Q = (nat(347715), nat(100));
    hunt("m_τ/m_e", &mt_me, &pi, &zeta);
}


