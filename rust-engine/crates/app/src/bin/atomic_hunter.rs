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
        ("1",          1), ("NT",         2), ("NS",         3), ("NT²",        4),
        ("d",          5), ("NS·NT",      6), ("d+NT=7",     7), ("NS²−1",      8),
        ("NS²",        9), ("NT·d",      10), ("d²+NS²−d=11",11), ("c·NS·NT",  12),
        ("F_7",       13), ("NS²+d=14",  14), ("NS·d",      15), ("(NS²+1)·NT−2", 18),
        ("NS²·c+2",   20), ("NS²+NS·NT", 15), ("d²−NT=23",  23), ("d²−1",      24),
        ("d²",        25), ("d²+NT−1=26",26), ("NS²+NS·d−1=23", 23),
        ("NS·NT·d−1=29", 29), ("NS·NT·d=30", 30), ("NT^d",      32),
        ("d²+d²−d²+15=40", 40), ("NS²·d", 45), ("d²+24=49", 49),
        ("d²·NT=50",  50), ("E·d=60",    60), ("NS·d²=75",  75),
        ("d²·c·NT=100", 100), ("NS²+d^NT−4=30", 30), ("NS·d²·c=150", 150),
        ("d·NT^d=160", 160), ("(NS²−1)·(d²−1)=192", 192), ("NT^d·NT²=128", 128),
        // FSM-period primes (per 2026-04-30 user analysis, composite hadrons)
        ("2^4+1=17",        17), ("2^4+NS=19",        19),
        ("d²+NT²=29",       29), ("2^d−1=31",         31),
        ("F_9=37",          37), ("d²+NT^d−16=41",    41),
        ("NS²·NT^d−2·d²=43",43), ("d·d²−NT²=47",      47),
        ("NT^d+NT^d−1=63",  63),
        // 3-quark Borromean: prime × atomic for composite period
        ("17·NT=34",  34), ("19·NT=38",  38), ("31·NT=62",  62),
        ("17·NS=51",  51), ("19·NS=57",  57), ("31·NS=93",  93),
        ("17·d=85",   85), ("19·d=95",   95),
    ]
}

/// Atomic fractional candidates p/q for atomic p, q.
/// Captures sub-simplex weight ratios that may appear in
/// composite hadronic / nuclear observables.
fn atomic_fractions() -> Vec<(&'static str, u64, u64)> {
    vec![
        ("NT/NS",      2, 3),  ("NS/NT",      3, 2),  ("NT/d",      2, 5),
        ("NS/d",       3, 5),  ("NT²/NS",     4, 3),  ("NS²/NT",    9, 2),
        ("NS²/d",      9, 5),  ("d/NS",       5, 3),  ("d/NT",      5, 2),
        ("(NS²−1)/d",  8, 5),  ("(NS²−1)/NT²",8, 4),  ("(d²−1)/d",  24, 5),
        ("(d²−1)/NS·NT",24,6), ("d²/(NS·NT)",25, 6),  ("(NT^d)/(NS·d²)",32,75),
        ("(d²−1)/(NS²−1)",24,8), ("NS²/(d²−1)", 9, 24), ("NT²/(d²−1)",4,24),
        ("(NS²+1)/d",  10, 5), ("(d+1)/NT",   6, 2),  ("(NS+NT+1)/d²", 6, 25),
        ("NS/(d²−1)",  3, 24), ("NT/(d²−1)",  2, 24), ("NS·NT/(d²−1)",6,24),
    ]
}

/// α_GUT correction coefficients: candidate · (1 + α_GUT·k).
/// k = 0 means no correction.
fn alpha_corrections() -> Vec<(&'static str, i32)> {
    vec![
        ("",            0),  ("·(1+α)",      1),  ("·(1+NTα)",    2),
        ("·(1+NSα)",    3),  ("·(1+NT²α)",   4),  ("·(1+dα)",     5),
        ("·(1+NS·NTα)", 6),  ("·(1+NS²α)",   9),  ("·(1−α)",     -1),
        ("·(1−NTα)",   -2),  ("·(1−NSα)",   -3),  ("·(1−NT²α)",  -4),
        ("·(1−dα)",    -5),  ("·(1−d²α)",  -25),
    ]
}

/// (label, π exponent, ζ(2) exponent) — small fractional powers.
fn transcendental_combos() -> Vec<(&'static str, u32, u32)> {
    vec![
        ("",          0, 0), ("·ζ(2)",     0, 1), ("·ζ(2)²",   0, 2),
        ("·π",        1, 0), ("·π·ζ(2)",   1, 1), ("·π²",      2, 0),
        ("·π³",       3, 0), ("·π·ζ(2)²",  1, 2), ("·π²·ζ(2)", 2, 1),
        ("·π⁴",       4, 0), ("·π⁵",       5, 0), ("·π·ζ(2)³", 1, 3),
        ("·ζ(2)³",    0, 3), ("·π⁶",       6, 0), ("·π²·ζ(2)²", 2, 2),
        ("·π³·ζ(2)",  3, 1), ("·π⁷",       7, 0), ("·π³·ζ(2)²", 3, 2),
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

/// Apply α_GUT linear correction: q · (1 + α·k/d²·ζ).
/// Computed as q + q·k·α_GUT.  α_GUT = 1/(d²·ζ(2)) so
/// α_GUT_num/den = (zeta.1) / (25·zeta.0).  Sign tracked: k can be ±.
fn apply_alpha(q: &Q, k: i32, zeta: &Q) -> Q {
    if k == 0 { return q.clone(); }
    // q·k·α_GUT = q · k / (25·ζ(2)) = (q.0·|k|·zeta.1) / (q.1·25·zeta.0)
    let ak = k.unsigned_abs() as u64;
    let corr_num = &q.0 * nat(ak) * &zeta.1;
    let corr_den = &q.1 * nat(25) * &zeta.0;
    if k > 0 {
        // q·(1+α·k) = q + q·α·k
        let n = &q.0 * &corr_den + &q.1 * &corr_num;
        let d = &q.1 * &corr_den;
        (n, d)
    } else {
        // q·(1−α·|k|) = q − q·α·|k|.  Assume positive (no underflow checks).
        let lhs = &q.0 * &corr_den;
        let rhs = &q.1 * &corr_num;
        let n = if lhs > rhs { lhs - rhs } else { rhs - lhs };
        (n, &q.1 * &corr_den)
    }
}

/// α² correction set for composite multi-step boundary leakage
/// (2026-04-30 user thesis: Massey product traces of multi-α leak).
fn alpha_sq_corrections() -> Vec<(&'static str, i32)> {
    vec![
        ("·(1+α²)",     1), ("·(1+NTα²)",   2), ("·(1+NSα²)",   3),
        ("·(1+NT²α²)",  4), ("·(1+dα²)",    5), ("·(1+NS·NTα²)",6),
        ("·(1+NS²α²)",  9), ("·(1+d²α²)",  25),
        ("·(1−α²)",    -1), ("·(1−NTα²)",  -2), ("·(1−dα²)",   -5),
        ("·(1−d²α²)", -25),
    ]
}

/// Apply q · (1 + α²·k) correction.  α² = 1/(d²·ζ(2))² so
/// q·k·α² = q·k / (625·ζ(2)²).
fn apply_alpha_sq(q: &Q, k: i32, zeta: &Q) -> Q {
    if k == 0 { return q.clone(); }
    let ak = k.unsigned_abs() as u64;
    let zeta_sq_num = &zeta.1 * &zeta.1;
    let zeta_sq_den = &zeta.0 * &zeta.0;
    let corr_num = &q.0 * nat(ak) * &zeta_sq_num;
    let corr_den = &q.1 * nat(625) * &zeta_sq_den;
    if k > 0 {
        let n = &q.0 * &corr_den + &q.1 * &corr_num;
        let d = &q.1 * &corr_den;
        (n, d)
    } else {
        let lhs = &q.0 * &corr_den;
        let rhs = &q.1 * &corr_num;
        let n = if lhs > rhs { lhs - rhs } else { rhs - lhs };
        (n, &q.1 * &corr_den)
    }
}

/// Class F-2 paired α correction: (1 + α·k₁)(1 + α·k₂).
/// Captures 2-internal-interface gluing in multi-simplex composite.
fn alpha_pair_corrections() -> Vec<(&'static str, i32, i32)> {
    vec![
        ("·(1+α)(1+α)",       1, 1),  ("·(1+NTα)(1+NTα)",      2, 2),
        ("·(1+NSα)(1+NSα)",   3, 3),  ("·(1+NT²α)(1+NT²α)",    4, 4),
        ("·(1+α)(1+NTα)",     1, 2),  ("·(1+α)(1+NSα)",        1, 3),
        ("·(1+NTα)(1+NSα)",   2, 3),  ("·(1+NTα)(1+NT²α)",     2, 4),
        ("·(1+NSα)(1+NT²α)",  3, 4),  ("·(1+NTα)(1+dα)",       2, 5),
        ("·(1+NSα)(1+dα)",    3, 5),  ("·(1+α)(1+NS·NTα)",     1, 6),
        ("·(1+NSα)(1+NS²α)",  3, 9),  ("·(1+NTα)(1+NS²α)",     2, 9),
        ("·(1+α)(1−α)",       1,-1),  ("·(1+NSα)(1−NTα)",      3,-2),
    ]
}

/// Apply q · (1 + α·k₁) · (1 + α·k₂) Class F-2 correction.
fn apply_alpha_pair(q: &Q, k1: i32, k2: i32, zeta: &Q) -> Q {
    let q1 = apply_alpha(q, k1, zeta);
    apply_alpha(&q1, k2, zeta)
}

fn hunt(label: &str, target: &Q, pi: &Q, zeta: &Q) {
    let mut best: Vec<(u64, String, Q)> = Vec::new();
    // Pass 1: integer-prefactor candidates
    for (k_lab, k) in atomic_ints() {
        for (t_lab, pi_p, ze_p) in transcendental_combos() {
            let base = candidate(k, pi_p, ze_p, pi, zeta);
            for (a_lab, a_k) in alpha_corrections() {
                let cand = apply_alpha(&base, a_k, zeta);
                let ppm = ppm_diff(target, &cand);
                best.push((ppm, format!("{k_lab}{t_lab}{a_lab}"), cand));
            }
        }
    }
    // Pass 2: rational-prefactor candidates p/q (sub-simplex weights)
    for (f_lab, p_num, p_den) in atomic_fractions() {
        for (t_lab, pi_p, ze_p) in transcendental_combos() {
            let pi_part = q_pow(pi, pi_p);
            let z_part = q_pow(zeta, ze_p);
            let base: Q = (nat(p_num) * &pi_part.0 * &z_part.0,
                           nat(p_den) * &pi_part.1 * &z_part.1);
            for (a_lab, a_k) in alpha_corrections() {
                let cand = apply_alpha(&base, a_k, zeta);
                let ppm = ppm_diff(target, &cand);
                best.push((ppm, format!("{f_lab}{t_lab}{a_lab}"), cand));
            }
        }
    }
    // Pass 3: α² (Massey-product) corrections on integer prefactors,
    // limited to a small transcendental subset for tractability.
    let trans_subset: &[(&str, u32, u32)] = &[
        ("",     0, 0), ("·ζ(2)",   0, 1), ("·ζ(2)²",  0, 2),
        ("·π",   1, 0), ("·π²",     2, 0), ("·π³",     3, 0),
        ("·π⁴",  4, 0), ("·π⁵",     5, 0), ("·π·ζ(2)", 1, 1),
        ("·π³·ζ(2)", 3, 1), ("·π·ζ(2)²", 1, 2),
    ];
    for (k_lab, k) in atomic_ints() {
        for (t_lab, pi_p, ze_p) in trans_subset {
            let base = candidate(k, *pi_p, *ze_p, pi, zeta);
            for (a_lab, a_k) in alpha_sq_corrections() {
                let cand = apply_alpha_sq(&base, a_k, zeta);
                let ppm = ppm_diff(target, &cand);
                best.push((ppm, format!("{k_lab}{t_lab}{a_lab}"), cand));
            }
        }
    }
    // Pass 4: Class F-2 paired α correction (multi-simplex composite).
    // Limited transcendental subset for tractability.
    for (k_lab, k) in atomic_ints() {
        for (t_lab, pi_p, ze_p) in trans_subset {
            let base = candidate(k, *pi_p, *ze_p, pi, zeta);
            for (p_lab, k1, k2) in alpha_pair_corrections() {
                let cand = apply_alpha_pair(&base, k1, k2, zeta);
                let ppm = ppm_diff(target, &cand);
                best.push((ppm, format!("{k_lab}{t_lab}{p_lab}"), cand));
            }
        }
    }
    // Pass 4b: Class F-2 paired α with rational prefactors.
    for (f_lab, p_num, p_den) in atomic_fractions() {
        for (t_lab, pi_p, ze_p) in trans_subset {
            let pi_part = q_pow(pi, *pi_p);
            let z_part = q_pow(zeta, *ze_p);
            let base: Q = (nat(p_num) * &pi_part.0 * &z_part.0,
                           nat(p_den) * &pi_part.1 * &z_part.1);
            for (p_lab, k1, k2) in alpha_pair_corrections() {
                let cand = apply_alpha_pair(&base, k1, k2, zeta);
                let ppm = ppm_diff(target, &cand);
                best.push((ppm, format!("{f_lab}{t_lab}{p_lab}"), cand));
            }
        }
    }
    best.sort_by_key(|(p, _, _)| *p);
    println!("--- {label} ---");
    println!("  target = {}", decimal(target, 9));
    for (ppm, lab, val) in best.iter().take(5) {
        println!("  {:<36} = {} ({} ppm)",
            lab, decimal(val, 9), ppm);
    }
    println!();
}

fn main() {
    let n_pi: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(2000);
    let n_z:  u64 = std::env::args().nth(2)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);
    let stuck_only = std::env::args().any(|a| a == "--stuck");

    // π midpoint from Leibniz bracket
    let (pi_lo, pi_hi) = pi_bracket(n_pi);
    let pi: Q = ((&pi_lo.0 * &pi_hi.1 + &pi_hi.0 * &pi_lo.1),
                  nat(2) * &pi_lo.1 * &pi_hi.1);

    // ζ(2) midpoint from Basel partial + 1/(N+1)
    let s = s_partial(n_z);
    let np1 = nat(n_z + 1);
    let zeta: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);

    println!("=== atomic-hunter — auto search for atomic identities ===\n");
    println!("brackets: π midpoint (Leibniz N={n_pi}), ζ(2) tight (Basel N={n_z})");
    if stuck_only {
        println!("[--stuck mode: focused on Class F composite-particle targets]");
    }
    println!();

    // m_n/m_p = 1.001378 (Class F-2 composite candidate)
    let mn_mp: Q = (nat(1001378u64), nat(1_000_000));
    hunt("m_n/m_p", &mn_mp, &pi, &zeta);

    // proton g-factor g_p = 5.5856946893
    let g_p: Q = (nat(55856946893u64), nat(10_000_000_000u64));
    hunt("g_p (proton)", &g_p, &pi, &zeta);

    // (m_n − m_p) / m_e = 1.293/0.5110 ≈ 2.5306
    let dmn_me: Q = (nat(25306), nat(10_000));
    hunt("(m_n−m_p)/m_e", &dmn_me, &pi, &zeta);

    if stuck_only { return; }

    // ── Single-simplex targets (already largely closed) ─────────
    let mp_me: Q = (nat(183615267343u64), nat(100_000_000));
    hunt("m_p/m_e", &mp_me, &pi, &zeta);
    let r_p_ratio: Q = (nat(40008), nat(10_000));
    hunt("r_p·m_p/(ℏc)", &r_p_ratio, &pi, &zeta);
    let mt_me: Q = (nat(347715), nat(100));
    hunt("m_τ/m_e", &mt_me, &pi, &zeta);
    let mmu_me: Q = (nat(20676828380u64), nat(100_000_000));
    hunt("m_μ/m_e (sanity)", &mmu_me, &pi, &zeta);
    let mw_me: Q = (nat(157296477u64), nat(1));
    hunt("m_W/m_e", &mw_me, &pi, &zeta);
    let alpha_mp_me: Q = (nat(13398396u64), nat(1_000_000));
    hunt("α_em·m_p/m_e", &alpha_mp_me, &pi, &zeta);
}


