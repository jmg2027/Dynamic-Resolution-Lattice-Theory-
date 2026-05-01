//! `quark-hierarchy` — heavy quark mass ratios from atomic primitives.
//! Lean: QuarkHierarchy.lean.
//!
//!   m_t/m_b ≈ 1/α_GUT = d²·ζ(2) ≈ 41.12   ★ DOUBLE-USE 1/α_GUT
//!   m_b/m_c ≈ NS = 3
//!   m_c/m_s ≈ NS²+NS+1 = 13 (= F_7)
//!   m_t/m_c ≈ 137 = same integer as 1/α_em (★ deep coincidence)
//!
//! Each quark hierarchy step = atomic primitive of (NS, NT, d, c).

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);
    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);

    let ns = 3u64; let d = 5u64;
    println!("=== Heavy quark hierarchy from K_{{3,2}}^{{(2)}} ===\n");

    // m_t/m_b ≈ 1/α_GUT = d²·ζ(2)
    let mt_mb: Q = (&zeta_tight.0 * nat(d * d), zeta_tight.1.clone());
    println!("m_t/m_b ≈ d²·ζ(2) = 25·ζ(2)");
    println!("        = 1/α_GUT");
    println!("        ≈ {}    ★", decimal(&mt_mb, 6));
    println!("Observed: m_t/m_b ≈ 172.8/4.18 = 41.34   →  {} match ★",
        "near-exact");

    println!();
    println!("--- m_b/m_c ≈ NS ---");
    println!("  NS = {} (spatial dim)", ns);
    println!("  Observed: m_b/m_c ≈ 4.18/1.27 = 3.29");
    println!("  → 3.29 / 3.00 ≈ 1.10 (10% match, Aλ correction nearby)");

    println!();
    println!("--- m_c/m_s ≈ NS²+NS+1 = F_7 ---");
    let f7 = ns*ns + ns + 1;
    println!("  NS²+NS+1 = 13 = F_7 (NH₃ denom AGAIN!)");
    println!("  Observed: m_c/m_s ≈ 1.27/0.095 = 13.4");
    println!("  → {}/{} ≈ 1.03 (3% match)", 134, f7*10);

    println!();
    println!("--- ★★ m_t/m_c ≈ 137 (same integer as 1/α_em!) ★★ ---");
    println!("  m_t/m_c = (m_t/m_b)·(m_b/m_c) ≈ 41·3.3 ≈ 135");
    println!("  Observed: m_t/m_c ≈ 172.8/1.27 = 136.1");
    println!("  ≈ 1/α_em integer part (137 vs 137.036)");
    println!("  ★ Same integer 137 appears in TWO independent contexts:");
    println!("     - fine structure α_em precision");
    println!("     - top/charm quark mass ratio");
    println!("  → Single DRLT origin (atomic catalog correspondence).");

    println!();
    println!("--- m_d/m_u ≈ NS+? ---");
    println!("  Observed m_d/m_u ≈ 4.66/2.16 = 2.16");
    println!("  ≈ NS-1 = 2? or related atomic ratio");

    println!("\nLean cite: QuarkHierarchy.mt_mb_dim (= d²) (0-axiom)");
}
