//! `wz-bosons` — m_W²/m_Z² = cos²θ_W = π²/(3 + π²) = 6·ζ(2)/(3 + 6·ζ(2))
//! Lean: WZBosons.lean.
//!
//! Pure 213 ratio (no external constants beyond ζ(2) bracket).

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);
    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);

    println!("=== m_W²/m_Z² = cos²θ_W (N = {n}) ===\n");
    println!("ζ(2)            ≈ {}", decimal(&zeta_tight, 9));
    let six_zeta: Q = (&zeta_tight.0 * nat(6), zeta_tight.1.clone());
    println!("6·ζ(2) = π²     ≈ {}", decimal(&six_zeta, 9));

    // m_W²/m_Z² = 6ζ(2) / (3 + 6ζ(2))
    let three: Q = (nat(3), nat(1));
    let denom: Q = (&three.0 * &six_zeta.1 + &six_zeta.0 * &three.1,
                    &three.1 * &six_zeta.1);
    let cos2: Q = (&six_zeta.0 * &denom.1, &six_zeta.1 * &denom.0);

    println!("3 + 6·ζ(2)      ≈ {}", decimal(&denom, 9));
    println!();
    println!("DRLT cos²θ_W    = {}    ★", decimal(&cos2, 9));
    println!("Observed m_W²/m_Z² ≈ 0.7686  (PDG)");

    let observed: Q = (nat(7686), nat(10000));
    let l = &cos2.0 * &observed.1; let r = &observed.0 * &cos2.1;
    let dn = if l > r { l - r } else { r - l };
    let diff: Q = (dn, &cos2.1 * &observed.1);
    let pct: Q = (&diff.0 * nat(10000) * &observed.1, &diff.1 * &observed.0);
    println!("|Δ|             ≈ {} ({} ×10⁻⁴)",
        decimal(&diff, 6), decimal(&pct, 2));

    println!("\nClosed form: m_W²/m_Z² = π²/(3+π²) = 6ζ(2)/(3+6ζ(2))");
    println!("Pure 213-rational (no external constant beyond ζ(2) bracket).");
    println!("\nm_W/m_Z ≈ √cos²θ_W ≈ 0.876 (DRLT bare) vs 0.881 (PDG)");
    println!("\nLean cite: WZBosons (cos²θ_W = π²/(3+π²))");
}
