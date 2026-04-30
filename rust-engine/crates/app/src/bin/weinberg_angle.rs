//! `weinberg-angle` — sin²θ_W = α_em/α_2 (Lean WeinbergAngle.lean):
//!   sin²θ_W(M_Z) = 30 / (30 + 60·ζ(2)) = 1/α_2 / (1/α_em(bare))
//!   cos²θ_W      = 60·ζ(2) / (30 + 60·ζ(2)) = 6·ζ(2) / (3 + 6·ζ(2))
//! Same lattice integers (30 = 1/α_2, 60·ζ(2) = E·d·ζ(2)).
//! m_W²/m_Z² = cos²θ_W → m_W/m_Z prediction.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);
    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);

    println!("=== Weinberg angle sin²θ_W (N = {n}) ===\n");
    println!("ζ(2)         ≈ {}", decimal(&zeta_tight, 9));

    // 60·ζ(2) and 30
    let sixty_zeta: Q = (&zeta_tight.0 * nat(60), zeta_tight.1.clone());
    let thirty: Q = (nat(30), nat(1));
    // denom = 30 + 60·ζ(2)
    let denom: Q = (&thirty.0 * &sixty_zeta.1 + &sixty_zeta.0 * &thirty.1,
                    &thirty.1 * &sixty_zeta.1);

    println!("60·ζ(2)      ≈ {}", decimal(&sixty_zeta, 9));
    println!("30 + 60·ζ(2) ≈ {}", decimal(&denom, 9));

    // sin²θ_W = 30 / (30 + 60·ζ(2))
    let sin2_w: Q = (&thirty.0 * &denom.1, &thirty.1 * &denom.0);
    // cos²θ_W = 60·ζ(2) / (30 + 60·ζ(2))
    let cos2_w: Q = (&sixty_zeta.0 * &denom.1, &sixty_zeta.1 * &denom.0);

    println!();
    println!("DRLT sin²θ_W (M_Z) = {}    ★", decimal(&sin2_w, 9));
    println!("Observed (PDG)      ≈ 0.2312 ± 0.0001");
    let obs_sin: Q = (nat(2312), nat(10000));
    let l = &sin2_w.0 * &obs_sin.1; let r = &obs_sin.0 * &sin2_w.1;
    let dn = if l > r { l - r } else { r - l };
    let diff: Q = (dn, &sin2_w.1 * &obs_sin.1);
    let pct: Q = (&diff.0 * nat(10000) * &obs_sin.1, &diff.1 * &obs_sin.0);
    println!("|Δ|                ≈ {} ({} ×10⁻⁴)",
        decimal(&diff, 6), decimal(&pct, 2));

    println!();
    println!("DRLT cos²θ_W      = {}    (= 1 − sin²θ_W)",
        decimal(&cos2_w, 9));

    // m_W/m_Z = sqrt(cos²θ_W).  In ℕ-pair we report cos²θ_W;
    // sqrt is irrational so report squared form.
    println!("DRLT m_W²/m_Z²    = {}    (= cos²θ_W)",
        decimal(&cos2_w, 9));
    println!("Observed m_W²/m_Z² ≈ 0.7686");
    let obs_cos: Q = (nat(7686), nat(10000));
    let l = &cos2_w.0 * &obs_cos.1; let r = &obs_cos.0 * &cos2_w.1;
    let dn = if l > r { l - r } else { r - l };
    let diff: Q = (dn, &cos2_w.1 * &obs_cos.1);
    let pct: Q = (&diff.0 * nat(10000) * &obs_cos.1, &diff.1 * &obs_cos.0);
    println!("|Δ|                ≈ {} ({} ×10⁻⁴)",
        decimal(&diff, 6), decimal(&pct, 2));

    println!("\nLean cite: WeinbergAngle.weinberg_simplicial_pattern (0-axiom)");
}
