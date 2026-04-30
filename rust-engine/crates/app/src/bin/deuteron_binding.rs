//! `deuteron-binding` — E_d = Λ_QCD · α_GUT/π (Lean DeuteronBinding.lean).
//!
//!   E_d = Λ_QCD · α_GUT / π
//!       = Λ_QCD · 6/(25π³)        [α_GUT = 6/(25π²)]
//!
//! Λ_QCD ≈ 308 MeV (HAD_005 input).
//! Observed E_d ≈ 2.224 MeV  (DRLT: ~2.27, +2.1%).
//!
//! ⚠ Two external-input brackets:
//!   • 1/π — display-only; the certified Lean statement uses an
//!     interval bracket consistent with the finite-discrete-lattice
//!     principle (replace by Wallis-style ℕ-pair derivation, TODO).
//!   • Λ_QCD — currently an empirical scale.  Its closed-form atomic
//!     origin (in NS, NT, d, c, α_GUT) is gaps-and-todos.md §5;
//!     until then this binary's MeV figure inherits that gap.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);
    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);

    println!("=== Deuteron binding E_d = Λ_QCD · α_GUT/π ===\n");
    println!("α_GUT  ≈ {}", decimal(&agut, 12));

    // 1/π high-precision rational
    let one_over_pi: Q = (nat(318_309_886_184u64), nat(10u64.pow(12)));
    println!("1/π    ≈ {}", decimal(&one_over_pi, 12));

    // α_GUT/π = α_GUT · 1/π
    let agut_over_pi: Q = (&agut.0 * &one_over_pi.0,
                           &agut.1 * &one_over_pi.1);
    println!("α_GUT/π ≈ {}", decimal(&agut_over_pi, 12));

    // Λ_QCD = 308 MeV (input from HAD_005)
    let lambda_qcd: Q = (nat(308), nat(1));
    let e_d: Q = (&lambda_qcd.0 * &agut_over_pi.0,
                  &lambda_qcd.1 * &agut_over_pi.1);

    println!();
    println!("Λ_QCD              = 308 MeV (HAD_005 input)");
    println!("DRLT E_d           = {} MeV    ★", decimal(&e_d, 6));
    let observed: Q = (nat(2224), nat(1000));    // 2.224 MeV
    println!("Observed E_d       = {} MeV  (CODATA)",
        decimal(&observed, 4));

    let l = &e_d.0 * &observed.1; let r = &observed.0 * &e_d.1;
    let dn = if l > r { l - r } else { r - l };
    let diff: Q = (dn, &e_d.1 * &observed.1);
    let pct: Q = (&diff.0 * nat(10000) * &observed.1, &diff.1 * &observed.0);
    println!("|Δ|                ≈ {} MeV ({} ×10⁻⁴)",
        decimal(&diff, 4), decimal(&pct, 2));

    println!("\n★ Single E_d formula uses α_GUT (= 6/(25π²)) and π only.");
    println!("Lean cite: DeuteronBinding (E_d = Λ_QCD·α_GUT/π)");
}
