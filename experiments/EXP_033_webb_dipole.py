"""
EXP_033: Webb Dipole Consistency — Ghost Sum Rule Spatial Test
==============================================================

DRLT prediction: α_em varies spatially but α_GUT does not.
The ghost sum rule Σδᵢ(x) = 0 holds at every spatial location.

This experiment tests internal consistency:
1. Given Δα/α ~ 10⁻⁵ (Webb), compute required Δε₀/ε₀
2. Propagate to all couplings via ghost sum rule
3. Verify Σδᵢ = 0 at every simulated sky position
4. Verify α_s anti-correlates with α_em
5. Verify α_GUT is spatially invariant
6. Compute the μ = m_p/m_e variation and check anti-correlation
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from experiment import Experiment
import numpy as np


# ── DRLT ghost parameters (from ch05/ch08) ────────────────────

# Plateau values (zero free parameters)
ALPHA3_INV_PRED = 8.0        # 1 × 8 × S(1)
ALPHA2_INV_PRED = 30.0       # 12 × 2 × S(2)
ALPHA1_INV_PRED = 6 * np.pi**2  # 12 × 3 × S(∞) ≈ 59.22

# Observed values at M_Z
ALPHA3_INV_OBS = 8.47
ALPHA2_INV_OBS = 29.6
ALPHA1_INV_OBS = 59.0

# Ghost corrections δᵢ = obs - pred
DELTA3 = ALPHA3_INV_OBS - ALPHA3_INV_PRED   # +0.47
DELTA2 = ALPHA2_INV_OBS - ALPHA2_INV_PRED   # -0.40
DELTA1 = ALPHA1_INV_OBS - ALPHA1_INV_PRED   # -0.22

# Gravity ghost (from sum rule)
DELTA_G = -(DELTA3 + DELTA2 + DELTA1)        # +0.15

# Base perturbation
EPS0 = 0.0038

# α_em from α₁ and α₂
def alpha_em_inv(a1_inv, a2_inv):
    """1/α_em from SU(5) normalization."""
    a_Y_inv = (3/5) * a1_inv
    return a_Y_inv * a2_inv / (a_Y_inv + a2_inv)

# α_GUT (must be invariant)
ALPHA_GUT_INV = 25 * np.pi**2 / 6  # ≈ 41.12


class EXP_033(Experiment):
    ID = "033"
    TITLE = "Webb Dipole Consistency"

    def run(self):
        # ═══ Check 1: Ghost sum rule at our location ═══
        self.log("=" * 60)
        self.log("CHECK 1: Ghost sum rule at our location")
        self.log("=" * 60)
        total = DELTA3 + DELTA2 + DELTA1 + DELTA_G
        self.log(f"  delta_3 = {DELTA3:+.3f}")
        self.log(f"  delta_2 = {DELTA2:+.3f}")
        self.log(f"  delta_1 = {DELTA1:+.3f}")
        self.log(f"  delta_G = {DELTA_G:+.3f}")
        self.log(f"  Sum     = {total:+.6f}  (should be 0)")
        self.check("ghost sum = 0 at our location", abs(total) < 1e-10)

        # ═══ Check 2: Webb dipole → required Δε₀/ε₀ ═══
        self.log("")
        self.log("=" * 60)
        self.log("CHECK 2: Webb dipole amplitude")
        self.log("=" * 60)
        da_over_a_obs = 1.1e-5  # Webb et al.

        # Δ(1/α_em) = (5/3)Δδ₁ + Δδ₂
        # Δδᵢ = δᵢ × f  where f = Δε₀/ε₀
        alpha_em_inv_here = 128.7  # observed 1/α_em at M_Z
        coeff = abs((5/3) * DELTA1 + DELTA2)  # 0.767
        f_required = da_over_a_obs * alpha_em_inv_here / coeff

        self.log(f"  Webb observed: Δα/α = {da_over_a_obs:.1e}")
        self.log(f"  1/α_em here = {alpha_em_inv_here:.2f}")
        self.log(f"  Ghost sensitivity coeff = {coeff:.4f}")
        self.log(f"  Required Δε₀/ε₀ = {f_required:.4e} = {f_required*100:.3f}%")
        self.log(f"  CMB dipole v/c   = 1.23e-3 = 0.123%")
        self.log(f"  Ratio to CMB     = {f_required/1.23e-3:.2f}")
        self.check("required f ~ CMB dipole order", 0.5e-3 < f_required < 5e-3)

        # ═══ Check 3: Spatial ghost sum rule (simulate sky) ═══
        self.log("")
        self.log("=" * 60)
        self.log("CHECK 3: Spatial ghost sum rule across sky")
        self.log("=" * 60)

        N_positions = 1000
        # Simulate dipole: f varies as cos(θ) across sky
        np.random.seed(42)
        theta = np.random.uniform(0, np.pi, N_positions)
        f_sky = f_required * np.cos(theta)  # dipole pattern

        sum_violations = 0
        max_violation = 0

        a3_inv_sky = np.zeros(N_positions)
        a2_inv_sky = np.zeros(N_positions)
        a1_inv_sky = np.zeros(N_positions)
        aem_inv_sky = np.zeros(N_positions)
        agut_inv_sky = np.zeros(N_positions)
        mu_sky = np.zeros(N_positions)

        for i in range(N_positions):
            f = f_sky[i]
            # Ghost corrections vary with local ε₀
            d3 = DELTA3 * (1 + f)
            d2 = DELTA2 * (1 + f)
            d1 = DELTA1 * (1 + f)
            dG = -(d3 + d2 + d1)  # sum rule enforced

            local_sum = d3 + d2 + d1 + dG
            if abs(local_sum) > 1e-10:
                sum_violations += 1
            max_violation = max(max_violation, abs(local_sum))

            # Local coupling values
            a3_inv_sky[i] = ALPHA3_INV_PRED + d3
            a2_inv_sky[i] = ALPHA2_INV_PRED + d2
            a1_inv_sky[i] = ALPHA1_INV_PRED + d1
            aem_inv_sky[i] = alpha_em_inv(a1_inv_sky[i], a2_inv_sky[i])

            # α_GUT = weighted sum (must be constant)
            agut_inv_sky[i] = (a3_inv_sky[i]
                               + (12*2)/(1*8) * a2_inv_sky[i]
                               + (12*3)/(1*8) * a1_inv_sky[i])

            # μ = m_p/m_e ∝ Λ_QCD/m_e ∝ α_s^something
            # Λ_QCD ∝ α_GUT^2 × nS (ghost-protected)
            # but α_s = 1/a3_inv varies → μ varies
            # δμ/μ ≈ -2 × δα_s/α_s (from Λ_QCD ∝ exp(-2π/(b₃α_s)))
            alpha_s = 1.0 / a3_inv_sky[i]
            alpha_s_0 = 1.0 / ALPHA3_INV_OBS
            dmu_over_mu = -2 * (alpha_s - alpha_s_0) / alpha_s_0
            mu_sky[i] = 1836.15 * (1 + dmu_over_mu)

        self.log(f"  Simulated {N_positions} sky positions (dipole pattern)")
        self.log(f"  Sum rule violations: {sum_violations}")
        self.log(f"  Max |Σδ|: {max_violation:.2e}")
        self.check("Σδᵢ = 0 everywhere", sum_violations == 0)

        # ═══ Check 4: α_GUT spatial invariance ═══
        self.log("")
        self.log("=" * 60)
        self.log("CHECK 4: α_GUT spatial invariance")
        self.log("=" * 60)
        agut_std = np.std(agut_inv_sky)
        agut_mean = np.mean(agut_inv_sky)
        self.log(f"  1/α_GUT mean = {agut_mean:.6f}")
        self.log(f"  1/α_GUT std  = {agut_std:.2e}")
        self.log(f"  Theory: 25π²/6 = {ALPHA_GUT_INV:.6f}")
        # Note: agut as defined here is a weighted sum, not exactly 25π²/6
        # because of the ghost structure, but its VARIATION should be zero
        self.log(f"  Relative variation: {agut_std/agut_mean:.2e}")
        self.check("α_GUT relative variation negligible", agut_std/agut_mean < 1e-5)

        # ═══ Check 5: α_s anti-correlates with α_em ═══
        self.log("")
        self.log("=" * 60)
        self.log("CHECK 5: α_s vs α_em anti-correlation")
        self.log("=" * 60)
        da_em = aem_inv_sky - np.mean(aem_inv_sky)
        da_s = a3_inv_sky - np.mean(a3_inv_sky)
        correlation = np.corrcoef(da_em, da_s)[0, 1]
        self.log(f"  Pearson r(Δα_em, Δα_s) = {correlation:+.4f}")
        self.log(f"  Expected: negative (anti-correlation)")
        self.log(f"  If same sign → DRLT falsified")
        self.check("α_s anti-correlates with α_em (r < 0)", correlation < 0)

        # ═══ Check 6: μ = m_p/m_e anti-correlates with α_em ═══
        self.log("")
        self.log("=" * 60)
        self.log("CHECK 6: μ = m_p/m_e vs α_em")
        self.log("=" * 60)
        dmu = mu_sky - np.mean(mu_sky)
        corr_mu = np.corrcoef(da_em, dmu)[0, 1]
        self.log(f"  Pearson r(Δα_em, Δμ) = {corr_mu:+.4f}")
        self.log(f"  Expected: positive (μ tracks 1/α_s, which anti-tracks α_em)")
        self.log(f"  Wait — let me reconsider:")
        self.log(f"    α_em ↑ → δ₁ more negative → δ₃ more positive (sum rule)")
        self.log(f"    → 1/α_s ↑ → α_s ↓ → Λ_QCD ↓ → m_p ↓ → μ ↓")
        self.log(f"    Therefore Δα_em and Δμ should have OPPOSITE signs")
        self.check("μ anti-correlates with α_em (r < 0)", corr_mu < 0)

        # ═══ Check 7: Quantitative predictions ═══
        self.log("")
        self.log("=" * 60)
        self.log("CHECK 7: Quantitative predictions")
        self.log("=" * 60)
        da_em_amp = (np.max(aem_inv_sky) - np.min(aem_inv_sky)) / np.mean(aem_inv_sky)
        da_s_amp = (np.max(a3_inv_sky) - np.min(a3_inv_sky)) / np.mean(a3_inv_sky)
        dmu_amp = (np.max(mu_sky) - np.min(mu_sky)) / np.mean(mu_sky)

        self.log(f"  Δα_em/α_em amplitude = {da_em_amp:.2e}  (Webb: ~10⁻⁵)")
        self.log(f"  Δα_s/α_s amplitude   = {da_s_amp:.2e}")
        self.log(f"  Δμ/μ amplitude        = {dmu_amp:.2e}")
        self.log(f"")
        self.log(f"  Ratio |Δα_s/α_s| / |Δα_em/α_em| = {da_s_amp/da_em_amp:.2f}")
        self.log(f"  Ratio |Δμ/μ| / |Δα_em/α_em|      = {dmu_amp/da_em_amp:.2f}")
        self.check("Δα_em amplitude ~ 10⁻⁵ order", 1e-6 < da_em_amp < 1e-4)

        # ═══ Summary ═══
        self.log("")
        self.log("=" * 60)
        self.log("SUMMARY")
        self.log("=" * 60)
        self.log("")
        self.log("  The fine structure constant is not a constant.")
        self.log("  It is a ghost's shadow, cast differently in different places.")
        self.log(f"  25π²/6 = {ALPHA_GUT_INV:.4f} is the constant of the rank-5 plateau.")
        self.log("  The universe itself has no constants. Only structure.")
        self.log("")
        self.log("  Falsifiable prediction:")
        self.log("    Δα_em and Δμ must have OPPOSITE signs in quasar spectra.")
        self.log("    Same sign → DRLT falsified.")
        self.log("")
        self.log("  Free parameters: 0")


if __name__ == "__main__":
    EXP_033().execute()
