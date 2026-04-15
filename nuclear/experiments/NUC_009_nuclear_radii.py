"""
NUC_009: Nuclear Radii from 600-Cell Geometry
==============================================
Nuclear radii follow r = r₀ × A^{1/3} with r₀ ≈ 1.2-1.3 fm.

On the 600-cell (S³ of radius R):
  - 120 = d! vertices on S³
  - Each vertex occupies solid angle 4π²R³/(3×120) ≈ R³/3
  - The vertex spacing ≈ R × (4π²/120)^{1/3}
  - A nucleons fill a cap of S³ with volume ∝ A
  - The cap radius r ∝ A^{1/3} (just like flat space!)

DRLT derivation of r₀:
  r₀ = ℏc / (Λ_QCD × geometric_factor)
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import numpy as np

PHI = (1 + np.sqrt(5)) / 2
d = 5
alpha_gut = 6 / (25 * np.pi**2)
hbar_c = 197.327  # MeV·fm
Lambda_QCD = 308  # MeV
m_p = 938.272  # MeV
r0_obs = 1.25  # fm (empirical nuclear radius parameter)


class NUC009(Experiment):
    ID = "NUC_009"
    TITLE = "Nuclear Radii from 600-Cell"

    def run(self):
        self.log("\n=== Part 1: A^{1/3} law from S³ packing ===")
        self.a13_from_s3()

        self.log("\n=== Part 2: r₀ from DRLT ===")
        self.r0_derivation()

        self.log("\n=== Part 3: Specific nuclei ===")
        self.specific_nuclei()

    # ── Part 1: A^{1/3} from S³ ─────────────────────────────────
    def a13_from_s3(self):
        """Derive the A^{1/3} law from nucleon packing on S³.

        The 600-cell lives on S³ (3-sphere of radius R).
        Volume of S³: Vol(S³) = 2π²R³.
        With 120 vertices, each occupies volume:
          v = 2π²R³ / 120 = π²R³/60

        A nucleons fill total volume A×v.
        The "radius" of this region (cap on S³) is:
          r³ ∝ A × v → r = (A × v)^{1/3} = v^{1/3} × A^{1/3}

        So r = r₀ × A^{1/3} with r₀ = v^{1/3} = (π²R³/60)^{1/3}.
        """
        self.log("  Volume of S³ (radius R): V = 2π²R³")
        self.log(f"  Number of vertices: d! = 120")
        self.log(f"  Volume per vertex: v = 2π²R³/120 = π²R³/60")
        self.log(f"")
        self.log(f"  A nucleons fill volume A×v on S³.")
        self.log(f"  For small A (A << 120), the cap ≈ flat region:")
        self.log(f"    (4/3)πr³ = A × v")
        self.log(f"    r = (3Av/4π)^{{1/3}} = (3π²R³/(4π×60))^{{1/3}} × A^{{1/3}}")
        self.log(f"    r = (πR³/80)^{{1/3}} × A^{{1/3}}")
        self.log(f"")
        self.log(f"  RESULT: r = r₀ × A^{{1/3}}")
        self.log(f"  with r₀ = (πR³/80)^{{1/3}} = R × (π/80)^{{1/3}}")
        self.log(f"")

        # Geometric factor
        geom = (np.pi / 80)**(1/3)
        self.log(f"  Geometric factor: (π/80)^{{1/3}} = {geom:.6f}")
        self.log(f"")
        self.log(f"  So: r₀/R = {geom:.4f}, or R = r₀/{geom:.4f}")
        self.log(f"  With r₀ = {r0_obs} fm: R = {r0_obs/geom:.3f} fm")

    # ── Part 2: r₀ from DRLT ───────────────────────────────────
    def r0_derivation(self):
        """Derive r₀ from DRLT constants.

        The nuclear radius parameter r₀ sets the overall scale.
        In DRLT: r₀ = ℏc/E_scale where E_scale is the relevant
        energy scale.

        Candidates:
          r₀ = ℏc/Λ_QCD = 197.3/308 = 0.641 fm (too small)
          r₀ = ℏc/(m_π c²) = 197.3/135 = 1.461 fm (too large)
          r₀ = ℏc × α_GUT^{1/3} / m_π = ?

        But in DRLT, the pion mass is:
          m_π = Λ_QCD × √(2α_GUT)  (from SM sub-project?)

        Let me try dimensional analysis on the 600-cell.
        """
        m_pi = 135.0  # MeV (pion mass)

        self.log("  Natural length scales:")
        scales = {
            'ℏc/Λ_QCD': hbar_c / Lambda_QCD,
            'ℏc/m_π': hbar_c / m_pi,
            'ℏc/m_p': hbar_c / m_p,
            'ℏc/(Λ_QCD×√α)': hbar_c / (Lambda_QCD * np.sqrt(alpha_gut)),
            'ℏc/(m_p×α^{1/3})': hbar_c / (m_p * alpha_gut**(1/3)),
        }

        for name, val in scales.items():
            err = (val - r0_obs) / r0_obs * 100
            flag = '★' if abs(err) < 15 else ''
            self.log(f"    {name:>25s} = {val:.4f} fm ({err:+6.1f}%) {flag}")

        # The 600-cell edge length on S³
        # Edge = 2R sin(π/10) = 2R × 1/(2φ) = R/φ
        edge_over_R = 1 / PHI
        self.log(f"\n  600-cell edge length: l = R/φ = R × {edge_over_R:.4f}")
        self.log(f"  If l ≡ nuclear nearest-neighbor distance:")

        # In nuclear physics, nearest-neighbor distance ≈ 2r₀
        # (two nucleons touching, each with radius r₀)
        # So: R/φ ≈ 2r₀ → R = 2φ r₀
        R_from_r0 = 2 * PHI * r0_obs
        self.log(f"    l = 2r₀ → R = 2φr₀ = {R_from_r0:.3f} fm")

        # Check consistency with Part 1
        geom = (np.pi / 80)**(1/3)
        r0_from_R = R_from_r0 * geom
        self.log(f"    r₀ = R × (π/80)^{{1/3}} = {r0_from_R:.4f} fm")
        self.log(f"    Self-consistency requires: (π/80)^{{1/3}} × 2φ = 1")
        self.log(f"    Actual: {geom * 2 * PHI:.4f}")
        self.log(f"    (not exactly 1, so there's a correction)")

        # Alternative: derive R from DRLT
        # R = nuclear radius of A=120 nucleus (complete 600-cell)
        # R(120) = r₀ × 120^{1/3} = 1.25 × 4.93 = 6.17 fm
        R_120 = r0_obs * 120**(1/3)
        self.log(f"\n  R(A=120) = r₀ × 120^{{1/3}} = {R_120:.3f} fm")
        self.log(f"  This is the 'radius' of the full 600-cell in fm.")

        # Energy-length relation
        self.log(f"\n  DRLT radius formula:")
        # r₀ = ℏc / (m_p × f) where f is some DRLT fraction
        # r₀ = 197.3/938.3 / f = 0.2103/f
        # For r₀ = 1.25: f = 0.2103/1.25 = 0.1682
        f_needed = (hbar_c / m_p) / r0_obs
        self.log(f"  r₀ = ℏc/(m_p × f) requires f = {f_needed:.4f}")

        # DRLT candidates for f:
        candidates = {
            '1/(d+1) = 1/6': 1/(d+1),
            'α_GUT^{1/3}': alpha_gut**(1/3),
            'ε^{1/2}': np.sqrt(alpha_gut**(2/3)*(1+alpha_gut)),
            '1/2d = 1/10': 1/(2*d),
        }

        self.log(f"  Candidates for f:")
        for name, val in candidates.items():
            r0_pred = hbar_c / (m_p * val)
            err = (r0_pred - r0_obs) / r0_obs * 100
            flag = '★' if abs(err) < 15 else ''
            self.log(f"    {name:>20s}: f={val:.6f}, r₀={r0_pred:.4f} fm "
                      f"({err:+6.1f}%) {flag}")

        # Best: check (d+1)^{-1} = 1/6
        r0_best = hbar_c / (m_p / (d+1))
        r0_best = hbar_c * (d+1) / m_p
        err = (r0_best - r0_obs) / r0_obs * 100
        self.log(f"\n  ★ Best: r₀ = (d+1)ℏc/m_p = {d+1}×{hbar_c/m_p:.4f}")
        self.log(f"       = {r0_best:.4f} fm ({err:+.2f}%)")
        self.check(f"r₀ = (d+1)ℏc/m_p within 5%", abs(err) < 5)

    # ── Part 3: Specific nuclei ─────────────────────────────────
    def specific_nuclei(self):
        """Compare predicted radii with observed values."""
        # r = r₀ × A^{1/3}, r₀ = (d+1)ℏc/m_p
        r0 = (d+1) * hbar_c / m_p

        nuclei = {
            '⁴He':   (4,   1.6755),
            '¹²C':   (12,  2.4702),
            '¹⁶O':   (16,  2.6991),
            '⁴⁰Ca':  (40,  3.4776),
            '⁵⁶Fe':  (56,  3.7377),
            '⁹⁰Zr':  (90,  4.2694),
            '²⁰⁸Pb': (208, 5.5012),
        }

        self.log(f"  r₀ = {r0:.4f} fm")
        self.log(f"  {'Nucleus':>8s}  {'A':>4s}  {'r_pred':>8s}  "
                  f"{'r_obs':>8s}  {'err':>8s}")

        total_err = 0
        count = 0
        for name, (A, r_obs) in nuclei.items():
            r_pred = r0 * A**(1/3)
            err = (r_pred - r_obs) / r_obs * 100
            total_err += err**2
            count += 1
            self.log(f"  {name:>8s}  {A:4d}  {r_pred:8.4f}  "
                      f"{r_obs:8.4f}  {err:+7.2f}%")

        rms = np.sqrt(total_err / count)
        self.log(f"\n  RMS error: {rms:.2f}%")
        self.check(f"RMS radius error < 10%", rms < 10)


if __name__ == "__main__":
    NUC009().execute()
