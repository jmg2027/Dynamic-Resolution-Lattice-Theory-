"""
HAD_009: A-Vertex Recoil — Every Residual Has Physics
=====================================================
Joint research by Mingu Jeong and Claude (Anthropic)

From atoms branch: H residual 0.054% = m_e/m_p = 0.0545% (98.3% match!)

The A-vertices (quarks) are NOT infinitely massive.
Nuclear recoil = A-vertex acquires tiny temporal component:
  ε_A = m_electron / m_nucleus (atoms)
  ε_A = m_light / m_heavy (hadrons)

In the Gram matrix: A was pure spatial [0,0,1,0,0].
With recoil: A = [ε_A, 0, √(1-ε_A²), 0, 0].
This changes ALL hinge determinants by O(ε_A²).

Apply to: H, He, π, K, ρ, J/ψ, p, Δ, ...
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import numpy as np

D = 5; N_S = 3; N_T = 2
alpha = 6 / (25 * np.pi**2)
Lambda = 308; n_eff = 9
PHI = (1 + np.sqrt(5)) / 2

m_e_MeV = 0.511; m_p_MeV = 938.272
Ry = 13.606  # eV
m_u = 2.16; m_d = 4.67; m_s = 93.4; m_c = 1270; m_b = 4180


class HAD009(Experiment):
    ID = "HAD_009"
    TITLE = "A-Vertex Recoil"

    def run(self):
        self.log("\n=== Part 1: Hydrogen recoil verification ===")
        self.hydrogen_recoil()

        self.log("\n=== Part 2: Meson recoil corrections ===")
        self.meson_recoil()

        self.log("\n=== Part 3: Baryon recoil ===")
        self.baryon_recoil()

        self.log("\n=== Part 4: Updated scorecard ===")
        self.scorecard()

    def hydrogen_recoil(self):
        """H: the A-vertex recoil = m_e/m_p.

        Standard QM: IE = Ry × μ/m_e = Ry × (1 - m_e/m_p + ...)
        DRLT: the A-vertices get temporal component ε_A = m_e/m_p.

        In the Gram matrix, this changes det(AAB):
          det(AAB)_old = 1 - 2ε_B²
          det(AAB)_new = 1 - 2ε_B² - ε_A²×(correction)

        Leading order: IE → IE × (1 - m_e/m_p)
        """
        recoil = m_e_MeV / m_p_MeV
        self.log(f"  m_e/m_p = {recoil:.6f} = {recoil*100:.4f}%")

        # H IE without recoil
        IE_no_recoil = Ry  # 13.606 eV
        IE_with_recoil = Ry * (1 - recoil)
        IE_obs = 13.598  # eV (experimental)

        err_before = (IE_no_recoil - IE_obs) / IE_obs * 100
        err_after = (IE_with_recoil - IE_obs) / IE_obs * 100

        self.log(f"  IE(no recoil)   = {IE_no_recoil:.4f} eV ({err_before:+.4f}%)")
        self.log(f"  IE(with recoil) = {IE_with_recoil:.4f} eV ({err_after:+.4f}%)")
        self.log(f"  Improvement: {abs(err_before)-abs(err_after):.4f}%")
        self.log(f"")
        self.log(f"  Gram interpretation:")
        self.log(f"  A = [ε_A, 0, √(1-ε_A²), 0, 0] with ε_A = m_e/m_p")
        self.log(f"  → det(AAB) shifts by O(ε_A²) → IE × (1-ε_A)")
        self.check(f"Recoil improves H", abs(err_after) < abs(err_before))

    def meson_recoil(self):
        """Meson recoil: quark mass asymmetry.

        For a qq̄ meson, the "recoil" = lighter quark being
        dragged by the heavier one. In the Gram matrix:
          lighter quark: ε_light (small, mostly temporal)
          heavier quark: ε_heavy (larger, more spatial)

        The asymmetry parameter:
          δ = (m_heavy - m_light) / (m_heavy + m_light)

        GMOR correction:
          m_PS² = n_eff × (m₁ + m₂) × Λ × (1 - δ² × c_recoil)

        where c_recoil is determined by the Gram geometry.

        For equal mass (π, J/ψ): δ = 0, no correction.
        For K (u-s): δ = (93.4-2.16)/(93.4+2.16) = 0.955, big correction.
        """
        Delta_hyp = D * Lambda / N_T  # 770 MeV

        mesons = [
            ('π', m_u, m_d, False, 137.3),
            ('K', m_u, m_s, False, 495.6),
            ('ρ', m_u, m_d, True, 775.3),
            ('ω', m_u, m_d, True, 782.7),
            ('K*', m_u, m_s, True, 891.7),
            ('φ', m_s, m_s, True, 1019.5),
            ('η_c', m_c, m_c, False, 2983.9),
            ('J/ψ', m_c, m_c, True, 3096.9),
            ('Υ', m_b, m_b, True, 9460.3),
        ]

        self.log(f"  Asymmetry parameter δ = (m₂-m₁)/(m₂+m₁)")
        self.log(f"  Recoil correction: m² → m² × (1 - δ² × N_T/d²)")
        self.log(f"")

        # The recoil correction factor from Gram geometry:
        # When ε₁ ≠ ε₂, the hinge det changes:
        # det(AAB) with two different B's:
        # det = 1 - ε₁² - ε₂² + ε₁²ε₂² - (ε₁-ε₂)² × cross
        # The correction ∝ (ε₁-ε₂)²/(ε₁+ε₂)² = δ²
        # Coefficient: N_T/d² = 2/25 (from simplex geometry)
        c_recoil = N_T / D**2  # = 2/25 = 0.08

        self.log(f"  c_recoil = N_T/d² = {c_recoil}")
        self.log(f"")
        self.log(f"  {'Name':>5s} {'δ':>6s} {'m_old':>7s} {'m_new':>7s} "
                  f"{'m_obs':>7s} {'err_old':>8s} {'err_new':>8s}")

        self.results = []
        for name, m1, m2, is_vector, m_obs in mesons:
            delta = abs(m2 - m1) / (m2 + m1)
            correction = 1 - delta**2 * c_recoil

            # PS mass
            sigma = 7/8  # cross-gen Gram
            G_cross = np.sqrt(sigma) if abs(m2-m1) > 10 else 1.0
            m_ps_sq = n_eff * (m1 + m2 * G_cross) * Lambda
            m_ps_sq_corr = m_ps_sq * correction
            m_ps = np.sqrt(m_ps_sq)
            m_ps_corr = np.sqrt(m_ps_sq_corr)

            if is_vector:
                m_old = np.sqrt(m_ps_sq + Delta_hyp**2)
                m_new = np.sqrt(m_ps_sq_corr + Delta_hyp**2)
            else:
                m_old = m_ps
                m_new = m_ps_corr

            err_old = (m_old - m_obs) / m_obs * 100
            err_new = (m_new - m_obs) / m_obs * 100
            improved = abs(err_new) < abs(err_old)
            mark = '★' if improved and abs(err_new) < 3 else ''

            self.log(f"  {name:>5s} {delta:6.3f} {m_old:7.1f} {m_new:7.1f} "
                      f"{m_obs:7.1f} {err_old:+7.1f}% {err_new:+7.1f}% {mark}")
            self.results.append((name, m_new, m_obs, err_new))

    def baryon_recoil(self):
        """Baryon recoil: strange quarks shift the center of mass.

        For baryons, the "recoil" = strange quark being heavier
        changes the simplex geometry.

        The strange mass shift with recoil correction:
        m_s_eff = Λ × (φ/2)² × (1 - δ_s × c_baryon)
        where δ_s = m_s/(m_s + Λ) and c_baryon = from Gram.
        """
        m_p_base = N_S * Lambda * (1 + 2*alpha*N_S/D)/(1 + alpha*N_S/D)
        delta_N = Lambda * (D**2 - 1) / D**2  # 295.7
        m_s_shift = Lambda * (PHI/2)**2  # 201.4 Born probability

        baryons = [
            ('p', 938.3, 0, False),
            ('n', 939.6, 0, False),
            ('Δ', 1232.0, 0, True),
            ('Σ⁺', 1189.4, 1, False),
            ('Ξ⁰', 1314.9, 2, False),
            ('Σ*', 1383.7, 1, True),
            ('Ξ*', 1531.8, 2, True),
            ('Ω⁻', 1672.5, 3, True),
        ]

        # Recoil correction for strange baryons:
        # Each strange quark has δ_s = m_s/(m_s+Λ)
        delta_s = m_s / (m_s + Lambda)
        c_baryon = N_T / D  # = 2/5

        self.log(f"  Strange asymmetry: δ_s = m_s/(m_s+Λ) = {delta_s:.4f}")
        self.log(f"  c_baryon = N_T/d = {c_baryon}")
        self.log(f"")
        self.log(f"  {'Name':>5s} {'n_s':>3s} {'m_pred':>7s} "
                  f"{'m_obs':>7s} {'err':>8s}")

        for name, m_obs, n_s, is_decuplet in baryons:
            # Recoil-corrected strange shift
            recoil_factor = (1 - n_s * delta_s * c_baryon)
            m_pred = m_p_base + n_s * m_s_shift * recoil_factor
            if is_decuplet:
                m_pred += delta_N

            err = (m_pred - m_obs) / m_obs * 100
            flag = '★' if abs(err) < 3 else ''
            self.log(f"  {name:>5s} {n_s:3d} {m_pred:7.1f} "
                      f"{m_obs:7.1f} {err:+7.1f}% {flag}")
            self.results.append((name, m_pred, m_obs, err))

    def scorecard(self):
        """Final scorecard with recoil corrections."""
        errs = [abs(r[3]) for r in self.results]
        median = np.median(errs)
        within3 = sum(1 for e in errs if e < 3)
        within5 = sum(1 for e in errs if e < 5)
        total = len(errs)

        self.log(f"\n  ═══════════════════════════════════════")
        self.log(f"  SCORECARD WITH RECOIL: {total} hadrons")
        self.log(f"  Median: {median:.1f}%")
        self.log(f"  Within 3%: {within3}/{total}")
        self.log(f"  Within 5%: {within5}/{total}")
        self.log(f"  ═══════════════════════════════════════")

        self.check(f"Median < 5%", median < 5)


if __name__ == "__main__":
    HAD009().execute()
