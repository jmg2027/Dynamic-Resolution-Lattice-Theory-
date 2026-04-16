"""
CST_016: BBN Light Element Abundances from DRLT
==================================================
Primordial nucleosynthesis with DRLT-predicted eta_B and Omega_b.
Predicts D/H, He-4, He-3, Li-7 mass fractions.

Joint research by Mingu Jeong and Claude (Anthropic).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from drlt import (D, N_S, N_T, ALPHA_GUT,
                  dark_energy_fraction, baryon_asymmetry)
from experiment import Experiment


class BBN(Experiment):
    ID = "CST_016"
    TITLE = "BBN Light Element Abundances"

    def run(self):
        OL = dark_energy_fraction()
        Om = 1 - OL
        DM_b = D + 1.0 / N_S
        Ob = Om / (1 + DM_b)
        eta_B = baryon_asymmetry()

        # H_0 from CST_013
        N_H = D**2*N_S + D*N_T + N_S
        h = np.exp(np.log(D+1) - N_H*np.log(D)
                   + np.log(1.2209e19)) * N_T/N_S
        h_unit = h / (6.5822e-25 * 3.2408e-20)
        h_dimless = h_unit / 100  # h = H_0/100

        ob_h2 = Ob * h_dimless**2

        self.log("\n=== DRLT BBN Parameters ===\n")
        self.log(f"  eta_B  = {eta_B:.4e}")
        self.log(f"  Ob     = {Ob:.6f}")
        self.log(f"  h      = {h_dimless:.4f}")
        self.log(f"  Ob*h^2 = {ob_h2:.6f}")
        self.log(f"  eta_10 = eta_B × 10^10 = {eta_B*1e10:.3f}")

        # Planck comparison
        ob_h2_planck = 0.02237
        eta_planck = 6.12e-10
        self.log(f"\n  Planck: Ob*h^2 = {ob_h2_planck}")
        self.log(f"  Planck: eta = {eta_planck}")
        self.check("eta_B within 1% of Planck",
                    abs(eta_B - eta_planck)/eta_planck < 0.01)

        # ===================================
        # Part 1: Helium-4 mass fraction Y_p
        # ===================================
        self.log(f"\n=== Part 1: He-4 (Y_p) ===\n")

        # Y_p depends on neutron fraction at freeze-out:
        # n/p = exp(-Q/T_freeze) where Q = m_n - m_p = 1.293 MeV
        # T_freeze ~ 0.7 MeV (weak interaction freeze-out)
        # n/p ~ exp(-1.293/0.7) ~ 1/6.7
        # After neutron decay (tau_n = 880 s, BBN at ~180 s):
        # n/p ~ 1/7

        # Number of neutrino species: N_eff
        # In DRLT: N_eff = n_S = 3 (exactly! from (3,2) split)
        N_eff = N_S  # 3

        Q_MeV = 1.2934  # m_n - m_p
        # Freeze-out T depends on N_eff:
        # T_f ∝ (N_eff)^(1/6) × G_F^(-2/3) × ...
        # Standard: T_f ≈ 0.70 MeV for N_eff=3
        T_f = 0.70 * (N_eff / 3.0)**(1./6)

        n_over_p_freeze = np.exp(-Q_MeV / T_f)
        # Neutron decay before BBN (~180 s):
        tau_n = 879.4  # s
        t_BBN = 180.0  # s
        n_over_p = n_over_p_freeze * np.exp(-t_BBN / tau_n)

        # Y_p = 2(n/p) / (1 + n/p)
        Y_p = 2 * n_over_p / (1 + n_over_p)

        # Small correction from eta_B (more baryons → slightly more He)
        # dY/d(eta_10) ≈ +0.002 per unit eta_10
        eta_10 = eta_B * 1e10
        Y_p_corr = Y_p + 0.002 * (eta_10 - 6.0)

        Y_p_obs = 0.2449  # Aver+ 2015
        Y_p_err = 0.0040

        self.log(f"  N_eff = n_S = {N_eff} (exact from DRLT)")
        self.log(f"  T_freeze = {T_f:.3f} MeV")
        self.log(f"  n/p (freeze) = {n_over_p_freeze:.4f}")
        self.log(f"  n/p (BBN)    = {n_over_p:.4f}")
        self.log(f"  Y_p (base)   = {Y_p:.4f}")
        self.log(f"  Y_p (corr)   = {Y_p_corr:.4f}")
        self.log(f"  Observed:      {Y_p_obs} ± {Y_p_err}")
        sig_Y = (Y_p_corr - Y_p_obs) / Y_p_err
        self.log(f"  Deviation:     {sig_Y:+.2f}σ")
        self.check("Y_p within 2σ", abs(sig_Y) < 2)

        # ===================================
        # Part 2: Deuterium D/H
        # ===================================
        self.log(f"\n=== Part 2: Deuterium D/H ===\n")

        # D/H depends sensitively on eta_B
        # Fit from Coc+ 2015:
        # D/H × 10^5 = 2.58 × (6.0/eta_10)^1.6
        DH_5 = 2.58 * (6.0 / eta_10)**1.6
        DH = DH_5 * 1e-5

        DH_obs = 2.527e-5  # Cooke+ 2018
        DH_err = 0.030e-5
        DH_5_obs = DH_obs * 1e5

        self.log(f"  D/H = 2.58 × (6.0/eta_10)^1.6")
        self.log(f"      = {DH_5:.3f} × 10^-5")
        self.log(f"  Observed: {DH_5_obs:.3f} × 10^-5"
                 f" ± {DH_err*1e5:.3f}")
        sig_D = (DH - DH_obs) / DH_err
        self.log(f"  Deviation: {sig_D:+.2f}σ")
        self.check("D/H within 2σ", abs(sig_D) < 2)

        # ===================================
        # Part 3: Helium-3
        # ===================================
        self.log(f"\n=== Part 3: He-3/H ===\n")

        # He-3/H ~ 1.0 × 10^-5 (weakly dependent on eta)
        He3_H = 1.04e-5 * (6.0 / eta_10)**0.6
        He3_obs = 1.1e-5  # solar system + HII regions
        He3_err = 0.2e-5

        self.log(f"  He-3/H = {He3_H:.3e}")
        self.log(f"  Observed: {He3_obs:.1e} ± {He3_err:.1e}")
        sig_3 = (He3_H - He3_obs) / He3_err
        self.log(f"  Deviation: {sig_3:+.1f}σ")

        # ===================================
        # Part 4: Lithium-7
        # ===================================
        self.log(f"\n=== Part 4: Li-7/H ===\n")

        # Li-7 has the famous "lithium problem":
        # BBN predicts ~5×10^-10 but observed ~1.6×10^-10
        Li_H = 4.68e-10 * (eta_10 / 6.0)**2
        Li_obs = 1.6e-10   # Spite plateau
        Li_err = 0.3e-10

        self.log(f"  Li-7/H (BBN) = {Li_H:.3e}")
        self.log(f"  Observed:      {Li_obs:.1e} ± {Li_err:.1e}")
        self.log(f"  Ratio BBN/obs: {Li_H/Li_obs:.1f}×")
        self.log(f"")
        self.log(f"  THE LITHIUM PROBLEM:")
        self.log(f"  Standard BBN over-predicts Li by factor ~3.")
        self.log(f"  DRLT prediction: factor {Li_H/Li_obs:.1f}×")
        self.log(f"")
        self.log(f"  Possible DRLT resolution:")
        self.log(f"  Simplex confinement (ch15) modifies nuclear")
        self.log(f"  reaction rates at T ~ 0.1 MeV via the")
        self.log(f"  det(G_h) dependence of ℏ_h.")
        self.log(f"  When det → det_min(Li-7 pathway),")
        self.log(f"  the reaction is suppressed.")

        # ===================================
        # Part 5: DRLT Unique: N_eff exactly 3
        # ===================================
        self.log(f"\n=== Part 5: N_eff = n_S = 3 (exact) ===\n")

        # Standard model: N_eff = 3.044 (QED corrections)
        # DRLT: N_eff = n_S = 3 (exactly from (3,2) split)
        # The 0.044 difference is from e+e- annihilation
        # heating the photon bath.
        #
        # In DRLT: the 0.044 comes from the alpha_GUT correction
        N_eff_SM = 3.044
        N_eff_DRLT = N_S * (1 + ALPHA_GUT * N_T / D)
        N_eff_obs = 2.99  # Planck 2018
        N_eff_err = 0.17

        self.log(f"  N_eff(bare DRLT) = n_S = {N_S}")
        self.log(f"  N_eff(+correction) = n_S(1+α·n_T/d)")
        self.log(f"    = {N_S}×(1+{ALPHA_GUT:.4f}×{N_T}/{D})")
        self.log(f"    = {N_eff_DRLT:.4f}")
        self.log(f"  Standard Model:  {N_eff_SM}")
        self.log(f"  Observed:        {N_eff_obs} ± {N_eff_err}")
        sig_N = (N_eff_DRLT - N_eff_obs) / N_eff_err
        self.log(f"  Deviation:       {sig_N:+.2f}σ")

        self.check("N_eff within 1σ", abs(sig_N) < 1)

        # ===================================
        # Part 6: Summary Table
        # ===================================
        self.log(f"\n=== Summary Table ===\n")
        self.log(f"  {'Element':<12} {'DRLT':>12} {'Observed':>12}"
                 f" {'Status':>10}")
        self.log(f"  {'-'*46}")
        self.log(f"  {'Y_p (He-4)':<12} {Y_p_corr:>12.4f}"
                 f" {Y_p_obs:>12.4f} {sig_Y:>+10.1f}σ")
        self.log(f"  {'D/H ×10^5':<12} {DH_5:>12.3f}"
                 f" {DH_5_obs:>12.3f} {sig_D:>+10.1f}σ")
        self.log(f"  {'He3/H ×10^5':<12} {He3_H*1e5:>12.3f}"
                 f" {He3_obs*1e5:>12.1f} {sig_3:>+10.1f}σ")
        self.log(f"  {'Li7/H ×10^10':<12} {Li_H*1e10:>12.2f}"
                 f" {Li_obs*1e10:>12.1f} {'(Li prob)':>10}")
        self.log(f"  {'N_eff':<12} {N_eff_DRLT:>12.3f}"
                 f" {N_eff_obs:>12.2f} {sig_N:>+10.2f}σ")
        self.log(f"")
        self.log(f"  All from DRLT: eta_B, N_eff, Ob from simplex.")


if __name__ == "__main__":
    BBN().execute()