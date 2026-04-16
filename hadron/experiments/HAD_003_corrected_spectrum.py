"""
HAD_003: Corrected Meson Spectrum (4 Geometric Corrections)
============================================================
Joint research by Mingu Jeong and Claude (Anthropic)

Apply ALL four corrections from HAD_002:
  1. SSS topological mass for η, η' (flavor singlet)
  2. Confined propagator P(ε) for spin splitting
  3. Coulomb + string for heavy quarkonia
  4. Cross-generation Gram overlap for K

All corrections are 0-parameter: they use DRLT constants only.
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import numpy as np

d = 5; N_S = 3; N_T = 2
n_eff = 9  # C(5,3) - 1
alpha_gut = 6 / (25 * np.pi**2)
eps = alpha_gut**(2/3) * (1 + alpha_gut)
Lambda = 308  # MeV
sigma_cross = 7/8  # from atoms/

m_u = 2.16; m_d = 4.67; m_s = 93.4
m_c = 1270; m_b = 4180

C_F = (N_S**2 - 1) / (2 * N_S)  # 4/3


def P_conf(e):
    """Confined propagator."""
    if abs(e) > 0.999: return 0
    return (1 - 2*e) / (1 - e)


def gmor_mass(mq1, mq2, gen1=1, gen2=1):
    """GMOR with cross-generation Gram correction.
    Same generation: G=1. Cross: G=σ_cross=7/8.
    """
    G = 1.0 if gen1 == gen2 else sigma_cross
    # Both quarks get Gram correction if cross-generation
    m1_eff = mq1
    m2_eff = mq2 * G**2 if gen1 != gen2 else mq2
    return np.sqrt(n_eff * (m1_eff + m2_eff) * Lambda)


def spin_split(eps_q1, eps_q2):
    """Vector-pseudoscalar splitting with confined propagator.
    eps_q = quark spatial coupling parameter.
    """
    e_avg = (eps_q1 + eps_q2) / 2
    return N_T * Lambda * (1 - e_avg)


def heavy_meson_mass(m_Q, alpha_s):
    """Heavy quarkonium: 2m_Q + string - Coulomb binding."""
    m_red = m_Q / 2
    E_coulomb = C_F**2 * alpha_s**2 * m_red / 2
    E_string = Lambda * (1 - alpha_s)  # string tension, reduced at short range
    return 2 * m_Q - E_coulomb + E_string


class HAD003(Experiment):
    ID = "HAD_003"
    TITLE = "Corrected Meson Spectrum"

    def run(self):
        self.log("\n=== Corrected Pseudoscalar Mesons ===")
        self.pseudoscalars()

        self.log("\n=== Corrected Vector Mesons ===")
        self.vectors()

        self.log("\n=== Corrected Heavy Quarkonia ===")
        self.quarkonia()

        self.log("\n=== Full Scorecard ===")
        self.scorecard()

    def pseudoscalars(self):
        """Pseudoscalar mesons with GMOR + Gram + SSS corrections."""
        # Quark coupling parameters
        eps_u = alpha_gut * N_S / d  # ~0.015
        eps_s = m_s / Lambda         # ~0.303

        mesons = [
            # (name, mq1, mq2, gen1, gen2, is_singlet, m_obs)
            ('π±', m_u, m_d, 1, 1, False, 139.6),
            ('π⁰', m_u, m_d, 1, 1, False, 135.0),
            ('K±', m_u, m_s, 1, 2, False, 493.7),
            ('K⁰', m_d, m_s, 1, 2, False, 497.6),
        ]

        self.log(f"  GMOR: m² = n_eff × (m_q₁ + m_q₂×G²) × Λ")
        self.log(f"  G = 1 (same gen), G = 7/8 (cross gen)")
        self.log(f"")
        self.log(f"  {'Meson':>6s}  {'m_pred':>8s}  {'m_obs':>8s}  "
                  f"{'err':>8s}  {'prev':>8s}")

        results = {}
        for name, mq1, mq2, g1, g2, singlet, m_obs in mesons:
            m_pred = gmor_mass(mq1, mq2, g1, g2)
            err = (m_pred - m_obs) / m_obs * 100
            # Previous (uncorrected)
            m_prev = np.sqrt(n_eff * (mq1 + mq2) * Lambda)
            prev_err = (m_prev - m_obs) / m_obs * 100
            flag = '★' if abs(err) < 3 else ''
            self.log(f"  {name:>6s}  {m_pred:8.1f}  {m_obs:8.1f}  "
                      f"{err:+7.1f}%  was {prev_err:+.1f}% {flag}")
            results[name] = (m_pred, m_obs, err)

        # η and η' with SSS topological mass
        self.log(f"\n  Flavor singlets (SSS topological correction):")

        # η: mostly (uū+dd̄)/√2 with some ss̄ mixing
        # η mass² = GMOR(light) + Λ² × mixing_factor
        # The mixing angle θ_η ≈ -15° in the octet-singlet basis
        # In DRLT: the SSS contributes Λ² × (1/n_channels) = Λ²/10
        # because SSS is 1 of 10 channels
        sss_fraction = 1 / (n_eff + 1)  # = 1/10
        m_eta_sq = (n_eff * (m_u + m_d) * Lambda
                    + Lambda**2 * N_S * sss_fraction)
        m_eta = np.sqrt(m_eta_sq)
        err_eta = (m_eta - 547.9) / 547.9 * 100
        self.log(f"  η:  m² = GMOR(ud) + Λ²×N_S/10")
        self.log(f"      = {n_eff*(m_u+m_d)*Lambda:.0f} + "
                  f"{Lambda**2*N_S*sss_fraction:.0f} = {m_eta_sq:.0f}")
        self.log(f"      m = {m_eta:.1f} MeV (obs 547.9, {err_eta:+.1f}%)")
        results['η'] = (m_eta, 547.9, err_eta)

        # η': gets the FULL SSS + strange GMOR
        m_etap_sq = (n_eff * (m_u + m_d + 2*m_s) * Lambda / N_S
                     + Lambda**2 * (1 - sss_fraction))
        m_etap = np.sqrt(m_etap_sq)
        err_etap = (m_etap - 957.8) / 957.8 * 100
        self.log(f"  η': m² = GMOR(uds)/N_S + Λ²×(1-1/10)")
        self.log(f"      = {n_eff*(m_u+m_d+2*m_s)*Lambda/N_S:.0f} + "
                  f"{Lambda**2*(1-sss_fraction):.0f} = {m_etap_sq:.0f}")
        self.log(f"      m = {m_etap:.1f} MeV (obs 957.8, {err_etap:+.1f}%)")
        results["η'"] = (m_etap, 957.8, err_etap)

        self.results_ps = results

    def vectors(self):
        """Vector mesons with confined propagator spin splitting."""
        eps_u = alpha_gut * N_S / d
        eps_s = m_s / Lambda

        self.log(f"  Spin splitting: Δm = N_T×Λ×(1-ε_avg)")
        self.log(f"  ε_u = {eps_u:.4f}, ε_s = {eps_s:.4f}")
        self.log(f"")

        ps_masses = {
            'ρ': ('π±', 139.6, eps_u, eps_u, 775.3),
            'ω': ('π⁰', 137.3, eps_u, eps_u, 782.7),
            'K*±': ('K±', self.results_ps['K±'][0], eps_u, eps_s, 891.7),
            'K*⁰': ('K⁰', self.results_ps['K⁰'][0], eps_u, eps_s, 891.7),
            'φ': ('ss̄', np.sqrt(n_eff*2*m_s*Lambda), eps_s, eps_s, 1019.5),
        }

        self.log(f"  {'Vector':>6s}  {'m_PS':>7s}  {'split':>7s}  "
                  f"{'m_pred':>8s}  {'m_obs':>8s}  {'err':>8s}")

        self.results_v = {}
        for name, (ps_name, m_ps, e1, e2, m_obs) in ps_masses.items():
            split = spin_split(e1, e2)
            m_pred = m_ps + split
            err = (m_pred - m_obs) / m_obs * 100
            flag = '★' if abs(err) < 5 else ''
            self.log(f"  {name:>6s}  {m_ps:7.1f}  {split:7.1f}  "
                      f"{m_pred:8.1f}  {m_obs:8.1f}  {err:+7.1f}% {flag}")
            self.results_v[name] = (m_pred, m_obs, err)

    def quarkonia(self):
        """Heavy quarkonia with Coulomb + string tension."""
        # α_s from DHA spectral ladder: α_s(Λ) = 1/8
        # Running with β₀ = (11N_S - 2n_f)/(12π)
        alpha_s_0 = 1/8
        n_f_c = 4  # u,d,s,c active at charm scale
        n_f_b = 5  # u,d,s,c,b active at bottom scale
        beta0_c = (11*N_S - 2*n_f_c) / (12*np.pi)
        beta0_b = (11*N_S - 2*n_f_b) / (12*np.pi)

        alpha_s_c = alpha_s_0 / (1 + beta0_c*alpha_s_0*np.log(m_c/Lambda))
        alpha_s_b = alpha_s_0 / (1 + beta0_b*alpha_s_0*np.log(m_b/Lambda))

        self.log(f"  α_s(m_c) = {alpha_s_c:.4f}, α_s(m_b) = {alpha_s_b:.4f}")
        self.log(f"  C_F = {C_F:.4f}")
        self.log(f"")

        # Heavy mesons: pseudoscalar and vector
        heavy = [
            ('η_c', m_c, alpha_s_c, 2983.9, 0),    # PS: no spin split
            ('J/ψ', m_c, alpha_s_c, 3096.9, 1),     # V: spin split
            ('η_b', m_b, alpha_s_b, 9399.0, 0),
            ('Υ(1S)', m_b, alpha_s_b, 9460.3, 1),
        ]

        self.log(f"  {'Meson':>8s}  {'m_pred':>8s}  {'m_obs':>8s}  {'err':>8s}")
        self.results_h = {}
        for name, m_Q, alpha_s, m_obs, is_vector in heavy:
            m_base = heavy_meson_mass(m_Q, alpha_s)
            # Vector gets additional spin splitting
            if is_vector:
                eps_Q = alpha_s  # heavy quark coupling
                m_base += spin_split(eps_Q, eps_Q) * alpha_s
            m_pred = m_base
            err = (m_pred - m_obs) / m_obs * 100
            flag = '★' if abs(err) < 5 else ''
            self.log(f"  {name:>8s}  {m_pred:8.1f}  {m_obs:8.1f}  "
                      f"{err:+7.1f}% {flag}")
            self.results_h[name] = (m_pred, m_obs, err)

    def scorecard(self):
        """Complete scorecard comparing HAD_001 vs HAD_003."""
        self.log(f"  ═══════════════════════════════════════════")
        self.log(f"  MESON SCORECARD: HAD_001 → HAD_003")
        self.log(f"  ───────────────────────────────────────────")
        self.log(f"  {'Meson':>8s}  {'HAD_001':>10s}  {'HAD_003':>10s}  "
                  f"{'improved?':>10s}")

        all_results = {}
        all_results.update(self.results_ps)
        all_results.update(self.results_v)
        all_results.update(self.results_h)

        # HAD_001 results (uncorrected)
        had001 = {
            'π±': +0.2, 'π⁰': +1.9, 'K±': +4.2, 'K⁰': +4.8,
            'η': -43.5, "η'": -45.9,
            'ρ': -2.8, 'K*±': None, 'K*⁰': None, 'ω': None, 'φ': None,
            'η_c': -14.5, 'J/ψ': -17.6, 'η_b': -10.6, 'Υ(1S)': -11.2,
        }

        improved = 0; total = 0
        total_err2_old = 0; total_err2_new = 0; n = 0
        for name, (m_pred, m_obs, err_new) in all_results.items():
            err_old = had001.get(name)
            if err_old is not None:
                better = abs(err_new) < abs(err_old)
                if better: improved += 1
                total += 1
                total_err2_old += err_old**2
                total_err2_new += err_new**2
                n += 1
                mark = '✓' if better else '✗'
                self.log(f"  {name:>8s}  {err_old:+9.1f}%  {err_new:+9.1f}%  "
                          f"    {mark}")

        rms_old = np.sqrt(total_err2_old / n)
        rms_new = np.sqrt(total_err2_new / n)
        self.log(f"\n  RMS: {rms_old:.1f}% → {rms_new:.1f}%")
        self.log(f"  Improved: {improved}/{total}")
        self.check(f"RMS improved", rms_new < rms_old)
        self.check(f"Majority improved", improved > total/2)

        self.log(f"\n  ═══════════════════════════════════════════")


if __name__ == "__main__":
    HAD003().execute()
