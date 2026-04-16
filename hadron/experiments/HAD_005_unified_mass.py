"""
HAD_005: Unified Hadron Mass from det(G) and ε
===============================================
Joint research by Mingu Jeong and Claude (Anthropic)

From HAD_004 drawings, the mass depends on TWO things:
  1. det(G) — how "distinguishable" the quarks are
  2. ε — how much each quark lives in spatial ℂ³

Observation: det(G) ≈ 1 means quarks are independent (free).
det(G) → 0 means quarks overlap (confined, SSS-like).

The mass should interpolate between:
  det ≈ 1: GMOR regime (chiral, light)
  det → 0: confinement regime (Λ scale)

Try: m² = n_eff × Σm_q × Λ × det(G) + Λ² × (1-det(G))

When det=1: pure GMOR → m² = n_eff Σm_q Λ (pion)
When det=0: pure Λ² → m = Λ (confinement scale)
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import numpy as np

D = 5; N_S = 3; N_T = 2; n_eff = 9
alpha = 6 / (25 * np.pi**2)
Lambda = 308
m_u = 2.16; m_d = 4.67; m_s = 93.4
m_c = 1270; m_b = 4180


def make_meson(eps1, eps2, same_spin):
    """Build meson Gram matrix from quark couplings.

    eps = spatial fraction of quark (0=temporal, 1=spatial).
    same_spin: True=vector(J=1), False=pseudoscalar(J=0).

    Quark 1: ψ₁ = (t₁, 0, ε₁, 0, 0) or (0, t₁, ε₁, 0, 0)
    Quark 2: ψ₂ = (t₂, 0, 0, ε₂, 0) or (0, t₂, 0, ε₂, 0)

    same_spin → same temporal slot → G₁₂ = t₁t₂ (temporal overlap)
    diff_spin → different slots → G₁₂ = 0
    """
    t1 = np.sqrt(max(0, 1 - eps1**2))
    t2 = np.sqrt(max(0, 1 - eps2**2))

    if same_spin:
        # Same temporal slot: ψ₁=(t₁,0,ε₁,0,0), ψ₂=(t₂,0,0,ε₂,0)
        v1 = np.array([t1, 0, eps1, 0, 0])
        v2 = np.array([t2, 0, 0, eps2, 0])
    else:
        # Different slots: ψ₁=(t₁,0,ε₁,0,0), ψ₂=(0,t₂,0,ε₂,0)
        v1 = np.array([t1, 0, eps1, 0, 0])
        v2 = np.array([0, t2, 0, eps2, 0])

    V = np.array([v1, v2])
    G = V @ V.T
    det = np.linalg.det(G)
    g12 = G[0, 1]
    return det, g12, G


def make_eta(eps_avg):
    """Build η as isotropic spatial overlap."""
    t = np.sqrt(max(0, 1 - 3*eps_avg**2))
    v1 = np.array([t, 0, eps_avg, eps_avg, eps_avg])
    v2 = np.array([0, t, eps_avg, eps_avg, eps_avg])
    v1 /= np.linalg.norm(v1)
    v2 /= np.linalg.norm(v2)
    V = np.array([v1, v2])
    G = V @ V.T
    return np.linalg.det(G), G[0, 1], G


def make_baryon_3q(eps_list):
    """Build baryon from 3 quarks.

    Light quark: pure spatial (eps=1, t=0)
    Strange: eps_s ≈ 0.303 (partial temporal)
    """
    vectors = []
    spatial_dirs = [
        [1, 0, 0],
        [0, 1, 0],
        [0, 0, 1],
    ]
    temporal_dirs = [
        [1, 0],
        [0, 1],
        [0.707, 0.707],
    ]
    for i, eps in enumerate(eps_list):
        t = np.sqrt(max(0, 1 - eps**2))
        s = spatial_dirs[i]
        td = temporal_dirs[i]
        v = np.array([t*td[0], t*td[1], eps*s[0], eps*s[1], eps*s[2]])
        v /= np.linalg.norm(v)
        vectors.append(v)
    V = np.array(vectors)
    G = V @ V.T
    return np.linalg.det(G), G


class HAD005(Experiment):
    ID = "HAD_005"
    TITLE = "Unified Mass from det(G)"

    def run(self):
        self.log("\n=== Part 1: Compute det(G) for all hadrons ===")
        det_table = self.compute_all_det()

        self.log("\n=== Part 2: Try unified formula ===")
        self.unified_formula(det_table)

        self.log("\n=== Part 3: Best formula ===")
        self.best_formula(det_table)

    def compute_all_det(self):
        """Compute det(G) for every hadron."""
        eps_u = alpha * N_S / D   # 0.0146
        eps_d = eps_u             # same for d (1st gen)
        eps_s = m_s / Lambda      # 0.303
        eps_c = np.sqrt(m_c / (m_c + Lambda))  # 0.897
        eps_b = np.sqrt(m_b / (m_b + Lambda))  # 0.965

        self.log(f"  Quark spatial couplings:")
        self.log(f"    ε_u = ε_d = {eps_u:.4f} (light)")
        self.log(f"    ε_s = {eps_s:.4f} (strange)")
        self.log(f"    ε_c = {eps_c:.4f} (charm)")
        self.log(f"    ε_b = {eps_b:.4f} (bottom)")
        self.log(f"")

        table = []  # (name, det, sum_mq, n_quarks, m_obs, is_vector)

        # Pseudoscalar mesons (J=0, different spin slots)
        for name, e1, e2, mq_sum, m_obs in [
            ('π',  eps_u, eps_d, m_u+m_d, 137.3),
            ('K',  eps_u, eps_s, m_u+m_s, 495.6),
            ('D',  eps_u, eps_c, m_u+m_c, 1869.7),
            ('B',  eps_u, eps_b, m_u+m_b, 5279.3),
            ('D_s', eps_s, eps_c, m_s+m_c, 1968.3),
            ('B_s', eps_s, eps_b, m_s+m_b, 5366.9),
            ('η_c', eps_c, eps_c, 2*m_c, 2983.9),
            ('η_b', eps_b, eps_b, 2*m_b, 9399.0),
        ]:
            det, g12, _ = make_meson(e1, e2, same_spin=False)
            table.append((name, det, mq_sum, 2, m_obs, False))

        # η (isotropic)
        eps_eta = (eps_u + eps_d + eps_s) / 3
        det_eta, _, _ = make_eta(eps_eta)
        table.append(('η', det_eta, m_u+m_d+m_s, 2, 547.9, False))

        # Vector mesons (J=1, same spin slot)
        for name, e1, e2, mq_sum, m_obs in [
            ('ρ',  eps_u, eps_d, m_u+m_d, 775.3),
            ('K*', eps_u, eps_s, m_u+m_s, 891.7),
            ('φ',  eps_s, eps_s, 2*m_s, 1019.5),
            ('J/ψ', eps_c, eps_c, 2*m_c, 3096.9),
            ('Υ',  eps_b, eps_b, 2*m_b, 9460.3),
        ]:
            det, g12, _ = make_meson(e1, e2, same_spin=True)
            table.append((name, det, mq_sum, 2, m_obs, True))

        # Baryons
        for name, eps_list, mq_sum, m_obs in [
            ('p',  [1.0, 1.0, 1.0], m_u+m_u+m_d, 938.3),
            ('Σ',  [1.0, 1.0, eps_s], m_u+m_u+m_s, 1189.4),
            ('Ξ',  [1.0, eps_s, eps_s], m_u+m_s+m_s, 1314.9),
            ('Ω',  [eps_s, eps_s, eps_s], 3*m_s, 1672.5),
        ]:
            det, _ = make_baryon_3q(eps_list)
            table.append((name, det, mq_sum, 3, m_obs, None))

        # Print table
        self.log(f"  {'Name':>6s}  {'det(G)':>8s}  {'Σm_q':>8s}  "
                  f"{'m_obs':>8s}  {'type':>6s}")
        for name, det, mq, nq, m_obs, is_v in table:
            t = 'V' if is_v else ('PS' if is_v is False else 'B')
            self.log(f"  {name:>6s}  {det:8.4f}  {mq:8.1f}  "
                      f"{m_obs:8.1f}  {t:>6s}")

        return table

    def unified_formula(self, table):
        """Try: m² = n_eff × Σm_q × Λ × det + Λ² × (1-det)

        This interpolates between GMOR (det=1) and Λ (det=0).
        For baryons (3 quarks): m = N_S × Λ × P(α, f) + corrections.
        """
        self.log(f"  Formula A: m² = n_eff × Σm_q × Λ × det + Λ² × (1-det)")
        self.log(f"")

        self.log(f"  {'Name':>6s}  {'m_pred':>8s}  {'m_obs':>8s}  {'err':>8s}")
        total_err2 = 0; n = 0
        for name, det, mq, nq, m_obs, is_v in table:
            if nq == 2:  # mesons
                m_sq = n_eff * mq * Lambda * det + Lambda**2 * (1 - det)
                if is_v:  # vector: add spin splitting
                    m_sq += (N_T * Lambda)**2 * det
                m_pred = np.sqrt(max(m_sq, 0))
            else:  # baryons
                m_pred = N_S * Lambda * (1 + alpha * N_S/D) + mq * det
                # Skip for now, focus on mesons
                continue

            err = (m_pred - m_obs) / m_obs * 100
            total_err2 += err**2; n += 1
            flag = '★' if abs(err) < 5 else ''
            self.log(f"  {name:>6s}  {m_pred:8.1f}  {m_obs:8.1f}  "
                      f"{err:+7.1f}% {flag}")

        rms = np.sqrt(total_err2 / n) if n > 0 else 0
        self.log(f"\n  Meson RMS: {rms:.1f}%")

    def best_formula(self, table):
        """Scan formula variants to find the best fit.

        The key variables: det(G), Σm_q, Λ, n_eff, N_S, N_T, d.
        Try systematic combinations.
        """
        self.log(f"  Scanning formula variants...")
        self.log(f"")

        # Extract meson data only
        mesons = [(name, det, mq, m_obs, is_v)
                  for name, det, mq, nq, m_obs, is_v in table
                  if nq == 2 and is_v is not None]

        best_rms = 999
        best_formula = ""

        # Formula family: m² = A × Σm_q × Λ × f(det) + B × Λ² × g(det)
        # With spin: + C × Λ² × h(det) for vectors

        formulas = {
            'GMOR pure':
                lambda mq, det, v: n_eff*mq*Lambda,
            'GMOR×det + Λ²(1-det)':
                lambda mq, det, v: n_eff*mq*Lambda*det + Lambda**2*(1-det),
            'GMOR + Λ²(1-det)':
                lambda mq, det, v: n_eff*mq*Lambda + Lambda**2*(1-det),
            'GMOR×√det + Λ²(1-√det)':
                lambda mq, det, v: n_eff*mq*Lambda*np.sqrt(det) + Lambda**2*(1-np.sqrt(det)),
            '(GMOR + Λ²)×det + Λ²':
                lambda mq, det, v: (n_eff*mq*Lambda + Lambda**2)*det + Lambda**2*(1-det),
            'GMOR×det + Λ²/det':
                lambda mq, det, v: n_eff*mq*Lambda*det + Lambda**2*(1-det) if det > 0.01 else Lambda**2,
        }

        # Spin splitting variants
        spin_add = {
            'N_T²Λ²':     lambda det: (N_T*Lambda)**2,
            'N_T²Λ²×det': lambda det: (N_T*Lambda)**2 * det,
            'N_T²Λ²×√det': lambda det: (N_T*Lambda)**2 * np.sqrt(det),
        }

        for f_name, f_func in formulas.items():
            for s_name, s_func in spin_add.items():
                total_err2 = 0; n = 0
                for name, det, mq, m_obs, is_v in mesons:
                    m_sq = f_func(mq, det, is_v)
                    if is_v:
                        m_sq += s_func(det)
                    m_pred = np.sqrt(max(m_sq, 0))
                    err = (m_pred - m_obs) / m_obs * 100
                    total_err2 += err**2; n += 1
                rms = np.sqrt(total_err2 / n)
                if rms < best_rms:
                    best_rms = rms
                    best_formula = f"{f_name} + {s_name}"

        self.log(f"  Best: '{best_formula}' → RMS = {best_rms:.1f}%")
        self.log(f"")

        # Show best formula results
        f_name_best = best_formula.split(' + ')[0]
        s_name_best = best_formula.split(' + ')[1]
        f_func = formulas[f_name_best]
        s_func = spin_add[s_name_best]

        self.log(f"  {'Name':>6s}  {'det':>6s}  {'m_pred':>8s}  "
                  f"{'m_obs':>8s}  {'err':>8s}")
        for name, det, mq, m_obs, is_v in mesons:
            m_sq = f_func(mq, det, is_v)
            if is_v:
                m_sq += s_func(det)
            m_pred = np.sqrt(max(m_sq, 0))
            err = (m_pred - m_obs) / m_obs * 100
            flag = '★' if abs(err) < 5 else ''
            self.log(f"  {name:>6s}  {det:6.4f}  {m_pred:8.1f}  "
                      f"{m_obs:8.1f}  {err:+7.1f}% {flag}")

        self.check(f"Best RMS < 15%", best_rms < 15)


if __name__ == "__main__":
    HAD005().execute()
