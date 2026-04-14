"""
EXP_060: 절대 질량 12개 + Ξ 보정
Joint research by Mingu Jeong and Claude (Anthropic)

EXP_046b의 질량 공식에 Ξ 수렴 보정을 적용.
각 질량의 닫힌 전파자 P(x)에 (1 - α·Ξ_mass) 인자를 곱함.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
import numpy as np
from experiment import Experiment

D = 5; N_S = 3; N_T = 2; C_LAT = 2
a     = 6 / (25 * np.pi**2)
ae    = 1 / 137.035999084
PHI   = (1 + np.sqrt(5)) / 2
M_Pl  = 1.220890e19
eps   = a**(N_T/N_S) * (1 + a)

# 범용 Ξ (m_μ/m_e에서 검증)
Xi = ae/(1-a) + a/(D**2-1) + ae**2

# 관측값 (PDG 2024) — (value_GeV, uncertainty_%)
OBS = {
    'v_H':   (246.22,     0.004),
    'm_t':   (172.57,     0.17),
    'm_b':   (4.18,       0.5),
    'm_τ':   (1.77686,    0.007),
    'm_c':   (1.27,       1.6),
    'm_s':   (93.4e-3,    0.9),
    'm_μ':   (105.658e-3, 2e-4),
    'm_u':   (2.16e-3,    12),
    'm_d':   (4.67e-3,    1.5),
    'm_e':   (0.511e-3,   3e-4),
    'm_p':   (0.93827,    1e-5),
    'Δm_np': (1.293e-3,   0.01),
}


class AbsoluteMasses(Experiment):
    ID = "060"
    TITLE = "Absolute Masses + Xi Correction"

    def run(self):
        def P(f):
            x = a * f
            return (1 + 2*x) / (1 + x)

        # ── v_H ──
        v_comb = (D + 1) * M_Pl / D**(D**2)
        x_vH = N_S * a**2
        v_H = v_comb * (1 + 2*x_vH) / (1 + x_vH)

        # ── 3세대 ──
        m_t = (v_H / np.sqrt(C_LAT)) * P(-1/N_S)
        m_b = m_t * a * P(-1/(D+1))
        m_tau = m_b / ((12/5) * P(-(D-1)/D))

        # ── 2세대 ──
        m_c = m_t * eps**2 * P(-1/D)
        m_s = m_b * (eps * PHI * (1+eps))**2 * P(-(D-1)/D)
        m_mu = m_tau * (eps * PHI**2 * (1+eps))**2 * P(-1/D)

        # ── 1세대 ──
        x_conf = -eps
        m_u = m_t * eps**4 / N_T**2 * (1+2*x_conf)/(1+x_conf)
        m_d = m_b * (eps*PHI)**4 * N_S * P(-N_T/(D+1))
        m_e = m_tau * (eps*PHI**2)**4 / N_S**2 * P(+N_T/D)

        # ── QCD ──
        m_p = N_S**2 * (v_comb/np.sqrt(C_LAT)) * a**2 * P(N_S/D)
        S2 = 15 / (2*np.pi**2)
        m_np = (m_d - m_u) * N_S * (D - 1 + S2) / D**2

        pred_base = {
            'v_H': v_H, 'm_t': m_t, 'm_b': m_b, 'm_τ': m_tau,
            'm_c': m_c, 'm_s': m_s, 'm_μ': m_mu,
            'm_u': m_u, 'm_d': m_d, 'm_e': m_e,
            'm_p': m_p, 'Δm_np': m_np,
        }

        # ── Ξ 보정 적용 ──
        # 하전 페르미온: 각 질량에 (1 - α·Ξ) 곱함
        # 양성자/n-p: 별도 처리
        corr = 1 - a * Xi

        pred_xi = {}
        for name, val in pred_base.items():
            if name in ('m_p', 'Δm_np', 'v_H'):
                pred_xi[name] = val  # 이미 정확하거나 별도 구조
            else:
                pred_xi[name] = val * corr

        # n-p: EM 보정
        pred_xi['Δm_np'] = m_np * (1 - Xi)  # EM 직접 보정

        # ── 출력 ──
        def fmt(v):
            av = abs(v)
            if av >= 1:      return f"{v:.3f} GeV"
            elif av >= 1e-3: return f"{v*1e3:.3f} MeV"
            elif av >= 1e-6: return f"{v*1e6:.2f} keV"
            else:            return f"{v*1e9:.4f} eV"

        order = ['v_H','m_t','m_b','m_τ','m_c','m_s','m_μ',
                 'm_u','m_d','m_e','m_p','Δm_np']

        self.log(f"\n  Ξ = {Xi:.6e},  α·Ξ = {a*Xi:.6e}")
        self.log(f"  보정 인자 (1-α·Ξ) = {corr:.8f}")

        self.log(f"\n  {'':>6} {'Base':>14} {'+ Ξ':>14}"
                 f" {'관측':>14} {'Base%':>8} {'Ξ%':>8}")
        self.log(f"  {'-'*68}")

        improved = 0
        total = 0
        for name in order:
            pb = pred_base[name]
            px = pred_xi[name]
            o, unc = OBS[name]
            eb = (pb - o)/o * 100
            ex = (px - o)/o * 100
            better = abs(ex) < abs(eb)
            if better:
                improved += 1
            total += 1
            mark = '↑' if better else ' '
            self.log(f"  {name:<6} {fmt(pb):>14} {fmt(px):>14}"
                     f" {fmt(o):>14} {eb:>+7.2f}% {ex:>+7.2f}% {mark}")

        self.log(f"\n  개선: {improved}/{total} 관측량에서 오차 감소")

        # n-p 상세
        mnp_obs = OBS['Δm_np'][0]
        err_np_b = (m_np - mnp_obs)/mnp_obs * 100
        err_np_x = (pred_xi['Δm_np'] - mnp_obs)/mnp_obs * 100
        self.log(f"\n  Δm_np 상세:")
        self.log(f"    Base: {m_np*1e3:.4f} MeV ({err_np_b:+.2f}%)")
        self.log(f"    +Ξ:  {pred_xi['Δm_np']*1e3:.4f} MeV ({err_np_x:+.2f}%)")
        self.log(f"    관측: {mnp_obs*1e3:.4f} MeV")

        self.check(f"과반수({improved}/{total}) 개선",
                   improved > total // 2)
        self.check("Δm_np Ξ보정 < 1%",
                   abs(err_np_x) < 1)


if __name__ == "__main__":
    AbsoluteMasses().execute()
