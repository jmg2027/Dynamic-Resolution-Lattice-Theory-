"""
EXP_061: 중성자-양성자 질량차 정밀화
Joint research by Mingu Jeong and Claude (Anthropic)

현재: Δm = (m_d-m_u) × n_S × (d-1+S₂/S∞) / d² = 1.44 MeV (+11%)
관측: 1.2934 MeV

문제: DRLT의 m_d - m_u = 2.52 MeV vs 물리 m_d - m_u = 2.51 MeV.
공식의 기하 인자가 과대. 인자 분석으로 개선.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
import numpy as np
from experiment import Experiment

D = 5; N_S = 3; N_T = 2; C_LAT = 2
a  = 6 / (25 * np.pi**2)
ae = 1 / 137.035999084
PHI = (1 + np.sqrt(5)) / 2
M_Pl = 1.220890e19
eps = a**(N_T/N_S) * (1 + a)

OBS_NP = 1.2934e-3  # GeV


class NPMassDiff(Experiment):
    ID = "061"
    TITLE = "Neutron-Proton Mass Difference"

    def run(self):
        def P(f):
            x = a * f
            return (1 + 2*x) / (1 + x)

        # DRLT 쿼크 질량
        v_comb = (D+1)*M_Pl / D**(D**2)
        x_vH = N_S * a**2
        v_H = v_comb * (1+2*x_vH)/(1+x_vH)
        m_t = (v_H/np.sqrt(C_LAT)) * P(-1/N_S)
        m_b = m_t * a * P(-1/(D+1))

        m_u = m_t * eps**4/N_T**2 * (1+2*(-eps))/(1+(-eps))
        m_d = m_b * (eps*PHI)**4 * N_S * P(-N_T/(D+1))

        dm_quarks = m_d - m_u
        S2 = 15 / (2*np.pi**2)

        self.log(f"\n  Phase 1: DRLT 쿼크 질량")
        self.log(f"  m_u = {m_u*1e3:.4f} MeV  (관측 ~2.16)")
        self.log(f"  m_d = {m_d*1e3:.4f} MeV  (관측 ~4.67)")
        self.log(f"  m_d - m_u = {dm_quarks*1e3:.4f} MeV")

        # ── Phase 2: 기존 공식 ──
        self.log(f"\n  Phase 2: 기존 공식")
        geom = N_S * (D - 1 + S2) / D**2
        self.log(f"  기하 인자 = n_S(d-1+S₂/S∞)/d² = {geom:.6f}")
        self.log(f"  S₂/S∞ = 15/(2π²) = {S2:.6f}")

        dm_base = dm_quarks * geom
        err_base = (dm_base - OBS_NP)/OBS_NP * 100
        self.log(f"  Δm_base = {dm_base*1e3:.4f} MeV  ({err_base:+.2f}%)")

        # ── Phase 3: 기하 인자 분석 ──
        self.log(f"\n  Phase 3: 기하 인자 후보")
        # 현재: n_S(d-1+S₂/S∞)/d² = 0.5712
        # 관측에서 역산: OBS/(m_d-m_u)
        geom_exact = OBS_NP / dm_quarks
        self.log(f"  필요한 기하 인자: {geom_exact:.6f}")
        self.log(f"  현재 기하 인자:   {geom:.6f}")
        self.log(f"  비율: {geom_exact/geom:.4f}")

        # 후보
        cands = {
            'n_S(d-1+S₂)/d² [기존]':        N_S * (D-1+S2) / D**2,
            'n_S(d-1)/d²':                   N_S * (D-1) / D**2,
            'n_S/d² × (d-1+S₂)/(1+α)':     N_S*(D-1+S2) / (D**2*(1+a)),
            '(d-1)/(d²-1)':                  (D-1) / (D**2-1),
            'n_S/(2d)':                       N_S / (2*D),
            'n_S(d-1+S₂)/d²/(1+S₂·α)':    N_S*(D-1+S2) / (D**2*(1+S2*a)),
        }

        self.log(f"\n  {'후보':>36} {'값':>10} {'Δm(MeV)':>10} {'오차':>8}")
        self.log(f"  {'-'*68}")
        for name, val in sorted(cands.items(),
                                 key=lambda kv: abs(kv[1]*dm_quarks*1e3 - OBS_NP*1e3)):
            dm = val * dm_quarks
            err = (dm - OBS_NP)/OBS_NP * 100
            self.log(f"  {name:>36} {val:>10.6f} {dm*1e3:>10.4f} {err:>+7.2f}%")

        # ── Phase 4: 관측 (m_d-m_u) 직접 사용 ──
        self.log(f"\n  Phase 4: PDG 쿼크 질량 직접 사용")
        dm_pdg = (4.67 - 2.16) * 1e-3  # GeV
        dm_pdg_v2 = dm_pdg * geom
        err_pdg = (dm_pdg_v2 - OBS_NP)/OBS_NP * 100
        self.log(f"  (m_d-m_u)_PDG = {dm_pdg*1e3:.2f} MeV")
        self.log(f"  Δm = {dm_pdg_v2*1e3:.4f} MeV  ({err_pdg:+.2f}%)")

        # EM 보정
        Xi = ae/(1-a) + a/(D**2-1) + ae**2
        dm_pdg_xi = dm_pdg * geom * (1 - Xi)
        err_xi = (dm_pdg_xi - OBS_NP)/OBS_NP * 100
        self.log(f"  +Ξ보정: {dm_pdg_xi*1e3:.4f} MeV  ({err_xi:+.2f}%)")

        self.log(f"\n  ┌{'─'*52}┐")
        self.log(f"  │ {'방법':^22} {'Δm(MeV)':^12} {'오차':^12} │")
        self.log(f"  ├{'─'*52}┤")
        for nm, val, err in [
            ('DRLT 쿼크 질량',        dm_base*1e3,     err_base),
            ('PDG 쿼크 질량',         dm_pdg_v2*1e3,   err_pdg),
            ('PDG + Ξ 보정',         dm_pdg_xi*1e3,   err_xi),
        ]:
            self.log(f"  │ {nm:^22} {val:>11.4f} {err:>+11.2f}% │")
        self.log(f"  │ {'관측':^22} {OBS_NP*1e3:>11.4f} {'':>12} │")
        self.log(f"  └{'─'*52}┘")

        self.log(f"\n  결론: 오차의 주 원인은 기하 인자(11%).")
        self.log(f"  Ξ 보정(0.85%)은 부차적. 기하 인자 개선이 핵심.")

        self.check("PDG 쿼크+기존 기하 < 5%",
                   abs(err_pdg) < 5)
        self.check("PDG 쿼크+Ξ < 5%",
                   abs(err_xi) < 5)


if __name__ == "__main__":
    NPMassDiff().execute()
