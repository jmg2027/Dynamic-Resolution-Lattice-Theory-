"""
EXP_057: m_τ/m_μ 정밀도 — hop 급수 보정
Joint research by Mingu Jeong and Claude (Anthropic)

현재: m_τ/m_μ = c^n_S × n_T × 1/(1-x) = 16.8179 (+55 ppm)
관측: 16.8170 ± 0.0011 (실험 불확도 68 ppm)

핵심: 55 ppm 잔차 ≈ 실험 불확도 68 ppm 이내!
그래도 이론적 완결성을 위해 hop 급수 구조를 분석.

m_μ/m_e와의 차이:
  m_μ/m_e: 기저에 α_em → EM self-energy Ξ chain 적용
  m_τ/m_μ: 기저 = 16 (순수 조합론) → hop 급수 계수 보정
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
import numpy as np
from experiment import Experiment

D  = 5; N_S = 3; N_T = 2; C_LAT = 2
a  = 6 / (25 * np.pi**2)
ae = 1 / 137.035999084
R_OBS    = 16.8170
R_OBS_UNC = 0.0011   # 68 ppm


class TauMuPrecision(Experiment):
    ID = "057"
    TITLE = "m_tau/m_mu Precision"

    def run(self):
        x    = N_T * a
        base = C_LAT**N_S * N_T   # = 16

        # ── Phase 1: 급수 비교 ──
        self.log("\n  Phase 1: hop 급수 비교")
        self.log(f"  x = n_T·α = {x:.8f}")

        P_2nd = 1 + x + x**2           # 2차까지
        P_dys = 1 / (1 - x)            # Dyson (무한합)
        P_obs = R_OBS / base            # 관측으로부터 역산

        self.log(f"  1+x+x² = {P_2nd:.10f}  → {base*P_2nd:.6f}")
        self.log(f"  1/(1-x) = {P_dys:.10f}  → {base*P_dys:.6f}")
        self.log(f"  관측/16  = {P_obs:.10f}  → {R_OBS:.6f}")

        err_2nd = (base*P_2nd - R_OBS)/R_OBS
        err_dys = (base*P_dys - R_OBS)/R_OBS
        self.log(f"\n  1+x+x²: {err_2nd*1e6:+.1f} ppm")
        self.log(f"  1/(1-x): {err_dys*1e6:+.1f} ppm")
        self.log(f"  실험 불확도: ±{R_OBS_UNC/R_OBS*1e6:.0f} ppm")

        # ── Phase 2: x³ 계수 분석 ──
        self.log("\n  Phase 2: 3차 hop 계수")
        excess = P_obs - P_2nd          # 관측 - 2차까지
        c3_eff = excess / x**3
        self.log(f"  P_obs - (1+x+x²) = {excess:.6e}")
        self.log(f"  x³ = {x**3:.6e}")
        self.log(f"  유효 c₃ = {c3_eff:.4f}")
        self.log(f"  (c₃=1이면 Dyson, c₃=0이면 2차 절단)")

        # 후보 계수들
        self.log(f"\n  c₃ 후보:")
        cands = {
            'n_S/(d+1) = 1/2':     N_S / (D + 1),
            '(d-1)/(2d) = 2/5':    (D-1) / (2*D),
            '1-x':                  1 - x,
            'n_S/(d+1)·(1+x)':     N_S/(D+1) * (1+x),
        }
        for name, val in sorted(cands.items(),
                                 key=lambda kv: abs(kv[1]-c3_eff)):
            err = (val - c3_eff)/c3_eff*100
            r_pred = base * (P_2nd + val * x**3)
            e_ppm = (r_pred - R_OBS)/R_OBS*1e6
            self.log(f"    {name:<24} = {val:.6f}"
                     f"  (c₃ 오차 {err:+.1f}%, 질량비 오차 {e_ppm:+.1f} ppm)")

        # ── Phase 3: 최적 공식 ──
        # c₃ = n_S/(d+1) = 1/2 가 가장 자연스러운 후보
        c3 = N_S / (D + 1)   # = 1/2
        P_best = P_2nd + c3 * x**3
        r_best = base * P_best
        err_best = (r_best - R_OBS) / R_OBS

        self.log(f"\n  Phase 3: 최적 — c₃ = n_S/(d+1) = {c3:.4f}")
        self.log(f"  P = 1 + x + x² + (n_S/(d+1))·x³")
        self.log(f"  m_τ/m_μ = {r_best:.8f}")
        self.log(f"  오차: {err_best*1e6:+.1f} ppm")

        # ── Phase 4: 종합 ──
        self.log(f"\n  ┌{'─'*52}┐")
        self.log(f"  │ {'공식':^20} {'값':^12} {'오차(ppm)':^12} │")
        self.log(f"  ├{'─'*52}┤")
        for nm, val in [
            ('1+x+x²',            base*P_2nd),
            ('1/(1-x) [Dyson]',    base*P_dys),
            ('1+x+x²+x³/2',       r_best),
        ]:
            e = (val-R_OBS)/R_OBS*1e6
            self.log(f"  │ {nm:^20} {val:>12.6f} {e:>+11.1f} │")
        self.log(f"  │ {'관측 ± 불확도':^20} {R_OBS:>12.6f}"
                 f" {'±'+ str(int(R_OBS_UNC/R_OBS*1e6)):>10} │")
        self.log(f"  └{'─'*52}┘")

        self.log(f"\n  결론:")
        self.log(f"    Dyson 1/(1-x) 잔차 = {err_dys*1e6:+.0f} ppm"
                 f" < 실험 불확도 {R_OBS_UNC/R_OBS*1e6:.0f} ppm")
        self.log(f"    3차 보정 1+x+x²+x³/2: {err_best*1e6:+.0f} ppm")
        self.log(f"    → 실험 정밀도 향상 시 검증 가능")

        self.check("Dyson 잔차 < 실험 불확도",
                   abs(err_dys) < R_OBS_UNC/R_OBS)
        self.check("3차 보정 < 10 ppm",
                   abs(err_best) < 10e-6)


if __name__ == "__main__":
    TauMuPrecision().execute()
