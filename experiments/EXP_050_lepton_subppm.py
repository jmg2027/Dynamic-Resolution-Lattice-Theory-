"""
EXP_053: 렙톤 질량 sub-ppm → ppb — 3단계 위상 루프 보정
Joint research by Mingu Jeong and Claude (Anthropic)

보정 체인:
  r₀ = n_S/(n_T·α_em)             ← 기저 임피던스
  P  = 1/(1-y), y=α/(n_S+1)       ← Dyson 재합산 (all-order α_GUT)
  δ₁ = -α_em·α/(1-α)              ← 1-loop EM × 1 GUT vertex
  δ₂ = -α²/(d²-1)                 ← SSS indirect coupling (Thm 3.1)
  δ₃ = -α_em²·α                   ← 2-loop EM × 1 GUT vertex

  m_μ/m_e = r₀ × P × (1 + δ₁ + δ₂ + δ₃)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
import numpy as np
from experiment import Experiment

# 상수
D     = 5
N_S   = 3
N_T   = 2
C_LAT = 2
ALPHA     = 6 / (25 * np.pi**2)       # α_GUT
ALPHA_EM  = 1 / 137.035999084         # α_em
PHI       = (1 + np.sqrt(5)) / 2

# 관측값 (PDG 2024)
R_MU_E_OBS   = 206.7682838
R_TAU_MU_OBS = 16.8170
R_TAU_E_OBS  = 3477.23


class LeptonSubppm(Experiment):
    ID = "053"
    TITLE = "Lepton Mass sub-ppm"

    def run(self):
        a   = ALPHA
        a_e = ALPHA_EM
        r0  = N_S / (N_T * a_e)
        y   = a / (N_S + 1)
        P   = 1 / (1 - y)

        self.log(f"\n  기저: r₀ = n_S/(n_T·α_em) = {r0:.6f}")
        self.log(f"  Dyson: P = 1/(1-y) = {P:.10f}")
        self.log(f"  r₀·P = {r0*P:.6f}")

        residual = R_MU_E_OBS / (r0 * P) - 1
        self.log(f"  잔차 δ_exact = {residual:.12f}  ({residual*1e6:+.1f} ppm)")

        # ── 3단계 보정 체인 ──
        d1 = -a_e * a / (1 - a)           # 1-loop EM × GUT
        d2 = -a**2 / (D**2 - 1)           # SSS indirect (Thm 3.1)
        d3 = -a_e**2 * a                  # 2-loop EM × GUT

        self.log(f"\n  ── 보정 체인 ──")
        labels = [
            ("δ₁ = -α_em·α/(1-α)",    d1, "1-loop EM × GUT vertex"),
            ("δ₂ = -α²/(d²-1)",       d2, "SSS indirect coupling"),
            ("δ₃ = -α_em²·α",         d3, "2-loop EM × GUT vertex"),
        ]

        cumul = 0
        for name, di, phys in labels:
            cumul += di
            r_i = r0 * P * (1 + cumul)
            err_i = (r_i - R_MU_E_OBS) / R_MU_E_OBS
            self.log(f"  {name}")
            self.log(f"    = {di:.12e}  ({di*1e6:+.2f} ppm)")
            self.log(f"    누적 오차: {err_i*1e6:+.3f} ppm"
                     f"  = {err_i*1e9:+.1f} ppb    [{phys}]")

        # 최종 결과
        d_total = d1 + d2 + d3
        r_final = r0 * P * (1 + d_total)
        err_final = (r_final - R_MU_E_OBS) / R_MU_E_OBS

        self.log(f"\n  ── 최종 결과 ──")
        self.log(f"  δ_total = δ₁+δ₂+δ₃ = {d_total:.12e}")
        self.log(f"  δ_exact            = {residual:.12e}")
        self.log(f"  차이               = {(d_total-residual):.3e}")
        self.log(f"\n  ★ m_μ/m_e = {r_final:.10f}")
        self.log(f"    관측      = {R_MU_E_OBS:.10f}")
        self.log(f"    오차      = {err_final*1e6:+.4f} ppm = {err_final*1e9:+.1f} ppb")

        # τ/μ
        x = N_T * a
        r_tau = C_LAT**N_S * N_T / (1 - x)
        err_tau = (r_tau - R_TAU_MU_OBS) / R_TAU_MU_OBS
        r_te = r_final * r_tau
        err_te = (r_te - R_TAU_E_OBS) / R_TAU_E_OBS

        self.log(f"\n  m_τ/m_μ = {r_tau:.6f}  ({err_tau*1e6:+.1f} ppm)")
        self.log(f"  m_τ/m_e = {r_te:.4f}  ({err_te*1e6:+.1f} ppm)")

        # 진행 테이블
        err_1st = (r0*(1+y) - R_MU_E_OBS) / R_MU_E_OBS
        err_dys = (r0*P - R_MU_E_OBS) / R_MU_E_OBS
        err_d1  = (r0*P*(1+d1) - R_MU_E_OBS) / R_MU_E_OBS
        err_d12 = (r0*P*(1+d1+d2) - R_MU_E_OBS) / R_MU_E_OBS

        self.log(f"\n  ┌{'─'*44}┐")
        self.log(f"  │ {'단계':^18} {'오차':^10} {'단위':^10} │")
        self.log(f"  ├{'─'*44}┤")
        for nm, e, unit in [
            ('1차 (1+y)',          err_1st*1e6,  'ppm'),
            ('Dyson 1/(1-y)',      err_dys*1e6,  'ppm'),
            ('+δ₁ (EM×GUT)',      err_d1*1e6,   'ppm'),
            ('+δ₂ (SSS α²)',     err_d12*1e6,  'ppm'),
            ('+δ₃ (2-loop EM)',   err_final*1e9, 'ppb'),
        ]:
            self.log(f"  │ {nm:^18} {e:>+9.1f} {unit:^10} │")
        self.log(f"  └{'─'*44}┘")

        self.check("δ₁: 26 ppm 도달",
                   abs(err_d1) < 30e-6)
        self.check("δ₁+δ₂: 2 ppm 도달",
                   abs(err_d12) < 2e-6)
        self.check("δ₁+δ₂+δ₃: sub-100 ppb",
                   abs(err_final) < 100e-9)
        self.check("m_τ/m_μ 오차 < 0.01%",
                   abs(err_tau) < 1e-4)


if __name__ == "__main__":
    LeptonSubppm().execute()
