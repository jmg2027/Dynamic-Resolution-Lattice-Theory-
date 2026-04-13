"""
EXP_050: 렙톤 질량 정밀도 — 0.02% → ppm 수준
Joint research by Mingu Jeong and Claude (Anthropic)

현재: m_μ/m_e = 206.80 (0.017% 오차)
목표: 다중 전파자 합성으로 ppm 수준 도달

핵심 아이디어:
  현재 1차 보정: (1 + α_GUT/(n_S+1))
  2차 보정: self-energy × generation-hop × self-energy
  크기: α_GUT × α_em ≈ 1.8e-4 (0.018%, 현재 오차와 같은 크기!)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
import numpy as np
from experiment import Experiment


class LeptonPrecision(Experiment):
    ID = "050"
    TITLE = "Lepton Precision"

    def run(self):
        d   = 5
        n_S = 3
        n_T = 2
        c   = 2
        alpha     = 6 / (25 * np.pi**2)  # α_GUT
        alpha_em  = 1 / 137.035999
        eps       = alpha**(n_T/n_S) * (1 + alpha)

        # 관측값
        r_mu_e_obs = 206.7682826  # m_μ/m_e (PDG, ppm precision)
        r_tau_mu_obs = 16.8170     # m_τ/m_μ
        r_tau_e_obs = 3477.23      # m_τ/m_e

        # ========================================
        # Phase 1: 현재 공식 (1차 보정)
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 1: 현재 공식 (1차)")
        self.log("="*60)

        # m_μ/m_e = (n_S/(n_T·α_em)) × (1 + α_GUT/(n_S+1))
        r0 = n_S / (n_T * alpha_em)
        corr1 = 1 + alpha / (n_S + 1)
        r_mu_e_1 = r0 * corr1
        err1 = (r_mu_e_1 - r_mu_e_obs) / r_mu_e_obs * 100

        self.log(f"  n_S/(n_T·α) = {r0:.6f}")
        self.log(f"  1차 보정: 1 + α_GUT/(n_S+1) = {corr1:.8f}")
        self.log(f"  m_μ/m_e (1차) = {r_mu_e_1:.4f}")
        self.log(f"  관측: {r_mu_e_obs:.7f}")
        self.log(f"  오차: {err1:+.4f}%  ({err1*1e4:+.1f} ppm)")

        # ========================================
        # Phase 2: 2차 보정 후보 탐색
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 2: 2차 보정 후보")
        self.log("="*60)

        # 잔차: r_obs/r_1차 - 1
        residual = r_mu_e_obs / r_mu_e_1 - 1
        self.log(f"\n  잔차 = r_obs/r_1차 - 1 = {residual:.8f}")
        self.log(f"  크기: {abs(residual):.2e}")

        # 가능한 2차 보정 항들
        candidates = {
            'α_GUT²/2': alpha**2 / 2,
            '-α_GUT×α_em': -alpha * alpha_em,
            '-α_GUT²/(n_S+1)²': -alpha**2 / (n_S+1)**2,
            '-α_GUT/(2d)': -alpha / (2*d),
            '-α_em/(4π)': -alpha_em / (4*np.pi),
            'α_GUT²×n_S': alpha**2 * n_S,
            '-3α_GUT²/d': -3*alpha**2/d,
            '-ε²/d': -eps**2/d,
            '-α_em×α_GUT/n_T': -alpha_em*alpha/n_T,
            '-α_GUT/(d²-1)': -alpha/(d**2-1),
            '-α_em/n_T²': -alpha_em/n_T**2,
        }

        self.log(f"\n  {'후보':>25} {'값':>14} {'잔차-값':>14} {'적합도':>8}")
        self.log(f"  {'-'*64}")
        for name, val in sorted(candidates.items(),
                                 key=lambda kv: abs(kv[1] - residual)):
            fit = abs(val - residual) / abs(residual) * 100
            self.log(f"  {name:>25} {val:>14.8f} {val-residual:>14.8f}"
                     f" {fit:>7.1f}%")

        # ========================================
        # Phase 3: 최적 2차 보정 적용
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 3: 2차 보정 적용")
        self.log("="*60)

        # 물리적으로 자연스러운 조합: self-energy loop
        # 전파자가 1-hop → self-energy → 복귀하면
        # 추가 위상 α_GUT × (무언가)

        # 시도 1: α_GUT²/(n_S+1)² (2차 면 통과 보정)
        corr2a = 1 + alpha/(n_S+1) + alpha**2/(n_S+1)**2
        r_2a = r0 * corr2a
        err_2a = (r_2a - r_mu_e_obs) / r_mu_e_obs * 100

        # 시도 2: 등비급수 합 = (n_S+1)/((n_S+1)-α_GUT)
        # 닫힌 전파자 아이디어: (1+2y)/(1+y) where y = α/(n_S+1)
        y = alpha / (n_S + 1)
        corr2b = (1 + 2*y) / (1 + y)
        r_2b = r0 * corr2b
        err_2b = (r_2b - r_mu_e_obs) / r_mu_e_obs * 100

        # 시도 3: 닫힌 전파자 + self-energy 교차항
        # m_μ/m_e = (n_S/(n_T·α_em)) × P(1/(n_S+1)) × (1 + δ₂)
        # where δ₂ = 교차항
        corr2c = corr2b * (1 - alpha_em * alpha / n_T)
        r_2c = r0 * corr2c
        err_2c = (r_2c - r_mu_e_obs) / r_mu_e_obs * 100

        # 시도 4: EXP_049 발견 적용 — dressed coupling
        # ε for lepton = α/(1+α) in hop correction
        y_dressed = (alpha/(n_S+1)) / (1 + alpha/(n_S+1))
        corr2d = (1 + 2*y_dressed) / (1 + y_dressed)
        r_2d = r0 * corr2d
        err_2d = (r_2d - r_mu_e_obs) / r_mu_e_obs * 100

        # 시도 5: 역공학 — 관측값을 정확히 맞추는 보정
        # r_obs = r0 × corr_exact → corr_exact = r_obs/r0
        corr_exact = r_mu_e_obs / r0
        self.log(f"\n  정확한 보정 = r_obs/r0 = {corr_exact:.10f}")
        self.log(f"  1 + α/(n_S+1)         = {corr1:.10f}")
        self.log(f"  차이                    = {corr_exact-corr1:.10f}")

        self.log(f"\n  {'보정 방식':>35} {'비율':>12} {'오차(%)':>10} {'ppm':>8}")
        self.log(f"  {'-'*68}")
        for name, r, err in [
            ('1차: 1+α/(n_S+1)', r_mu_e_1, err1),
            ('2a: 1+α/(n_S+1)+α²/(n_S+1)²', r_2a, err_2a),
            ('2b: P(1/(n_S+1)) 닫힌 전파자', r_2b, err_2b),
            ('2c: P × (1-α_em·α/n_T)', r_2c, err_2c),
            ('2d: P(dressed 1/(n_S+1))', r_2d, err_2d),
        ]:
            self.log(f"  {name:>35} {r:>12.4f} {err:>+9.4f}% {err*1e4:>+7.0f}")

        # ========================================
        # Phase 4: m_τ/m_μ 정밀도
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 4: m_τ/m_μ 정밀도")
        self.log("="*60)

        x_hop = n_T * alpha
        r_tau_mu_1 = c**n_S * n_T * (1 + x_hop + x_hop**2)
        err_tm1 = (r_tau_mu_1 - r_tau_mu_obs)/r_tau_mu_obs * 100

        # 닫힌 전파자 적용: (1+2x_hop)/(1+x_hop) 대신 등비급수
        r_tau_mu_p = c**n_S * n_T * (1 + 2*x_hop) / (1 + x_hop)
        err_tmp = (r_tau_mu_p - r_tau_mu_obs)/r_tau_mu_obs * 100

        # 3차까지: 1+x+x²+x³
        r_tau_mu_3 = c**n_S * n_T * (1 + x_hop + x_hop**2 + x_hop**3)
        err_tm3 = (r_tau_mu_3 - r_tau_mu_obs)/r_tau_mu_obs * 100

        self.log(f"\n  x_hop = n_T·α_GUT = {x_hop:.8f}")
        self.log(f"  {'방식':>25} {'비율':>12} {'오차(%)':>10}")
        self.log(f"  {'-'*50}")
        for name, r, err in [
            ('2차: 1+x+x²', r_tau_mu_1, err_tm1),
            ('3차: 1+x+x²+x³', r_tau_mu_3, err_tm3),
            ('닫힌: (1+2x)/(1+x)', r_tau_mu_p, err_tmp),
        ]:
            self.log(f"  {name:>25} {r:>12.4f} {err:>+9.4f}%")

        # ========================================
        # Phase 5: 종합 + Checks
        # ========================================
        self.log("\n" + "="*60)
        self.log("  종합")
        self.log("="*60)

        best_r = r_2b  # 닫힌 전파자 방식
        best_err = err_2b

        self.log(f"""
  m_μ/m_e 최선:
    공식: (n_S/(n_T·α_em)) × (1+2y)/(1+y), y = α_GUT/(n_S+1)
    값: {best_r:.6f}
    관측: {r_mu_e_obs:.7f}
    오차: {best_err:+.4f}% ({best_err*1e4:+.1f} ppm)

  m_τ/m_μ 최선:
    공식: c^n_S × n_T × (1+2x)/(1+x), x = n_T·α_GUT
    값: {r_tau_mu_p:.6f}
    관측: {r_tau_mu_obs:.4f}
    오차: {err_tmp:+.4f}%

  m_τ/m_e = {best_r * r_tau_mu_p:.2f}
    관측: {r_tau_e_obs:.2f}
    오차: {(best_r*r_tau_mu_p - r_tau_e_obs)/r_tau_e_obs*100:+.3f}%
""")

        self.check(f"m_μ/m_e (2b): |{best_err:.3f}%| < 0.02%",
                   abs(best_err) < 0.02)
        self.check(f"m_τ/m_μ (1+x+x²): |{err_tm1:.4f}%| < 0.01%",
                   abs(err_tm1) < 0.01)
        self.check(f"m_μ/m_e precision improved vs 1차",
                   abs(best_err) < abs(err1))
        self.check(f"2차 잔차 ≈ -α_GUT×α_em (3.9% fit)",
                   abs((-alpha*alpha_em - residual)/residual) < 0.05)


if __name__ == "__main__":
    LeptonPrecision().execute()
