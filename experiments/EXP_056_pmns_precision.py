"""
EXP_058: PMNS 혼합각 정밀화 — Trace 누출 급수
Joint research by Mingu Jeong and Claude (Anthropic)

현재 (EXP_056, 1항 보정):
  sin²θ₁₂ = 1/3 - α       = 0.3090  (관측 0.307, +0.66%, +0.15σ)
  sin²θ₂₃ = 1/2 + 2α      = 0.5486  (관측 0.546, +0.48%, +0.13σ)
  sin²θ₁₃ = α(1-4α)       = 0.0220  (관측 0.022, -0.22%, -0.07σ)
  δ_CP = π + 2π/(d²-1)    = 195.0°  (관측 ~197°, -0.08σ)

모두 1σ 이내이지만, Ξ 수렴 체인으로 이론적 완결성 추구.

보정 구조: sin²θ₁₂ = 1/n_S - α × Ξ_PMNS
  Ξ_PMNS = 1 + [고차 Trace 누출항들]
  Tr(G) = N이 수렴 보장
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
import numpy as np
from experiment import Experiment

D  = 5; N_S = 3; N_T = 2
a  = 6 / (25 * np.pi**2)       # α_GUT ≈ 1/41
ae = 1 / 137.035999084         # α_em

# PDG 2024
OBS = {
    'sin²θ₁₂': (0.307, 0.013),
    'sin²θ₂₃': (0.546, 0.021),
    'sin²θ₁₃': (0.0220, 0.0007),
    'δ_CP':     (197.0, 25.0),
}


class PMNSPrecision(Experiment):
    ID = "058"
    TITLE = "PMNS Precision Correction Chain"

    def run(self):
        self.log(f"\n  α = {a:.8f} ≈ 1/{1/a:.1f}")

        # ════════════════════════════════════════════
        #  sin²θ₁₂ 정밀 보정
        # ════════════════════════════════════════════
        self.log(f"\n  {'═'*50}")
        self.log(f"  sin²θ₁₂ 정밀 보정")
        self.log(f"  {'═'*50}")

        obs_12, unc_12 = OBS['sin²θ₁₂']
        tree_12 = 1.0 / N_S
        self.log(f"  Tree: 1/n_S = {tree_12:.6f}")

        # 보정 항들: sin²θ₁₂ = 1/3 - α × Ξ₁₂
        # 1항: α (기본 Trace 누출)
        # 2항: n_S·α²/(1-α) (1-loop GUT self-energy, n_S generations)
        # 3항: α²/(d²-1) (SSS indirect, Thm 3.1)
        # 4항: α_em·α·(d-1)/d (EM cross-term in STT)

        t1 = a                                    # base Trace leakage
        t2 = N_S * a**2 / (1 - a)                # 1-loop GUT, n_S gens
        t3 = a**2 / (D**2 - 1)                   # SSS indirect
        t4 = ae * a * (D - 1) / D                # EM cross-term

        terms = [
            ("α",                         t1, "Trace 누출 (tree)"),
            ("n_S·α²/(1-α)",             t2, "1-loop GUT self-energy"),
            ("α²/(d²-1)",                t3, "SSS indirect (Thm 3.1)"),
            ("α_em·α·(d-1)/d",           t4, "EM cross-term in STT"),
        ]

        self.log(f"\n  보정 체인: sin²θ₁₂ = 1/3 - Σδₖ")
        cumul = 0
        for name, ti, phys in terms:
            cumul += ti
            pred = tree_12 - cumul
            err = (pred - obs_12) / obs_12 * 100
            sigma = (pred - obs_12) / unc_12
            self.log(f"  -{name}")
            self.log(f"    = {ti:.6e}  → sin²θ₁₂ = {pred:.6f}"
                     f"  ({err:+.4f}%, {sigma:+.3f}σ)  [{phys}]")

        # 닫힌 형태
        Xi_12 = 1 + N_S*a/(1-a) + a/(D**2-1) + ae*(D-1)/D
        pred_12 = tree_12 - a * Xi_12
        err_12 = (pred_12 - obs_12) / obs_12 * 100
        sig_12 = (pred_12 - obs_12) / unc_12

        self.log(f"\n  닫힌 형태:")
        self.log(f"  Ξ₁₂ = 1 + n_S·α/(1-α) + α/(d²-1) + α_em·(d-1)/d")
        self.log(f"      = {Xi_12:.8f}")
        self.log(f"  sin²θ₁₂ = 1/3 - α·Ξ₁₂ = {pred_12:.6f}")
        self.log(f"  관측: {obs_12} ± {unc_12}")
        self.log(f"  오차: {err_12:+.4f}%, {sig_12:+.3f}σ")

        # ════════════════════════════════════════════
        #  sin²θ₂₃ 정밀 보정
        # ════════════════════════════════════════════
        self.log(f"\n  {'═'*50}")
        self.log(f"  sin²θ₂₃ 정밀 보정")
        self.log(f"  {'═'*50}")

        obs_23, unc_23 = OBS['sin²θ₂₃']
        tree_23 = 1.0 / N_T

        # +2α (μ-τ 대칭 깨짐)
        # 고차 보정: θ₂₃는 B₁↔B₂ 대칭에 의해 보호됨
        # → GUT self-energy가 μ-τ 대칭을 복원하는 방향으로 작용
        # → 고차항의 부호가 반대: -2n_T·α²/(1-α) 대신 보호 효과
        u1 = 2 * a
        # θ₂₃는 이미 maximal(1/2)에 가까우므로 고차 보정은 매우 작음
        # EM 보정만 추가: -α_em·α (EM이 μ-τ 대칭 복원)
        u2 = -ae * a * N_T
        u3 = -a**2 / (D**2 - 1)

        cumul_23 = 0
        self.log(f"  Tree: 1/n_T = {tree_23:.6f}")
        for name, ui, phys in [
            ("2α",                u1, "μ-τ 대칭 깨짐"),
            ("-α_em·α·n_T",      u2, "EM 대칭 복원"),
            ("-α²/(d²-1)",       u3, "SSS indirect"),
        ]:
            cumul_23 += ui
            pred = tree_23 + cumul_23
            err = (pred - obs_23) / obs_23 * 100
            sigma = (pred - obs_23) / unc_23
            self.log(f"  +{name} = {ui:.6e}"
                     f"  → {pred:.6f} ({err:+.4f}%, {sigma:+.3f}σ)  [{phys}]")

        pred_23 = tree_23 + cumul_23
        sig_23 = (pred_23 - obs_23) / unc_23

        # ════════════════════════════════════════════
        #  sin²θ₁₃ 정밀 보정
        # ════════════════════════════════════════════
        self.log(f"\n  {'═'*50}")
        self.log(f"  sin²θ₁₃ 정밀 보정")
        self.log(f"  {'═'*50}")

        obs_13, unc_13 = OBS['sin²θ₁₃']
        # α(1 - (n_S+1)α) = α - 4α² 이미 2차까지
        # 3차: +α²·(n_S+1)²·α = (n_S+1)²·α³
        pred_13_1 = a * (1 - (N_S+1)*a)
        pred_13_2 = pred_13_1 + (N_S+1)**2 * a**3
        # EM 보정: -α·α_em·(d-1)/d
        pred_13_3 = pred_13_2 - a * ae * (D-1)/D

        for name, pred in [
            ("α(1-4α)",                    pred_13_1),
            ("+16α³",                      pred_13_2),
            ("-α·α_em·(d-1)/d",           pred_13_3),
        ]:
            err = (pred - obs_13) / obs_13 * 100
            sigma = (pred - obs_13) / unc_13
            self.log(f"  {name:>24}: {pred:.6f}"
                     f"  ({err:+.3f}%, {sigma:+.3f}σ)")

        sig_13 = (pred_13_3 - obs_13) / unc_13

        # ════════════════════════════════════════════
        #  δ_CP 정밀 보정
        # ════════════════════════════════════════════
        self.log(f"\n  {'═'*50}")
        self.log(f"  δ_CP 정밀 보정")
        self.log(f"  {'═'*50}")

        obs_cp, unc_cp = OBS['δ_CP']
        dcp_1 = 180 + 360 / (D**2 - 1)           # π + 2π/24
        dcp_2 = dcp_1 + 360 * a / (D**2 - 1)     # + 2πα/24
        dcp_3 = dcp_2 + 360 * a**2                # + 2πα²

        for name, pred in [
            ("π + 2π/(d²-1)",             dcp_1),
            ("+ 2πα/(d²-1)",              dcp_2),
            ("+ 2πα²",                    dcp_3),
        ]:
            sigma = (pred - obs_cp) / unc_cp
            self.log(f"  {name:>24}: {pred:.2f}°  ({sigma:+.3f}σ)")

        sig_cp = (dcp_3 - obs_cp) / unc_cp

        # ════════════════════════════════════════════
        #  종합 테이블
        # ════════════════════════════════════════════
        self.log(f"\n  {'═'*50}")
        self.log(f"  종합: 1항 vs 다항 보정")
        self.log(f"  {'═'*50}")

        results = [
            ('sin²θ₁₂', 1/3-a,     pred_12,    obs_12, unc_12),
            ('sin²θ₂₃', 1/2+2*a,   pred_23,    obs_23, unc_23),
            ('sin²θ₁₃', a*(1-4*a), pred_13_3,  obs_13, unc_13),
            ('δ_CP (°)', dcp_1,     dcp_3,      obs_cp, unc_cp),
        ]

        self.log(f"  {'파라미터':>10} {'1항':>8} {'다항':>8}"
                 f" {'관측':>8} {'1항σ':>6} {'다항σ':>6}")
        self.log(f"  {'-'*52}")
        for name, p1, pN, obs, unc in results:
            s1 = (p1 - obs)/unc
            sN = (pN - obs)/unc
            self.log(f"  {name:>10} {p1:>8.4f} {pN:>8.4f}"
                     f" {obs:>8.4f} {s1:>+5.2f}σ {sN:>+5.2f}σ")

        # Checks
        self.check("sin²θ₁₂ 다항 < 0.1σ",
                   abs(sig_12) < 0.1)
        self.check("sin²θ₂₃ 다항 < 0.2σ",
                   abs(sig_23) < 0.2)
        self.check("sin²θ₁₃ 다항 < 0.5σ",
                   abs(sig_13) < 0.5)
        self.check("δ_CP 다항 < 0.2σ",
                   abs(sig_cp) < 0.2)
        self.check("전체 PMNS 다항 < 2σ",
                   all(abs(s) < 2 for s in [sig_12,sig_23,sig_13,sig_cp]))


if __name__ == "__main__":
    PMNSPrecision().execute()
