"""
EXP_054: 중성미자 질량비 — PMNS 결합 seesaw
Joint research by Mingu Jeong and Claude (Anthropic)

미해결 문제 2:
  현재: 단순 seesaw m_ν=m_l²/M_R → m_ν₃/m_ν₂ = (m_τ/m_μ)² = 283
  관측: √(Δm²₃₂/Δm²₂₁) ≈ 5.7
  문제: 50배 과대평가

해결 핵심 통찰:
  1. 중성미자 Dirac 질량 ≠ 하전 렙톤 질량
     하전 렙톤: SSS 구속 + generation hop → 강한 계층
     중성미자: STT 민주적 채널 → 약한 계층
  2. m_D ∝ diag(√det_B) = diag(1, 1/√2, 1/√2)
  3. M_R = M_R0 × T (B-pair 전이 행렬, 비대각)
  4. m_ν = (m_D0²/M_R0) × D × T⁻¹ × D
     질량 비율은 T⁻¹ 고유값비로 결정!
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
import numpy as np
from experiment import Experiment

# 상수
D     = 5
N_S   = 3
N_T   = 2
ALPHA = 6 / (25 * np.pi**2)
M_PL  = 1.220890e19  # GeV

# 관측값
DM21_SQ = 7.53e-5     # eV²
DM32_SQ = 2.453e-3    # eV²
M_E   = 0.51099895e-3 # GeV
M_MU  = 105.6583755e-3
M_TAU = 1.77686


class NeutrinoRatio(Experiment):
    ID = "054"
    TITLE = "Neutrino Mass Ratio"

    def run(self):
        r32_obs = np.sqrt(DM32_SQ / DM21_SQ)
        r32_simple = (M_TAU / M_MU)**2
        M_R0 = (D + 1) * M_PL / D**12

        # ── Phase 1: 문제 확인 ──
        self.log("\n  Phase 1: 단순 seesaw 문제")
        self.log(f"  단순 seesaw: m_ν₃/m_ν₂ = (m_τ/m_μ)² = {r32_simple:.1f}")
        self.log(f"  관측: √(Δm²₃₂/Δm²₂₁) = {r32_obs:.2f}")
        self.log(f"  과대: {r32_simple/r32_obs:.0f}배")

        # ── Phase 2: B-pair 전이 행렬 T ──
        self.log("\n  Phase 2: B-pair 전이 행렬 T")
        # B₃=(B₁+B₂)/√2, ⟨B₁|B₂⟩=0
        # gen e=(B₁,B₂), gen μ=(B₁,B₃), gen τ=(B₂,B₃)
        s = 1 / np.sqrt(2)
        T = np.array([
            [1.0,  s,    s  ],  # e-e, e-μ, e-τ
            [s,    1.0,  0.5],  # μ-e, μ-μ, μ-τ
            [s,    0.5,  1.0],  # τ-e, τ-μ, τ-τ
        ])
        self.log(f"  T[e,μ] = 1/√2 (B₁ 공유)")
        self.log(f"  T[e,τ] = 1/√2 (B₂ 공유)")
        self.log(f"  T[μ,τ] = 1/2  (B₃ 공유, B₁⊥B₂)")
        for i, n in enumerate(['e', 'μ', 'τ']):
            row = '  '.join(f'{T[i,j]:.4f}' for j in range(3))
            self.log(f"    T[{n}] = [{row}]")

        T_evals = np.sort(np.linalg.eigvalsh(T))
        self.log(f"\n  T 고유값: [{', '.join(f'{e:.6f}' for e in T_evals)}]")

        # ── Phase 3: DRLT seesaw ──
        self.log("\n  Phase 3: DRLT seesaw = D × T⁻¹ × D")
        # D = diag(√det_B): det_B = 1-|⟨B_i|B_j⟩|²
        det_B = np.array([1.0, 0.5, 0.5])
        D_w = np.diag(np.sqrt(det_B))
        self.log(f"  D = diag({np.sqrt(det_B[0]):.4f}, "
                 f"{np.sqrt(det_B[1]):.4f}, {np.sqrt(det_B[2]):.4f})")

        T_inv = np.linalg.inv(T)
        M_eff = D_w @ T_inv @ D_w

        self.log(f"\n  M_ν_eff = D × T⁻¹ × D:")
        for i in range(3):
            row = '  '.join(f'{M_eff[i,j]:>8.5f}' for j in range(3))
            self.log(f"    [{row}]")

        evals = np.sort(np.abs(np.linalg.eigvalsh(M_eff)))
        self.log(f"\n  고유값: [{', '.join(f'{e:.6f}' for e in evals)}]")

        r32_eff = evals[2] / evals[1] if evals[1] > 1e-15 else float('inf')
        self.log(f"  ★ m₃/m₂ = {r32_eff:.4f}  (관측 {r32_obs:.2f})")

        # ── Phase 4: 절대 scale ──
        self.log("\n  Phase 4: 절대 scale")
        v_H = 246.0
        kappa = 2 * ALPHA / 3  # STT coupling
        m_D0 = v_H * np.sqrt(2 * kappa / N_S)
        m_nu0 = m_D0**2 / M_R0  # GeV
        self.log(f"  κ_STT = 2α/3 = {kappa:.6f}")
        self.log(f"  m_D0 = v_H√(2κ/n_S) = {m_D0:.4f} GeV")
        self.log(f"  m_ν0 = m_D0²/M_R0 = {m_nu0*1e9:.6f} eV")

        m_phys = evals * m_nu0 * 1e9  # eV
        self.log(f"\n  중성미자 질량:")
        for i in range(3):
            self.log(f"    m_ν{i+1} = {m_phys[i]*1e3:.4f} meV")

        dm21 = m_phys[1]**2 - m_phys[0]**2
        dm32 = m_phys[2]**2 - m_phys[1]**2
        r32 = np.sqrt(abs(dm32/dm21)) if dm21 > 0 else float('inf')
        self.log(f"\n  Δm²₂₁ = {dm21:.3e} eV²  (관측 {DM21_SQ:.2e})")
        self.log(f"  Δm²₃₂ = {dm32:.3e} eV²  (관측 {DM32_SQ:.2e})")
        self.log(f"  √(Δm²₃₂/Δm²₂₁) = {r32:.2f}")

        # ── Phase 5: 결론 ──
        self.log(f"\n  ┌{'─'*48}┐")
        self.log(f"  │ {'':^10} {'단순':^10} {'DRLT':^10} {'관측':^10} │")
        self.log(f"  ├{'─'*48}┤")
        self.log(f"  │ {'m₃/m₂':^10} {r32_simple:>10.1f}"
                 f" {r32_eff:>10.2f} {r32_obs:>10.2f} │")
        self.log(f"  └{'─'*48}┘")
        self.log(f"  개선: {r32_simple:.0f} → {r32_eff:.1f} (관측 {r32_obs:.1f})")

        self.check(f"질량비 {r32_eff:.1f} << 283 (구조적 개선)",
                   r32_eff < r32_simple / 5)
        self.check(f"질량비 order correct (1~50)",
                   0.5 < r32_eff < 50)


if __name__ == "__main__":
    NeutrinoRatio().execute()
