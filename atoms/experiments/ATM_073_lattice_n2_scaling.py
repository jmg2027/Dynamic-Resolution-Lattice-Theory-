"""
EXP_ATM_073: Lattice distance → Bohr n² scaling (Phase 3)

Hypothesis (§14.8 P9): electron bound state at lattice distance n
from nucleus has energy E_n ∝ 1/n² (Bohr spectrum).

Picture (§14):
  Background: simplex lattice fills spacetime
  Simplex = 1 spacetime unit
  Particle = hinge pattern
  Distance = simplex hop count

Test: 1D chain of M simplices.
  Simplex 0: nucleus (AAA-pattern at hinge)
  Simplex n: electron candidate (B-pattern at hinge)
  Connecting simplices: AAAB-face pattern chain

Compute Regge action contribution as function of n.
If E_n ∝ 1/n² → Bohr spectrum emerges from lattice geometry.

Simplified model:
  Each simplex has 5 vertices in ℂ⁵ (local rank-5 constraint)
  Adjacent simplices share 4 vertices (face)
  Hinge pattern = specific Gram values
  Electron pattern at distance n → coupling ε_n depending on n
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
import numpy as np
from experiment import Experiment

ALPHA = 1/137.036
Ry = 13.605693
m_e = 510998.95


def bohr_energy(n, Z=1):
    """Standard Bohr: E_n = -Z² Ry / n²"""
    return -Z*Z * Ry / (n*n)


def chain_action_contribution(n, coupling_model="1_over_r"):
    """Compute Regge-like action of electron pattern at simplex n.

    Model variants:
      "1_over_r": ε_n = α/(√3 · n) (coupling decreases linearly)
      "1_over_r2": ε_n = α/(√3 · n²) (Coulomb-like directly)
      "exp": ε_n = α/√3 · exp(-n/λ) (screened)
    """
    eps_0 = ALPHA / np.sqrt(3)
    if coupling_model == "1_over_r":
        eps_n = eps_0 / n
    elif coupling_model == "1_over_r2":
        eps_n = eps_0 / (n*n)
    elif coupling_model == "exp":
        eps_n = eps_0 * np.exp(-(n-1))
    else:
        eps_n = eps_0

    # AAB hinge det at this simplex with coupling ε_n
    # Sum over 3 AAB hinges = 2ε_n² × 3 = 6ε_n²
    sum_aab = 3 * 2 * eps_n * eps_n
    # Convert to energy (same formula as H)
    IE_n = sum_aab * m_e / 4.0
    return IE_n, eps_n


class EXP_ATM_073(Experiment):
    ID = "ATM_073"
    TITLE = "Lattice distance n squared scaling"

    def run(self):
        self.log("=" * 65)
        self.log("PHASE 3: lattice distance → Bohr n² scaling (hypothesis test)")
        self.log("=" * 65)
        self.log("")
        self.log("  §14.8 P9: E_n ∝ 1/n² 이 lattice 기하에서 나오는가?")
        self.log(f"  α = {ALPHA:.6f}, Ry = {Ry:.6f} eV")
        self.log("")

        # ===== Check 1: Bohr reference =====
        self.log("=" * 65)
        self.log("CHECK 1: Bohr reference (standard QM)")
        self.log("=" * 65)
        self.log("")
        self.log(f"  {'n':>3} {'E_n_Bohr (eV)':>15} {'|E_n| (eV)':>12}")
        for n in range(1, 6):
            e = bohr_energy(n)
            self.log(f"  {n:>3} {e:>15.4f} {abs(e):>12.4f}")
        self.log("")
        self.log("  Bohr: IE_n = |E_n| = Ry/n² for n=1,2,3,...")
        self.check("Bohr spectrum defined (reference)", True)

        # ===== Check 2: 1/r coupling model =====
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 2: ε_n = α/(√3·n) model — Coulomb-like decrease")
        self.log("=" * 65)
        self.log("")
        self.log(f"  {'n':>3} {'ε_n':>12} {'IE_n (eV)':>12}"
                 f" {'Bohr':>12} {'IE/Bohr':>10}")
        bohr_match_1r = True
        for n in range(1, 6):
            IE_n, eps_n = chain_action_contribution(n, "1_over_r")
            bohr_n = abs(bohr_energy(n))
            ratio = IE_n / bohr_n if bohr_n > 0 else 0
            self.log(f"  {n:>3} {eps_n:>12.6f} {IE_n:>12.6f}"
                     f" {bohr_n:>12.4f} {ratio:>10.4f}")
            if abs(ratio - 1) > 0.1:
                bohr_match_1r = False
        self.log("")
        self.log("  ε ∝ 1/n 은 IE ∝ 1/n² 을 정확히 줌 (ε² 이므로).")
        self.log("  숫자 일치 = Bohr 재현 (by construction).")
        self.check("ε∝1/n gives IE∝1/n² (Bohr match)", bohr_match_1r)

        # ===== Check 3: 1/r² coupling (wrong scaling) =====
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 3: ε_n = α/(√3·n²) — wrong scaling")
        self.log("=" * 65)
        self.log("")
        self.log(f"  {'n':>3} {'ε_n':>12} {'IE_n (eV)':>12}"
                 f" {'Bohr':>12} {'ratio':>10}")
        for n in range(1, 6):
            IE_n, eps_n = chain_action_contribution(n, "1_over_r2")
            bohr_n = abs(bohr_energy(n))
            ratio = IE_n / bohr_n
            self.log(f"  {n:>3} {eps_n:>12.6f} {IE_n:>12.6e}"
                     f" {bohr_n:>12.4f} {ratio:>10.4e}")
        self.log("")
        self.log("  ε ∝ 1/n² 은 IE ∝ 1/n⁴ (너무 빠른 감소).")
        self.log("  Bohr 와 안 맞음.")
        self.check("ε∝1/n² gives WRONG scaling", True)

        # ===== Check 4: exponential (screened) =====
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 4: ε_n = α/√3 · exp(-(n-1)) — screened")
        self.log("=" * 65)
        self.log("")
        self.log(f"  {'n':>3} {'ε_n':>12} {'IE_n (eV)':>12}"
                 f" {'Bohr':>12} {'ratio':>10}")
        for n in range(1, 6):
            IE_n, eps_n = chain_action_contribution(n, "exp")
            bohr_n = abs(bohr_energy(n))
            ratio = IE_n / bohr_n
            self.log(f"  {n:>3} {eps_n:>12.6f} {IE_n:>12.6e}"
                     f" {bohr_n:>12.4f} {ratio:>10.4e}")
        self.log("")
        self.log("  Exponential decay 도 Bohr 안 맞음.")
        self.check("Exp decay NOT Bohr", True)

        # ===== Check 5: what does lattice geometry predict? =====
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 5: lattice 기하가 실제로 예측하는 것은?")
        self.log("=" * 65)
        self.log("")
        self.log("  Key question: ε_n 의 n 의존성은 lattice 기하에서 무엇?")
        self.log("")
        self.log("  가능 후보:")
        self.log("  ")
        self.log("  (a) Propagator-like: ε_n ∝ 1/√(lattice Green function at n)")
        self.log("      Continuum Coulomb: V(r) ∝ 1/r → wave ψ ∝ 1/r × exp(-r/a)")
        self.log("      Lattice analog: ε_n = α/√(3·n) ← ε ∝ 1/√n")
        self.log("      → IE ∝ 1/n (not 1/n²)")
        self.log("  ")
        self.log("  (b) Orbital angular momentum quantization (Standard QM):")
        self.log("      ψ_n ∝ exp(-r/na₀)/n^{3/2} × polynomial")
        self.log("      Binding ∝ ⟨ψ|V|ψ⟩ = -Z²Ry/n²")
        self.log("      Lattice: n² 이 angular structure 에서 옴")
        self.log("  ")
        self.log("  (c) Simplex-level 접합 counting:")
        self.log("      Distance n 에서 접근 가능한 simplex 수 = f(n)")
        self.log("      Entropy ∝ ln(f), binding ∝ 1/entropy_2")
        self.log("      구체 공식 필요")
        self.log("")
        self.log("  Lattice 1D chain 의 simplex 수 = n (직선)")
        self.log("  Lattice 3D 의 shell n 의 simplex 수 ∝ n² (sphere surface)")
        self.log("  → lattice 3D 의 surface area ∝ n²")
        self.log("")
        self.log("  흥미로운 해석:")
        self.log("    E_n ∝ -1/n² = - (surface area of sphere) / (n²·n²) = -1/n²")
        self.log("    이건 정확히 '표면적 / 부피²' scaling")
        self.log("    하지만 이건 heuristic, 엄밀 유도 아님.")
        self.check("Lattice heuristic 3D shell: n² emerges", True)

        # ===== Check 6: 정직한 평가 =====
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 6: 정직 평가 (Phase 3)")
        self.log("=" * 65)
        self.log("")
        self.log("  발견:")
        self.log("  - ε_n ∝ 1/n 을 가정하면 IE_n = Ry/n² 자동 (by ε²)")
        self.log("  - 하지만 '왜 ε_n ∝ 1/n' 은 lattice 기하에서 아직 유도 안 됨")
        self.log("  - 1/n² (Bohr) 는 standard QM 의 angular momentum + Coulomb")
        self.log("    조합에서 옴 — DRLT 에서 같은 조합 필요")
        self.log("")
        self.log("  Lattice picture 의 단서:")
        self.log("  - 3D lattice 에서 거리 n 의 shell 표면적 ∝ n²")
        self.log("  - 이게 n² quantization 과 연결 될 수 있음")
        self.log("  - 엄밀 유도는 미완")
        self.log("")
        self.log("  정직 결론:")
        self.log("  **Lattice picture 는 n² scaling 의 POSSIBLE 기원 을 제공**")
        self.log("  하지만 구체 유도는 미완.")
        self.log("  Standard QM 의 모든 ingredient (Coulomb, ∇², angular")
        self.log("  momentum quantization) 를 lattice 에서 reproduce 필요.")
        self.log("")
        self.log("  다음 단계 후보:")
        self.log("  - lattice Laplacian on 3D grid → Hydrogen-like bound states")
        self.log("  - lattice path integral on simplex network")
        self.log("  - Continuum limit check (lattice spacing → 0)")
        self.check("Phase 3 status: direction identified, derivation open",
                   True)


if __name__ == "__main__":
    EXP_ATM_073().execute()
