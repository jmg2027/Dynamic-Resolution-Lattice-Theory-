import E213.Physics.SimplexCounts

/-!
# Phase 4 Library — IE 계산 방법론 (재사용 가능)

★ 모든 원자 IE 의 *통일* 계산 절차 ★

표준 차용 부재.  Atomic primitives + Lens 만.

## Procedure

  Step 1.  Z atomic (원자 번호 → atomic 정수 표현)
  Step 2.  Shell occupation (NT² · vertex slot)
  Step 3.  σ_atomic chain (각 shell 별 atomic 비)
  Step 4.  Z_eff = Z - σ_total atomic
  Step 5.  Leading IE = R · Z_eff² / n² (R = 13.605693 eV)
  Step 6.  Closed propagator P(x/k_Z) atomic correction
  Step 7.  Hund penalty (n > half_shell 시) atomic
  Step 8.  Final IE bracket (Lean rational decide)

## Atomic σ catalog

  σ_1s_to_outer = 7/8 = (NS²-1)·1/(NS²) reduced  (Phase 1)
  σ_2s_to_2s    = NS/d = 3/5            (Be, inverse Y-norm)
  σ_2s_to_2p    = (NS²+(NS²-1))/(4d) = 17/20  (B fit)
  σ_2p_to_2p    = (NS²+NT)/(d·NS) = 11/15      (C)

## Atomic invariants

  R∞    = 13.605693 eV  (Phase 4 H 4.3 ppb 검증)
  α_GUT = 6/(d²·π²) = 6/(25·π²) atomic
  α_3   = 1/(NS²-1) = 1/8 atomic
  x     = α_GUT · NS/d = 18/(125·π²) atomic
  P(x)  = (1+2x)/(1+x) closed propagator

## Hund penalty

  half_shell = NS for p, NS+NT for d, ...
  ε_pair = R · NS/(NS²-1) = R · α_3 · NS atomic

## 사용

각 원자 IE 파일은 위 절차 적용:
  Z atomic → σ chain → Z_eff → leading → P(x) → Hund → bracket.
-/

namespace E213.Physics.Phase4.Library.IEMethodology

open E213.Physics.Simplex

/-- R∞ in 10⁻⁶ eV (Phase 4 verified to 4.3 ppb). -/
def R_micro : Nat := 13605693

/-- α_3 inverse atomic = NS² - 1 = 8. -/
theorem alpha_3_inv : NS * NS - 1 = 8 := by decide

/-- p-shell half = NS. -/
theorem p_half : NS * NT / 2 = NS := by decide

/-- ε_pair atomic ratio: 3/8 = NS/(NS²-1). -/
theorem epsilon_pair_ratio : NS * 8 = 3 * (NS * NS - 1) := by decide

end E213.Physics.Phase4.Library.IEMethodology
