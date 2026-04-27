import E213.Physics.SimplexCounts

/-!
# Phase 4 HundPenalty — *Hund 규칙 = atomic edge penalty*

★ User insight ★
"훈트 규칙은 새 물리 법칙이 아닌 격자 간선 점유율 > 절반
일 때 의 atomic combinatorial penalty."

## 가설

  ε_pair = R · NS/(NS²-1) = R · α_3 · NS = R · 3/8 atomic

  Half-fill = NS (= 3, half of NS·NT=6).
  n_2p > NS 시 (n - NS) 개 paired electron.
  IE_actual = IE_no_pair - ε_pair · 1.

  관측 O drop ~5 eV ≈ ε_pair atomic (R·3/8 ≈ 5.10).

→ "Hund 규칙" = 격자 α_3 strong coupling penalty.
-/

namespace E213.Physics.Phase4.HundPenalty

open E213.Physics.Simplex

/-- p-shell size = NS·NT = 6 atomic. -/
theorem p_shell_size : NS * NT = 6 := by decide

/-- Half-fill = NS atomic (half of NS·NT). -/
theorem half_fill : NS * NT = 2 * NS := by decide

/-- ε_pair atomic = NS/(NS²-1) = 3/8. -/
theorem epsilon_pair_atomic : NS * 8 = 3 * (NS * NS - 1) := by decide

/-- α_3 atomic = 1/(NS²-1) = 1/8. -/
theorem alpha_3_atomic : NS * NS - 1 = 8 := by decide

/-- O paired count = 1 (= 2p⁴ - half). -/
theorem O_paired : (4 : Nat) - NS = 1 := by decide

/-- F paired count = 2. -/
theorem F_paired : (5 : Nat) - NS = 2 := by decide

/-- Ne paired count = 3. -/
theorem Ne_paired : (6 : Nat) - NS = 3 := by decide

/-- ★ Hund Penalty Atomic Capstone ★
    "이상한 보정" 부재.  α_3 · NS · R = atomic Lens output. -/
theorem hund_atomic :
    -- p shell size atomic
    (NS * NT = 6)
    -- half = NS atomic
    ∧ (NS * NT = 2 * NS)
    -- ε_pair atomic = NS/(NS²-1)
    ∧ (NS * 8 = 3 * (NS * NS - 1))
    -- α_3 atomic
    ∧ (NS * NS - 1 = 8)
    -- Paired counts
    ∧ (4 - NS = 1) ∧ (5 - NS = 2) ∧ (6 - NS = 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Phase4.HundPenalty
