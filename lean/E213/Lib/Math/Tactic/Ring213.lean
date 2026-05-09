/-!
# Ring213 — ∅-axiom polynomial identity infrastructure (no Mathlib)

Mathlib's `ring` tactic isn't available without imports. For 213-native
polynomial identity proofs, we use:

1. **Recurrence-as-definition pattern**: define seq via the desired
   recurrence; the recurrence then holds by `rfl`.
2. **Pointwise verification**: equality with closed-form formula at
   finite N via `decide`.
3. **Universal recursion**: `rfl` extends to all n by reduction.

For our algebra-tower discovery: linear recurrences on Nat-indexed
Int sequences. More general polynomial identities (involving pow_succ
etc.) need more infrastructure.
-/

namespace E213.Lib.Math.Tactic.Ring213

/-- 2nd-order linear inhomogeneous recurrence over Int. -/
structure Recurrence2 where
  a₀ : Int   -- initial
  a₁ : Int   -- second
  c₁ : Int   -- coeff of n+1 term
  c₂ : Int   -- coeff of n term
  d  : Int   -- inhomogeneous constant

/-- Sequence defined by 2nd-order linear recurrence. -/
def Recurrence2.seq (R : Recurrence2) : Nat → Int
  | 0     => R.a₀
  | 1     => R.a₁
  | n + 2 => R.c₁ * R.seq (n+1) + R.c₂ * R.seq n + R.d

/-- ★ Universal recurrence theorem (∅-axiom by `rfl`). -/
theorem Recurrence2.seq_recurrence (R : Recurrence2) (n : Nat) :
    R.seq (n + 2) = R.c₁ * R.seq (n + 1) + R.c₂ * R.seq n + R.d := rfl

end E213.Lib.Math.Tactic.Ring213

namespace E213.Lib.Math.Tactic.Ring213

/-- Type A residual recurrence as `Recurrence2`. -/
def typeA_residual : Recurrence2 :=
  { a₀ := 43, a₁ := 197, c₁ := 6, c₂ := -8, d := 3 }

/-- ★ Type A recurrence (∅-axiom, ∀ n). -/
theorem typeA_residual_universal (n : Nat) :
    typeA_residual.seq (n + 2)
      = 6 * typeA_residual.seq (n + 1) + (-8) * typeA_residual.seq n + 3 :=
  typeA_residual.seq_recurrence n

/-- ★ Type A residual matches measured (n = 0..4). -/
theorem typeA_residual_measured :
    typeA_residual.seq 0 = 43 ∧
    typeA_residual.seq 1 = 197 ∧
    typeA_residual.seq 2 = 841 ∧
    typeA_residual.seq 3 = 3473 ∧
    typeA_residual.seq 4 = 14113 := by decide

end E213.Lib.Math.Tactic.Ring213
