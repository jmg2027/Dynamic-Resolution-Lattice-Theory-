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


/-- Z[√5]-valued sequence: (a + b·√5) coefficients per index. -/
structure RecurrenceZ5_b where
  b₀ : Int          -- initial √5 coefficient
  ratio : Int       -- multiplicative ratio per step (b_{n+1} = ratio · b_n)

/-- Geometric Z[√5] sequence: b_n = b₀ · ratio^n. -/
def RecurrenceZ5_b.bSeq (R : RecurrenceZ5_b) : Nat → Int
  | 0 => R.b₀
  | n + 1 => R.ratio * R.bSeq n

theorem RecurrenceZ5_b.bSeq_recurrence (R : RecurrenceZ5_b) (n : Nat) :
    R.bSeq (n + 1) = R.ratio * R.bSeq n := rfl

/-- Type C residual b_n (√5 coefficient at L_{n+5}). -/
def typeC_residual_b : RecurrenceZ5_b := { b₀ := 8, ratio := 8 }

theorem typeC_residual_b_measured :
    typeC_residual_b.bSeq 0 = 8 ∧
    typeC_residual_b.bSeq 1 = 64 ∧
    typeC_residual_b.bSeq 2 = 512 ∧
    typeC_residual_b.bSeq 3 = 4096 ∧
    typeC_residual_b.bSeq 4 = 32768 := by decide


/-- 3rd-order linear inhomogeneous recurrence over Int. -/
structure Recurrence3 where
  a₀ : Int
  a₁ : Int
  a₂ : Int
  c₁ : Int  -- coeff of (n+2) term
  c₂ : Int  -- coeff of (n+1) term
  c₃ : Int  -- coeff of n term
  d  : Int  -- constant

def Recurrence3.seq (R : Recurrence3) : Nat → Int
  | 0     => R.a₀
  | 1     => R.a₁
  | 2     => R.a₂
  | n + 3 => R.c₁ * R.seq (n+2) + R.c₂ * R.seq (n+1) + R.c₃ * R.seq n + R.d

/-- ★ Universal 3rd-order recurrence theorem (∅-axiom by `rfl`). -/
theorem Recurrence3.seq_recurrence (R : Recurrence3) (n : Nat) :
    R.seq (n + 3) = R.c₁ * R.seq (n+2) + R.c₂ * R.seq (n+1) + R.c₃ * R.seq n + R.d := rfl

-- UNIVERSAL CD-doubling transient law: all 4 Types share coefficients
-- (14, -56, 64), only constant `d` is base-dependent.
-- Char poly: x³ - 14x² + 56x - 64 = (x-2)(x-4)(x-8) — eigenvalues 2, 4, 8.

/-- Type A (ZI) unreduced residual rat sequence. -/
def typeA_rat_uni : Recurrence3 :=
  { a₀ := 4096,    a₁ := 22016,    a₂ := 100864
  , c₁ := 14, c₂ := -56, c₃ := 64, d := -10752 }

/-- Type C (ZOmega) unreduced residual rat sequence. -/
def typeC_rat_uni : Recurrence3 :=
  { a₀ := 456192,  a₁ := 2944512,  a₂ := 19975680
  , c₁ := 14, c₂ := -56, c₃ := 64, d := -124416 }

/-- Type D (Hurwitz) unreduced residual rat sequence. -/
def typeD_rat_uni : Recurrence3 :=
  { a₀ := -211968, a₁ := -8266752, a₂ := -95597568
  , c₁ := 14, c₂ := -56, c₃ := 64, d := 1188864 }

theorem typeA_rat_uni_measured :
    typeA_rat_uni.seq 3 = 430592 ∧
    typeA_rat_uni.seq 4 = 1778176 := by decide

theorem typeC_rat_uni_measured :
    typeC_rat_uni.seq 3 = 143838720 ∧
    typeC_rat_uni.seq 4 = 1083428352 := by decide

theorem typeD_rat_uni_measured :
    typeD_rat_uni.seq 3 = -887804928 ∧
    typeD_rat_uni.seq 4 = -7603688448 := by decide

end E213.Lib.Math.Tactic.Ring213
