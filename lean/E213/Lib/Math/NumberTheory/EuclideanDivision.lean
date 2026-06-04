/-!
# 213-native Euclidean division (∅-axiom)

Core Lean's `Nat.div` / `Nat.mod` are defined by well-founded recursion,
and **every** core lemma about them carries `propext` (and some
`Quot.sound`).  Any 213 development that reasons about `/` or `%` through
those lemmas inherits the taint, so division-based combinatorics cannot
stay strict ∅-axiom while leaning on core division.

This file gives the division primitive built the other way — by *upward*
induction, using only `Nat` addition / multiplication / order lemmas that
are themselves ∅-axiom:

  - `exists_quot_rem` — for `d > 0`, every `n` has a quotient/remainder
    `n = d·q + r` with `r < d`;
  - `quot_rem_unique` — that `(q, r)` is unique.

Together they characterise Euclidean division as a relation, ∅-axiom,
without ever unfolding core `Nat.div`.  Downstream code that needs a
division fact can take it from here instead of from `Nat.div_*`.

Companion: `theory/math/numbertheory/euclidean_division.md`.
-/

namespace E213.Lib.Math.NumberTheory.EuclideanDivision

/-! ## Existence -/

/-- **Euclidean division exists.**  For `d > 0`, every `n` factors as
    `n = d·q + r` with `r < d`.  Ordinary induction on `n`: each step
    increments the remainder, rolling over to the next quotient when it
    would reach `d`.  No subtraction, no core `Nat.div`. -/
theorem exists_quot_rem (d : Nat) (hd : 0 < d) :
    ∀ n, ∃ q r, n = d * q + r ∧ r < d := by
  intro n
  induction n with
  | zero => exact ⟨0, 0, by rw [Nat.mul_zero], hd⟩
  | succ n ih =>
      rcases ih with ⟨q, r, hn, hr⟩
      rcases Nat.lt_or_ge (r + 1) d with h | h
      · -- remainder still below d
        exact ⟨q, r + 1, by rw [hn]; exact (Nat.add_succ (d * q) r).symm, h⟩
      · -- remainder reached d: roll over to q + 1, remainder 0
        have hrd : r + 1 = d := Nat.le_antisymm hr h
        refine ⟨q + 1, 0, ?_, hd⟩
        rw [hn, Nat.mul_succ, Nat.add_zero]
        calc (d * q + r).succ = d * q + (r + 1) := (Nat.add_succ (d * q) r).symm
          _ = d * q + d := by rw [hrd]

/-! ## Uniqueness -/

/-- Reshape `a + d + x = (a + x) + d`, used to cancel the common `+ d`. -/
private theorem add_mid_comm (a d x : Nat) : a + d + x = (a + x) + d := by
  rw [Nat.add_assoc, Nat.add_comm d x, ← Nat.add_assoc]

/-- Right cancellation, ∅-axiom (core `Nat.add_right_cancel` carries
    `propext`).  Induction on the cancelled summand via constructor
    injectivity. -/
private theorem add_right_cancel_pure {n m : Nat} :
    ∀ k, n + k = m + k → n = m
  | 0, h => h
  | _ + 1, h => add_right_cancel_pure _ (Nat.succ.inj h)

/-- **Quotient and remainder are unique.**  Two Euclidean representations
    of the same `n` (both remainders `< d`) coincide.  Induction on the
    first quotient; the cross cases force a remainder `≥ d`,
    contradicting `r < d`. -/
theorem quot_rem_unique (d : Nat) :
    ∀ q1 r1 q2 r2, r1 < d → r2 < d →
      d * q1 + r1 = d * q2 + r2 → q1 = q2 ∧ r1 = r2 := by
  intro q1
  induction q1 with
  | zero =>
      intro r1 q2 r2 h1 _ heq
      cases q2 with
      | zero =>
          refine ⟨rfl, ?_⟩
          rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add] at heq
          exact heq
      | succ q2' =>
          exfalso
          rw [Nat.mul_zero, Nat.zero_add, Nat.mul_succ] at heq
          have hle : d ≤ r1 := by
            rw [heq]
            exact Nat.le_trans (Nat.le_add_left d (d * q2')) (Nat.le_add_right _ r2)
          exact Nat.lt_irrefl d (Nat.lt_of_le_of_lt hle h1)
  | succ q1' ih =>
      intro r1 q2 r2 h1 h2 heq
      cases q2 with
      | zero =>
          exfalso
          rw [Nat.mul_zero, Nat.zero_add, Nat.mul_succ] at heq
          have hle : d ≤ r2 := by
            rw [← heq]
            exact Nat.le_trans (Nat.le_add_left d (d * q1')) (Nat.le_add_right _ r1)
          exact Nat.lt_irrefl d (Nat.lt_of_le_of_lt hle h2)
      | succ q2' =>
          rw [Nat.mul_succ, Nat.mul_succ] at heq
          -- (d*q1' + d) + r1 = (d*q2' + d) + r2 ; cancel the common + d
          rw [add_mid_comm (d * q1') d r1, add_mid_comm (d * q2') d r2] at heq
          have heq' : d * q1' + r1 = d * q2' + r2 := add_right_cancel_pure d heq
          rcases ih r1 q2' r2 h1 h2 heq' with ⟨hq, hr⟩
          exact ⟨congrArg Nat.succ hq, hr⟩

/-! ## Packaged characterisation -/

/-- The Euclidean-division relation: `IsQuotRem d n q r` holds iff
    `n = d·q + r` with `r < d`. -/
def IsQuotRem (d n q r : Nat) : Prop := n = d * q + r ∧ r < d

/-- ★★★★★ **Euclidean division, ∅-axiom.**  For `d > 0` and every `n`
    there is a unique `(q, r)` with `n = d·q + r`, `r < d` — the division
    primitive characterised without unfolding core `Nat.div`. -/
theorem euclidean_division (d : Nat) (hd : 0 < d) (n : Nat) :
    (∃ q r, IsQuotRem d n q r)
    ∧ (∀ q1 r1 q2 r2, IsQuotRem d n q1 r1 → IsQuotRem d n q2 r2 →
        q1 = q2 ∧ r1 = r2) := by
  refine ⟨exists_quot_rem d hd n, ?_⟩
  rintro q1 r1 q2 r2 ⟨hn1, hr1⟩ ⟨hn2, hr2⟩
  exact quot_rem_unique d q1 r1 q2 r2 hr1 hr2 (hn1 ▸ hn2)

end E213.Lib.Math.NumberTheory.EuclideanDivision
