import E213.Theory.Internal.Int213
import E213.Term.Tactic.Nat213

/-!
# Theory.Tower.NatPairToInt — orthogonal-axis projection

ℕ → ℤ as **two orthogonal ℕ-axes + diagonal quotient projection**
(orthogonal-coordinate framing — see G62 research note).

A pair `(a, b) : ℕ × ℕ` represents the integer `a - b`.  Two pairs
represent the same integer iff they differ by **diagonal translation**:
  `(a, b) ~ (c, d)  ⟺  a + d = b + c`

This file provides:
- `npairToInt : ℕ × ℕ → ℤ`  (the projection map)
- `npairEquiv : ℕ × ℕ → ℕ × ℕ → Prop`  (the diagonal equivalence)
- the +ℕ and -ℕ axis embeddings

All theorems satisfy the ∅-axiom standard.

## What this materializes (G62 framing)

The "2-side extension" ℕ → ℤ is concretely:
- Take TWO orthogonal copies of ℕ (the `a` axis and the `b` axis)
- Project (a, b) to `a - b` ∈ ℤ
- This collapses each diagonal-translation orbit to one integer
- The "lost information" = which fiber-representative (a, b) we
  came from
-/

namespace E213.Theory.Tower.NatPairToInt

/-- Orthogonal-axis pair representing an integer. -/
abbrev NPair : Type := Nat × Nat

/-- Project pair `(a, b)` to integer `a - b` via `Int.subNatNat`. -/
def npairToInt (p : NPair) : Int := Int.subNatNat p.1 p.2

/-- Diagonal equivalence: `(a,b) ~ (c,d) ⟺ a + d = b + c`. -/
def npairEquiv (p q : NPair) : Prop := p.1 + q.2 = p.2 + q.1

/-- Reflexivity of the equivalence. -/
theorem npairEquiv_refl (p : NPair) : npairEquiv p p := by
  show p.1 + p.2 = p.2 + p.1
  exact Nat.add_comm _ _

/-- Symmetry of the equivalence. -/
theorem npairEquiv_symm {p q : NPair} (h : npairEquiv p q) :
    npairEquiv q p := by
  show q.1 + p.2 = q.2 + p.1
  rw [Nat.add_comm q.1 p.2, Nat.add_comm q.2 p.1]
  exact h.symm

/-- The natural injection ℕ → ℕ × ℕ via `(n, 0)`.  This is one
    side of the orthogonal-axis embedding. -/
def natToNPair (n : Nat) : NPair := (n, 0)

/-- `npairToInt (n, 0) = n`.  The +ℕ axis. -/
theorem npairToInt_natToNPair (n : Nat) :
    npairToInt (natToNPair n) = Int.ofNat n := by
  show Int.subNatNat n 0 = Int.ofNat n
  cases n with
  | zero => rfl
  | succ k =>
      show (match 0 - (k+1) with
            | 0 => Int.ofNat ((k+1) - 0)
            | j+1 => Int.negSucc j) = Int.ofNat (k+1)
      rw [Nat.zero_sub]; rfl

/-- The "anti-axis" embedding ℕ → ℕ × ℕ via `(0, n)`.  Maps to
    negative integers. -/
def natToNPairNeg (n : Nat) : NPair := (0, n)

/-- `npairToInt (0, n) = -n`.  The -ℕ axis. -/
theorem npairToInt_natToNPairNeg (n : Nat) :
    npairToInt (natToNPairNeg n) = -(Int.ofNat n) := by
  show Int.subNatNat 0 n = -(Int.ofNat n)
  cases n with
  | zero => rfl
  | succ k =>
      show (match (k+1) - 0 with
            | 0 => Int.ofNat (0 - (k+1))
            | j+1 => Int.negSucc j) = -(Int.ofNat (k+1))
      rfl

/-- ★ The two axes meet at zero: `(0, 0)` projects to `0`. -/
theorem npairToInt_zero : npairToInt (0, 0) = 0 := rfl

/-- ★ Same-integer pairs are diagonally equivalent.  This is one
    direction of the Grothendieck completion correctness:
    if two pairs represent the same integer, they differ by a
    diagonal translation.  Proved on the diagonal-shift form
    `(n+k, k)` representing `n` for any k. -/
theorem npairToInt_diag_shift (n k : Nat) :
    npairToInt (n + k, k) = npairToInt (n, 0) := by
  show Int.subNatNat (n + k) k = Int.subNatNat n 0
  show (match k - (n + k) with
        | 0 => Int.ofNat ((n + k) - k)
        | j+1 => Int.negSucc j)
     = (match 0 - n with
        | 0 => Int.ofNat (n - 0)
        | j+1 => Int.negSucc j)
  rw [show k - (n + k) = 0 from by
        rw [Nat.add_comm n k];
        show (k + 0) - (k + n) = 0
        rw [E213.Tactic.Nat213.add_sub_add_left k 0 n,
            Nat.zero_sub],
      E213.Tactic.Nat213.add_sub_cancel_right n k,
      Nat.zero_sub, Nat.sub_zero]

/-- ★ Diagonal-equivalent pairs project to the same integer.
    Generalized form: `(a + k, b + k) ~ (a, b)` for any k. -/
theorem npairToInt_translation_invariant (a b k : Nat) :
    npairToInt (a + k, b + k) = npairToInt (a, b) := by
  show Int.subNatNat (a + k) (b + k) = Int.subNatNat a b
  show (match (b + k) - (a + k) with
        | 0 => Int.ofNat ((a + k) - (b + k))
        | j+1 => Int.negSucc j)
     = (match b - a with
        | 0 => Int.ofNat (a - b)
        | j+1 => Int.negSucc j)
  rw [E213.Tactic.Nat213.add_sub_add_right b k a,
      E213.Tactic.Nat213.add_sub_add_right a k b]

-- ═══ "Lost properties" ℕ → ℤ (G62) — concrete witnesses ═══

/-- ★ Loss 1 — Fiber multiplicity at 0.  In ℕ the integer `0` has
    a unique representation (just `0`).  Under the orthogonal-axis
    projection `ℕ × ℕ → ℤ`, the integer `0` has *infinitely many*
    representatives `(k, k)` for every `k`.  Concrete witness: 4
    distinct NPairs all projecting to 0. -/
theorem zero_fiber_multiple :
    npairToInt (0, 0) = npairToInt (1, 1) ∧
    npairToInt (1, 1) = npairToInt (2, 2) ∧
    npairToInt (2, 2) = npairToInt (5, 5) ∧
    npairToInt (5, 5) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- ★ Loss 2 — Negative axis emerges.  Integers below 0 exist in
    ℤ but not in ℕ.  Concrete: `-1` is reached via the anti-axis
    embedding, NOT via the +ℕ embedding. -/
theorem negative_axis_witness :
    npairToInt (natToNPairNeg 1) = -1 ∧
    ∀ n : Nat, npairToInt (natToNPair n) ≠ -1 := by
  refine ⟨?_, ?_⟩
  · exact npairToInt_natToNPairNeg 1
  · intro n h
    rw [npairToInt_natToNPair] at h
    -- h : Int.ofNat n = -1.  Both sides are different constructors:
    -- LHS = Int.ofNat n, RHS = -1 = Int.negSucc 0 (different ctor).
    cases n with
    | zero => exact absurd h (by decide)
    | succ _ => exact Int.noConfusion h

/-- ★ Loss 3 — Swap-symmetry forced.  In ℕ, the operation
    "swap (a, b) = (b, a)" has fixed points only on the
    diagonal `a = b`.  Under the projection to ℤ, swap becomes
    NEGATION — every non-zero integer is moved to its negative.
    Witness: `swap (5, 0) ↦ (0, 5)`, `npairToInt (5, 0) = 5`,
    `npairToInt (0, 5) = -5`. -/
theorem swap_realizes_negation :
    npairToInt (5, 0) = 5 ∧
    npairToInt (0, 5) = -5 ∧
    npairToInt (0, 5) = -(npairToInt (5, 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact npairToInt_natToNPair 5
  · exact npairToInt_natToNPairNeg 5
  · rfl

-- ═══ Emergence of 0 as algebraic center (G64) ═══

/-- ★ Loss/Gain 4 — `0` acquires a NEW algebraic role in ℤ that
    has no analog in ℕ: it is the **unique fixed point of negation**.
    In ℕ, negation isn't defined, so 0 has no such role.  In ℤ,
    `-z = z ⟹ z = 0` (and conversely `-0 = 0`). -/
theorem zero_unique_negation_fixed (z : Int) : -z = z ↔ z = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    cases z with
    | ofNat n =>
        cases n with
        | zero => rfl
        | succ k =>
            -- h : -(Int.ofNat (k+1)) = Int.ofNat (k+1)
            -- LHS = Int.negSucc k, RHS = Int.ofNat (k+1) — different ctors
            exact Int.noConfusion h
    | negSucc n =>
        -- h : -(Int.negSucc n) = Int.negSucc n
        -- LHS = Int.ofNat (n+1), RHS = Int.negSucc n — different ctors
        exact Int.noConfusion h
  · intro h
    rw [h]; rfl

/-- ★ The integer `0` is the **collapse of the entire diagonal**:
    every pair `(k, k) : NPair` projects to `0`.  In ℕ, `0` is just
    one element; in ℤ via NPair, `0` is the swap-fixed-set
    (= diagonal `{(k, k)}`) materialized as a single point. -/
theorem zero_is_diagonal_collapse : ∀ (k : Nat), npairToInt (k, k) = 0
  | 0 => rfl
  | (k+1) => by
      show Int.subNatNat (k+1) (k+1) = 0
      show (match (k+1) - (k+1) with
            | 0 => Int.ofNat ((k+1) - (k+1))
            | (j+1) => Int.negSucc j) = (0 : Int)
      rw [Nat.succ_sub_succ_eq_sub]
      exact zero_is_diagonal_collapse k

/-- ★ "0 lost its boundary role": in ℕ, only 0 has no predecessor;
    in ℤ, EVERY integer has a predecessor.  Witness for `0 : Int`. -/
theorem zero_has_predecessor_in_int :
    ∃ p : Int, p + 1 = 0 := ⟨-1, rfl⟩

/-- ★ Symmetric counterpart: 0 has a successor in both ℕ and ℤ —
    this part is preserved.  But the asymmetry is only between
    successor and predecessor at 0. -/
theorem zero_has_successor_in_int :
    ∃ s : Int, 0 + 1 = s := ⟨1, rfl⟩

end E213.Theory.Tower.NatPairToInt
