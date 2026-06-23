import E213.Lib.Physics.Simplex.Counts
import E213.Meta.Int213.Core

/-!
# Mobius213.Px.DenomInvariantFamily — the denominator-preserving symmetry family of P(x)

For any integer `n`, P(x) = (2x+1)/(x+1) admits a rewriting

  `P(x) = n + ((2 - n)·x + (1 - n)) / (x + 1)`

where the *denominator (x+1) is preserved* and the numerator
shifts as a linear function of `n`.  This gives a ℤ-indexed
family of decompositions of P(x), each preserving the
denominator.

  · n = 0: `P = 0 + (2x+1)/(x+1)`             — original form
  · n = 1: `P = 1 + x/(x+1)`                  — leading 1 absorbed
  · n = 2: `P = 2 - 1/(x+1)`                  — numerator collapses to -1
  · n = 3: `P = 3 - (x+2)/(x+1)`              — numerator flips sign
  · n = 4: `P = 4 - (2x+3)/(x+1)`
  · n = 5: `P = 5 - (3x+4)/(x+1)`
  · n = 6: `P = 6 - (4x+5)/(x+1)`
  · …

The structure: `ℤ` acting by integer-shift on the additive
constant.  Each shift recomputes the residue numerator as
`(2-n)·x + (1-n)`.

This file:
  · Proves the general algebraic identity for the family.
  · Concrete witnesses at `n = 0, 1, 2, 3, 4, 5, 6`.
  · Identifies the `(2, 1, 3)`-signature subset of the family.
  · Connects the family to the broader symmetry-group
    conjecture (different *preservation axes* yielding
    different group-like structures).

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Algebra.Mobius213.Px.DenomInvariantFamily

open E213.Lib.Physics.Simplex.Counts (NS NT d)

/-! ## §1 — The general algebraic identity -/

/-- ★★★★★ **The denominator-preserving family identity**:

      `(2x+1) - n·(x+1) = (2 - n)·x + (1 - n)`

    This is the residue numerator at shift `n`: subtracting
    `n·(x+1)` from the original numerator preserves the
    denominator and shifts the additive constant.

    Proved via the PURE Int213 simp ring set (same set as
    `QuadIdentities.int_quad_diophantus`). -/
theorem denom_invariant_residue (n x : Int) :
    (2 * x + 1) - n * (x + 1) = (2 - n) * x + (1 - n) := by
  -- Expand n * (x + 1) = n*x + n
  rw [E213.Meta.Int213.mul_add, E213.Meta.Int213.mul_one]
  -- Goal: 2*x + 1 - (n*x + n) = (2-n)*x + (1-n)
  -- Expand (2 - n) * x via Int213.sub_mul: 2*x - n*x
  rw [E213.Meta.Int213.sub_mul]
  -- Goal: 2*x + 1 - (n*x + n) = 2*x - n*x + (1 - n)
  -- Rewrite both sides into canonical (+ -) form.
  rw [Int.sub_eq_add_neg, E213.Meta.Int213.neg_add,
      Int.sub_eq_add_neg, Int.sub_eq_add_neg]
  -- Goal: 2*x + 1 + (-(n*x) + -n) = 2*x + -(n*x) + (1 + -n)
  -- Flatten both sides to left-assoc, then swap middle terms.
  rw [← E213.Meta.Int213.add_assoc (2 * x + 1) (-(n*x)) (-n),
      ← E213.Meta.Int213.add_assoc (2 * x + -(n*x)) 1 (-n)]
  -- Goal: 2*x + 1 + -(n*x) + -n = 2*x + -(n*x) + 1 + -n
  rw [E213.Meta.Int213.add_right_comm (2 * x) 1 (-(n*x))]

/-! ## §2 — Concrete witnesses at n = 0, 1, 2, 3, 4, 5, 6 -/

/-- `n = 0`: identity decomposition `P(x) = 0 + (2x+1)/(x+1)`. -/
theorem family_n0 (x : Int) :
    (2 * x + 1) - 0 * (x + 1) = 2 * x + 1 := by
  rw [denom_invariant_residue]
  show (2 : Int) * x + 1 = 2 * x + 1
  rfl

/-- `n = 1`: numerator simplifies to `x`. -/
theorem family_n1 (x : Int) :
    (2 * x + 1) - 1 * (x + 1) = x := by
  rw [denom_invariant_residue]
  -- Goal: (2 - 1) * x + (1 - 1) = x
  show (1 : Int) * x + 0 = x
  rw [Int.one_mul, Int.add_zero]

/-- `n = 2`: numerator collapses to `-1`. -/
theorem family_n2 (x : Int) :
    (2 * x + 1) - 2 * (x + 1) = -1 := by
  rw [denom_invariant_residue]
  -- Goal: (2 - 2) * x + (1 - 2) = -1
  show (0 : Int) * x + (-1) = -1
  rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_add]

/-- `n = 3`: numerator becomes `-(x + 2)`. -/
theorem family_n3 (x : Int) :
    (2 * x + 1) - 3 * (x + 1) = -(x + 2) := by
  rw [denom_invariant_residue]
  -- Goal: (2 - 3) * x + (1 - 3) = -(x + 2)
  show (-1 : Int) * x + (-2) = -(x + 2)
  rw [E213.Meta.Int213.neg_add]
  -- Goal: -1 * x + -2 = -x + -2
  show (-1 : Int) * x + (-2) = -x + (-2)
  rw [show ((-1 : Int) * x = -x) from by
        rw [E213.Meta.Int213.neg_mul]; rw [Int.one_mul]]

/-- `n = 4`: numerator becomes `-(2x + 3)`. -/
theorem family_n4 (x : Int) :
    (2 * x + 1) - 4 * (x + 1) = -(2 * x + 3) := by
  rw [denom_invariant_residue]
  -- Goal: (2 - 4) * x + (1 - 4) = -(2 * x + 3)
  show (-2 : Int) * x + (-3) = -(2 * x + 3)
  rw [E213.Meta.Int213.neg_add, E213.Meta.Int213.neg_mul]

/-- `n = 5`: numerator becomes `-(3x + 4)`. -/
theorem family_n5 (x : Int) :
    (2 * x + 1) - 5 * (x + 1) = -(3 * x + 4) := by
  rw [denom_invariant_residue]
  show (-3 : Int) * x + (-4) = -(3 * x + 4)
  rw [E213.Meta.Int213.neg_add, E213.Meta.Int213.neg_mul]

/-- `n = 6`: numerator becomes `-(4x + 5)`. -/
theorem family_n6 (x : Int) :
    (2 * x + 1) - 6 * (x + 1) = -(4 * x + 5) := by
  rw [denom_invariant_residue]
  show (-4 : Int) * x + (-5) = -(4 * x + 5)
  rw [E213.Meta.Int213.neg_add, E213.Meta.Int213.neg_mul]

/-! ## §3 — The (2,1,3) signature subset

Among the ℤ-indexed family, specific shifts highlight the
`(NS, NT, det) = (3, 2, 1)` signature.  Reading the
**residue-numerator coefficient pattern** `(2-n, 1-n)`:

  · n = -1: `(3, 2)` — exact `(NS, NT)` atomic signature
  · n =  0: `(2, 1)` — `(NT, det)` directly
  · n =  1: `(1, 0)` — `(det, zero)`
  · n =  2: `(0, -1)` — boundary

The shift `n = -1` is the unique shift where the residue
numerator coefficients are *exactly* `(NS, NT) = (3, 2)`. -/

/-- ★★★★★★ **The `(NS, NT)` shift**: at `n = -1`, the residue
    numerator `(2-n, 1-n) = (3, 2)` is exactly the atomic
    signature `(NS, NT)`.

      P(x) = -1 + (3x + 2)/(x + 1)
-/
theorem family_nNS_NT (x : Int) :
    (2 * x + 1) - (-1) * (x + 1) = 3 * x + 2 := by
  rw [denom_invariant_residue]
  -- Goal: (2 - -1) * x + (1 - -1) = 3 * x + 2
  show (3 : Int) * x + 2 = 3 * x + 2
  rfl

/-- ★★★★ **The `(NT, det)` shift**: at `n = 0`, residue is
    `(2-0, 1-0) = (2, 1) = (NT, det)`. -/
theorem family_nNT_det (x : Int) :
    (2 * x + 1) - 0 * (x + 1) = (NT : Int) * x + 1 := by
  rw [denom_invariant_residue]
  -- Goal: (2 - 0) * x + (1 - 0) = NT * x + 1
  show (2 : Int) * x + 1 = (2 : Int) * x + 1
  rfl

/-! ## §4 — Family symmetry structure: ℤ-translation group -/

/-- ★★★★★ **Family additivity**: shifting by `n + m` is the
    same as shifting by `n` then by `m`.  The family is a
    ℤ-torsor: ℤ acts on decompositions by additive translation. -/
theorem family_additive (n m x : Int) :
    (2 * x + 1) - (n + m) * (x + 1)
      = ((2 * x + 1) - n * (x + 1)) - m * (x + 1) := by
  rw [E213.Meta.Int213.add_mul]
  -- Goal: 2*x + 1 - (n*(x+1) + m*(x+1))
  --     = 2*x + 1 - n*(x+1) - m*(x+1)
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg]
  rw [E213.Meta.Int213.neg_add]
  -- Goal: 2*x + 1 + (-(n*(x+1)) + -(m*(x+1)))
  --     = 2*x + 1 + -(n*(x+1)) + -(m*(x+1))
  rw [← E213.Meta.Int213.add_assoc]

/-! ## §5 — Master: the ℤ-family + (NS, NT) signature -/

/-- ★★★★★★★★ **Master**: the denominator-preserving family
    is parameterised by ℤ, with the algebraic identity
    `(2x+1) - n(x+1) = (2-n)x + (1-n)`; among ℤ-shifts, the
    `n = -1` shift produces the exact `(NS, NT)` atomic
    signature `(3, 2)` as the residue-numerator coefficients,
    and the `n = 0` shift recovers the original `(NT, det)`
    coefficients. -/
theorem denom_invariant_family_master :
    -- (a) General algebraic identity for any n
    (∀ (n x : Int), (2 * x + 1) - n * (x + 1) = (2 - n) * x + (1 - n))
    -- (b) n = -1 gives (NS, NT) atomic signature
    ∧ (∀ x : Int, (2 * x + 1) - (-1) * (x + 1) = 3 * x + 2)
    -- (c) n = 0 gives the original (NT, det) coefficients
    ∧ (∀ x : Int, (2 * x + 1) - 0 * (x + 1) = (NT : Int) * x + 1)
    -- (d) ℤ-additivity: family is a ℤ-torsor under shifts
    ∧ (∀ (n m x : Int), (2 * x + 1) - (n + m) * (x + 1)
        = ((2 * x + 1) - n * (x + 1)) - m * (x + 1)) :=
  ⟨denom_invariant_residue,
   family_nNS_NT,
   family_nNT_det,
   family_additive⟩

end E213.Lib.Math.Algebra.Mobius213.Px.DenomInvariantFamily
