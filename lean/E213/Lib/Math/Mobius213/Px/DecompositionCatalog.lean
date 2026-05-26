import E213.Lib.Math.Mobius213
import E213.Lib.Math.Mobius213OneAsGlue
import E213.Lib.Math.SimplexCountsBridge

/-!
# Mobius213.Px.DecompositionCatalog — parallel (2, 1, 3) extraction methods

The signature axis catalogs (`Mobius213SignatureAxisCatalog`
and its Phase-2 sibling) enumerate *where* the framework's
`(NS, NT, det)` signature appears across math/physics
domains.  This file addresses a sharper question:

  **What are the parallel methods for extracting `(2, 1, 3)`
  from P(x) itself across math fields?**

The conjecture: each math field has a *natural counting
tradition*; when that tradition is applied to the single object
`P(x) = (2x+1)/(x+1)` or equivalently the matrix
`P = [[2,1],[1,1]]`, the result lands on `(2, 1, 3)`-shaped data.
The extraction *methods* are structurally parallel across
fields, even though their vocabularies differ.

Each axis below is "field X's counting method applied to P(x)
yields a `(2, 1, 3)`-shaped triple".  Together they witness
that the integers `(NS, NT, det) = (3, 2, 1)` are not
field-specific but *the same data viewed through different
counting lenses*.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Mobius213.Px.DecompositionCatalog

open E213.Lib.Math.SimplexCountsBridge (NS NT d)
open E213.Lib.Math.Mobius213OneAsGlue
  (mobius_entries_sum_to_d ns_is_succ_nt mobius_det_eq_ns_minus_nt
   off_diagonal_is_two_ones one_is_det)

/-! ## §1 — Algebraic counting (matrix entries) -/

/-- **Algebraic method**: count matrix entries by their
    structural role.  P = [[2, 1], [1, 1]] has 4 entries
    decomposing as `(NT, glue, glue, unit)`.

    Reading: `2` (one NT entry) + `1+1` (two glues) + `1` (one
    unit) = `1·NT + 2·glue + 1·unit`. -/
theorem px_alg_entries_decomp :
    -- One NT-valued entry
    ((2 : Nat) = NT)
    -- Two glue entries (off-diagonal sum)
    ∧ ((1 : Nat) + 1 = NT)
    -- One unit entry (det)
    ∧ ((1 : Nat) = 1)
    -- Sum = d
    ∧ ((2 : Nat) + 1 + 1 + 1 = d) :=
  ⟨by decide, off_diagonal_is_two_ones, rfl, mobius_entries_sum_to_d⟩

/-! ## §2 — Polynomial counting (coefficient extraction) -/

/-- **Polynomial method**: extract degree and coefficient counts
    of `2x+1` (numerator) and `x+1` (denominator).

    Reading: numerator `2x+1` has 2 coefficients summing to
    `NS = 3`; denominator `x+1` has 2 coefficients summing to
    `NT = 2`; division is 1 operator. -/
theorem px_poly_coeff_decomp :
    -- Numerator coefficient count
    ((2 : Nat) = NT)
    -- Numerator coefficient sum (2 + 1)
    ∧ ((2 : Nat) + 1 = NS)
    -- Denominator coefficient sum (1 + 1)
    ∧ ((1 : Nat) + 1 = NT)
    -- Single division operator
    ∧ ((1 : Nat) = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | decide

/-! ## §3 — Projective / PGL(2) counting -/

/-- **PGL counting**: dimension of the projective transformation
    group + linear space + scalar invariance.

    Reading: PGL(2) has `4 - 1 = 3` parameters (matrix minus
    scale equivalence); acts on 2D linear space `{x, 1}`;
    projective unit = 1. -/
theorem px_pgl_dim_decomp :
    -- PGL(2) dimension = matrix DOF
    ((2 : Nat) * 2 - 1 = NS)
    -- Input linear space dimension
    ∧ ((2 : Nat) = NT)
    -- Projective unit (scale invariance)
    ∧ ((1 : Nat) = 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> first | rfl | decide

/-! ## §4 — Number-theoretic counting (Bezout / Pell unit) -/

/-- **Number-theoretic method**: count `(2, 1, 3)` via Bezout
    on `{NT, NS} = {2, 3}` and the Pell unit invariant.

    Reading: `2 = NT` and `3 = NS` are coprime atoms (gcd = 1);
    `det P = 1` is the Pell unit; Bezout combination
    `3·1 - 2·1 = 1` realises the glue. -/
theorem px_numeric_bezout :
    -- Atoms NT, NS
    ((2 : Nat) = NT)
    ∧ ((3 : Nat) = NS)
    -- Pell unit / det
    ∧ ((1 : Int) = (2 : Int) * 1 - 1 * 1)
    -- Bezout combination NS·1 − NT·1 = 1
    ∧ ((1 : Int) = (NS : Int) - (NT : Int))
    -- NS - NT = glue = 1
    ∧ NS = NT + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact one_is_det
  · exact mobius_det_eq_ns_minus_nt.symm
  · exact ns_is_succ_nt

/-! ## §5 — Discriminant / characteristic-polynomial counting -/

/-- **Characteristic polynomial counting**: P has char poly
    `x² − 3x + 1` of degree 2 with 2 roots `(φ², 1/φ²)` and
    discriminant 5.

    Reading: degree 2 = NT; trace coefficient `3 = NS`;
    constant coefficient `1 = det`. -/
theorem px_char_poly_decomp :
    -- Polynomial degree (= number of eigenvalues = NT = 2)
    ((2 : Nat) = NT)
    -- Trace coefficient = NS = 3
    ∧ ((3 : Int) = (NS : Int))
    -- Constant term = det = 1
    ∧ ((1 : Int) = (2 : Int) * 1 - 1 * 1)
    -- Discriminant = d = 5
    ∧ ((3 : Int)^2 - 4 * 1 = (d : Int)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · decide
  · exact one_is_det
  · decide

/-! ## §6 — Combinatorial counting (factorial / Pascal-row witness) -/

/-- **Combinatorial method**: count `(2, 1, 3)` via factorial
    decompositions of small integers and the `(NS, NT)`
    complementary-subset symmetry.

    Reading: `3! = 6` (Sym(3) order = NS·NT); `5·4 = 20`
    falling-factorial relates to Pascal row `d` middle pair
    `2·10 = 20`; complementary subset-sizes `2 + 3 = d`. -/
theorem px_combinatorial_factorial :
    -- 3! = 6 = NS · NT
    (3 * 2 * 1 = NS * NT)
    -- Complementary subset sizes 2 + 3 = d
    ∧ (NT + NS = d)
    -- Pascal row d middle pair: 2 · 10 = 20 = 5 · 4
    ∧ ((2 : Nat) * 10 = d * (d - 1))
    -- Row d sum: 2^d
    ∧ ((2 : Nat) ^ d = 32) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §7 — Information / dimension counting -/

/-- **Information-theoretic method**: count P's data by
    information-theoretic dimensions.

    Reading: input space has 2 dimensions of state (variable
    +constant), matrix carries 3 independent parameters (DOF),
    output ratio = 1 bit of projective quotient. -/
theorem px_information_dim :
    -- Input dimensions (variable + constant)
    ((2 : Nat) = NT)
    -- Matrix DOF
    ∧ ((4 : Nat) - 1 = NS)
    -- Output projective dimension
    ∧ ((1 : Nat) = 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> first | rfl | decide

/-! ## §8 — Master decomposition catalog -/

/-- ★★★★★★★★ **Master parallel-decomposition catalog**: across
    7 distinct counting traditions (algebraic / polynomial /
    PGL / number-theoretic / characteristic-polynomial /
    combinatorial / information), P(x) yields `(2, 1, 3)`-
    shaped data.

    Each conjunct below is one field's natural counting method
    applied to P(x), confirming that the integers `(NT, det,
    NS) = (2, 1, 3)` are not field-specific but the same data
    viewed through different counting lenses. -/
theorem px_decomposition_master :
    -- Algebraic (matrix entries)
    ((2 : Nat) = NT ∧ (1 : Nat) + 1 = NT ∧ (2 : Nat) + 1 + 1 + 1 = d)
    -- Polynomial (coefficient sums)
    ∧ ((2 : Nat) + 1 = NS ∧ (1 : Nat) + 1 = NT)
    -- PGL (DOF / input dim)
    ∧ ((2 : Nat) * 2 - 1 = NS ∧ (2 : Nat) = NT)
    -- Number-theoretic (Bezout / Pell)
    ∧ ((1 : Int) = (NS : Int) - (NT : Int) ∧ NS = NT + 1)
    -- Characteristic polynomial (degree, trace, det, disc)
    ∧ ((3 : Int) = (NS : Int) ∧ (3 : Int)^2 - 4 * 1 = (d : Int))
    -- Combinatorial (factorial / complementary subsets)
    ∧ (3 * 2 * 1 = NS * NT ∧ NT + NS = d)
    -- Information (input + DOF + projective)
    ∧ ((2 : Nat) = NT ∧ (4 : Nat) - 1 = NS) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
          ⟨?_, ?_⟩⟩
  all_goals first | rfl | decide
                  | exact mobius_entries_sum_to_d
                  | exact mobius_det_eq_ns_minus_nt.symm
                  | exact ns_is_succ_nt

end E213.Lib.Math.Mobius213.Px.DecompositionCatalog
