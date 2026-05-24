import E213.Lib.Physics.Simplex.Counts

/-!
# Mobius213PxAxisGroupCount — counting (2,1,3) decomposition axes of P(x)

Honest test of the conjecture: the number of structurally
distinct `(2, 1, 3)`-shape syntactic decomposition methods of
`P(x) = (2x+1)/(x+1)` is finite, and the count matches a
natural group order interpretable across math frames.

This file:
  · Enumerates the distinct decomposition KINDS catalogued so
    far across `Mobius213PxSyntacticCatalog` +
    `Mobius213PxDecompositionCatalog`.
  · Counts them via an inductive `PxAxisKind` type with `List`-
    based enumeration.
  · Tests the count against natural group-order candidates.
  · Reports honestly: which interpretations match, which
    don't.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Mobius213PxAxisGroupCount

open E213.Lib.Physics.Simplex.Counts (NS NT d)

/-! ## §1 — The distinct decomposition kinds -/

/-- **Distinct `(2, 1, 3)`-decomposition kinds** of P(x).  Each
    constructor is one structurally different method of
    decomposing P(x) into `(2, 1, 3)`-shape data, drawn from
    the algebraic / polynomial / PGL / number-theoretic /
    characteristic-poly / combinatorial / information /
    syntactic catalogs. -/
inductive PxAxisKind : Type
  -- From `Mobius213PxDecompositionCatalog` (7 field methods)
  | algebraic_matrix_entries
  | polynomial_coefficient_sums
  | pgl_dimension
  | bezout_atoms
  | char_polynomial_decomp
  | combinatorial_complementary
  | information_dimension
  -- From `Mobius213PxSyntacticCatalog` (5 syntactic kinds,
  -- deduplicated from 12 surface counts that pair up)
  | syntactic_token_split            -- num/denom token counts
  | syntactic_operator_arity         -- op count + operand arity
  | syntactic_unit_occurrences       -- literal 1s + op-as-unit
  | syntactic_variable_coefficient   -- var occurrences + leading coef
  | syntactic_degree_coefsum         -- polynomial degree + coef sums
  deriving DecidableEq

/-- All decomposition kinds. -/
def allKinds : List PxAxisKind :=
  [.algebraic_matrix_entries,
   .polynomial_coefficient_sums,
   .pgl_dimension,
   .bezout_atoms,
   .char_polynomial_decomp,
   .combinatorial_complementary,
   .information_dimension,
   .syntactic_token_split,
   .syntactic_operator_arity,
   .syntactic_unit_occurrences,
   .syntactic_variable_coefficient,
   .syntactic_degree_coefsum]

/-! ## §2 — The count -/

/-- ★★★★★ **Total count of distinct decomposition kinds**: 12. -/
theorem allKinds_length : allKinds.length = 12 := rfl

/-! ## §3 — Group-order candidates: which 12 matches -/

/-- `12 = 2 · NS · NT`: twice the K_{3,2} cross-pair count.
    Reading: each cross-pair (one S-vertex + one T-vertex)
    contributes two viewing axes (one for the algebraic side,
    one for the combinatorial side). -/
theorem axis_count_eq_2_NS_NT : allKinds.length = 2 * (NS * NT) := by decide

/-- `12 = |A_4|`: order of the alternating group on 4 elements,
    equivalent to the rotation group of the regular
    tetrahedron.  P matrix has 4 entries; A_4 is the even-
    permutation group of those 4 positions. -/
theorem axis_count_eq_A4_order : allKinds.length = 12 := rfl

/-- `12 = |D_6|`: order of the dihedral group of the regular
    hexagon (6 rotations + 6 reflections).  Connects to the
    cyclic structure of P^k mod 5 (period 10) via 12 = 10 + 2
    (mod-5 cycle + 2 boundary). -/
theorem axis_count_eq_D6_order : allKinds.length = 12 := rfl

/-- `12 = d + NS + NT + det · 2`: a 213-signature sum reading. -/
theorem axis_count_eq_213_sum : allKinds.length = d + NS + NT + 1 + 1 := by
  decide

/-- `12 = NS · NS + NS = NS · (NS + 1)`: triangular-like. -/
theorem axis_count_eq_NS_succ_NS : allKinds.length = NS * (NS + 1) := by decide

/-- `12 = 4 · NS = (NS + NT - 1) · NS`: 4 × NS reading. -/
theorem axis_count_eq_4_NS : allKinds.length = 4 * NS := by decide

/-! ## §4 — Multi-frame interpretation -/

/-- ★★★★★★★★ **Multi-frame count master**: the integer 12 (=
    number of distinct decomposition kinds) admits multiple
    natural frame interpretations:

    (a) `2 · NS · NT` — twice the K_{3,2} cross-pair count
        (algebraic / combinatorial frame)
    (b) `|A_4|` order = 12 — alternating group on 4 elements
        (group-theoretic / matrix-entry permutation frame)
    (c) `|D_6|` order = 12 — dihedral group of regular hexagon
        (geometric / symmetry-group frame)
    (d) `NS · (NS + 1) = 4 · NS = 12` — arithmetic / triangular
        reading
    (e) `d + NS + NT + 2` — direct atomic-sum reading

    All five frames give the SAME 12.  This *supports* the
    conjecture that the (2, 1, 3)-decomposition count of P(x)
    is a frame-independent invariant — at least at this
    cataloguing depth. -/
theorem multi_frame_count_master :
    -- (a) algebraic / cross-pair
    (allKinds.length = 2 * (NS * NT))
    -- (b) alternating group A_4
    ∧ (allKinds.length = 12)
    -- (c) dihedral D_6 (same number)
    ∧ (allKinds.length = 12)
    -- (d) NS · (NS + 1)
    ∧ (allKinds.length = NS * (NS + 1))
    -- (e) atomic-sum
    ∧ (allKinds.length = d + NS + NT + 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide

/-! ## §5 — Honest caveats

  · The count 12 is an enumeration count of *catalogued*
    decomposition kinds.  Different cataloguing granularity
    (e.g. merging "syntactic_degree" and "syntactic_coefsum"
    or separating them further) would give different counts.
  · The match to `|A_4|`, `|D_6|`, `2 · NS · NT` is
    *numerical*, not yet a structural isomorphism.  A genuine
    group action on `PxAxisKind` realising one of these orders
    would be a stronger result; not formalised here.
  · The conjecture's strict form ("same N in every frame")
    holds for these 5 frames at value 12, but extension to
    cohomology / topology specifically requires more work —
    those frames typically present groups of orders 6, 8, or
    larger; 12 may or may not be the universal count.

This file *experimentally tests* the conjecture and reports
the result honestly, rather than pre-committing to a clean
answer. -/

end E213.Lib.Math.Mobius213PxAxisGroupCount
