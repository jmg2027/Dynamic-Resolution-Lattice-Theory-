import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff

/-!
# Jacobsthal-sequence cardinality cut-off

Eighth external sequence in the cut-off applications family.
Jacobsthal numbers `J_n` with `J_0 = 0`, `J_1 = 1`,
`J_{n+2} = J_{n+1} + 2 J_n` (multiplicative-variant of Fibonacci
with weight 2 on the deeper term).

Closed form: `J_n = (2^n − (−1)^n) / 3`.  Growth is `~ 2^n / 3` —
fastest in the Direction C family (compare Padovan `≈ 1.32^n`,
Narayana `≈ 1.47^n`, Tribonacci `≈ 1.84^n`, Fibonacci/Lucas
`≈ 1.62^n`, Pell `≈ 2.41^n`).  Jacobsthal sits between the
slow-growth recurrences and Pell.

## Catalogue coincidences

| n | J_n | catalogue role          |
|---|-----|-------------------------|
| 3 | 3   | NS (atomic generator)   |
| 4 | 5   | d (atomic generator)    |

★ **Jacobsthal hits `(NS, d)` at CONSECUTIVE indices `{3, 4}`**,
skipping `NT = 2` entirely (J_2 = 1).  Only two catalogue hits,
but they're the two LARGER atomic generators landing on the
sub-lattice where `NT` is absent.  No catalogue prime hits
(`J_5 = 11`, `J_6 = 21 = NS · 7`, `J_7 = 43`).

The closed form `J_n = (2^n − (−1)^n) / 3` makes Jacobsthal the
unique Direction C sequence whose values are always odd for
`n ≥ 1` — structural complement to the Hunter-atom parity
spectrum (`{2, 3, 5, 7, 13}` has only `NT = 2` even).

## Cut-off slices

  · **Depth 1 (M_1 = 3125)**: cut-off at `n ≥ 14`
    (`J_13 = 2731 < 3125 < 5461 = J_14`).  Earliest crossing in
    the Direction C family — exponential growth rate dominates.
  · **Depth 2 restricted (M_{2,r} = 9 765 625)**: cut-off at
    `n ≥ 25` (`J_24 = 5 592 405 < M_{2,r} < 11 184 811 = J_25`).

## Cross-references

  · `cardinality_cutoff_applications.md` — applications family.
  · `PellCutoff.lean` — closest growth-rate companion
    (silver-ratio `≈ 2.41^n` vs. Jacobsthal `2^n`).
-/

namespace E213.Lib.Math.Cohomology.Fractal.JacobsthalCutoff

open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanDepth2Cutoff (M2r depth2Value
  asymptotic_cutoff_at_depth_2_restricted)

/-! ## §1 Jacobsthal sequence -/

/-- Jacobsthal sequence: `J_0 = 0`, `J_1 = 1`,
    `J_{n+2} = J_{n+1} + 2 J_n`. -/
def Jac : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => Jac (n + 1) + 2 * Jac n

/-! ## §2 Small-value table -/

theorem Jac_0  : Jac 0  = 0 := rfl
theorem Jac_1  : Jac 1  = 1 := rfl
theorem Jac_2  : Jac 2  = 1 := by decide
theorem Jac_3  : Jac 3  = 3 := by decide
theorem Jac_4  : Jac 4  = 5 := by decide
theorem Jac_5  : Jac 5  = 11 := by decide
theorem Jac_6  : Jac 6  = 21 := by decide
theorem Jac_7  : Jac 7  = 43 := by decide
theorem Jac_8  : Jac 8  = 85 := by decide
theorem Jac_13 : Jac 13 = 2731 := by decide
theorem Jac_14 : Jac 14 = 5461 := by decide
theorem Jac_24 : Jac 24 = 5592405 := by decide
theorem Jac_25 : Jac 25 = 11184811 := by decide

/-! ## §3 Catalogue coincidences

    Jacobsthal hits the catalogue ONLY at indices `{3, 4}`, but
    those are the two LARGER atomic generators in consecutive
    sequence positions: `(J_3, J_4) = (NS, d)`. -/

/-- `J_3 = 3 = NS` (atomic generator). -/
theorem Jac_3_eq_NS : Jac 3 = 3 := Jac_3

/-- `J_4 = 5 = d` (atomic generator). -/
theorem Jac_4_eq_d : Jac 4 = 5 := Jac_4

/-- ★ **Consecutive `(NS, d)` window**:
    `(J_3, J_4) = (3, 5)` — Jacobsthal threads the two larger
    Hunter generators at adjacent indices, skipping `NT = 2`
    (`J_2 = 1` is not catalogue).  Distinct fingerprint from
    Fibonacci's `(NT, NS, d) = (F_3, F_4, F_5)` triple. -/
theorem Jac_3_4_are_NS_d :
    Jac 3 = 3 ∧ Jac 4 = 5 :=
  ⟨Jac_3, Jac_4⟩

/-- ★ **`J_6 = 21 = NS · 7`**: Jacobsthal hits the product of two
    catalogue atoms at index 6.  Not a direct hit but a structural
    coincidence with the multiplicative sub-lattice. -/
theorem Jac_6_eq_NS_times_7 : Jac 6 = 3 * 7 := Jac_6

/-! ## §4 Depth-1 cut-off application

    `M_1 = 3125`.  Boundary `J_13 = 2731 < 3125 < 5461 = J_14`.
    Earliest crossing in the Direction C family. -/

theorem Jac_13_below_M1 : Jac 13 < 3125 := by decide
theorem Jac_14_above_M1 : 3125 < Jac 14 := by decide

/-- ★ **Depth-1 cut-off witness for Jacobsthal**: `J_14 = 5461`
    exceeds `M_1 = 3125`. -/
theorem Jac_14_exceeds_depth_1 : 3125 < Jac 14 := Jac_14_above_M1

theorem Jac_14_not_at_depth_1 :
    ∀ (i j : Fin 3),
      [2, 3, 5].get! i.val ≠ Jac 14
      ∧ ([2, 3, 5].get! i.val + [2, 3, 5].get! j.val) ≠ Jac 14
      ∧ ([2, 3, 5].get! i.val * [2, 3, 5].get! j.val) ≠ Jac 14
      ∧ ([2, 3, 5].get! i.val ^ [2, 3, 5].get! j.val) ≠ Jac 14 :=
  fun i j => asymptotic_cutoff_at_depth_1 (Jac 14) i j Jac_14_above_M1

/-! ## §5 Depth-2-restricted cut-off application

    `M_{2,r} = 9 765 625`.  Boundary `J_24 = 5 592 405 < M_{2,r}
    < 11 184 811 = J_25`. -/

theorem Jac_24_below_M2r : Jac 24 < M2r := by decide
theorem Jac_25_above_M2r : M2r < Jac 25 := by decide

/-- ★ **Depth-2-restricted cut-off witness for Jacobsthal**:
    `J_25 = 11 184 811` exceeds `M_{2,r} = 9 765 625`. -/
theorem Jac_25_not_at_depth_2_restricted :
    ∀ (a b c d : Fin 3) (opL opR : Fin 3) (opOut : Fin 2),
      depth2Value a b c d opL opR opOut ≠ Jac 25 :=
  fun a b c d opL opR opOut =>
    asymptotic_cutoff_at_depth_2_restricted (Jac 25)
      Jac_25_above_M2r a b c d opL opR opOut

/-! ## §6 Capstone -/

/-- ★★★ **Capstone**: Jacobsthal catalogue intersections
    (consecutive `(NS, d)` window + multiplicative coincidence
    `J_6 = NS · 7`) + cut-off boundaries.  Jacobsthal is the
    fastest-growing slow-recurrence in Direction C and the only
    sequence with `J_n` always odd for `n ≥ 1`. -/
theorem capstone :
    -- Consecutive (NS, d) at indices {3, 4}
    (Jac 3 = 3 ∧ Jac 4 = 5)
    -- Multiplicative coincidence
    ∧ Jac 6 = 3 * 7
    -- Depth-1 cut-off boundary (earliest in family)
    ∧ 3125 < Jac 14
    -- Depth-2-restricted cut-off boundary
    ∧ M2r < Jac 25 :=
  ⟨Jac_3_4_are_NS_d, Jac_6_eq_NS_times_7, Jac_14_above_M1,
   Jac_25_above_M2r⟩

end E213.Lib.Math.Cohomology.Fractal.JacobsthalCutoff
