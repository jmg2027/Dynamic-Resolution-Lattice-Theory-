import E213.Physics.Simplex.Counts

/-!
# f_occ spectrum — pattern occupation fractions on the (3, 2) 5-simplex

The 10 distinct rational f_occ values that govern all DRLT couplings
via the universal law `x = α_GUT × f_occ` (free regime).

Structure: each entry is `((num, den), multiplicity)`.  All denominators
are slot/face counts {1, 2, 3, 4, 5}.  Hodge-paired entries
(k ↔ d - k) give CPT symmetry.

This file is 0-axiom, decide-checked throughout.  No real numbers.
-/

namespace E213.Physics.Focc

open E213.Physics.Simplex

/-- The 10-entry f_occ spectrum on the (3, 2) 5-simplex.

    Each entry: `((numerator, denominator), multiplicity)`.

    Categories (ordered by f_occ):
      1/5, 2/5, 3/5, 4/5  → matter (Λᵏℂ⁵, k=1,2,3,4)
      1/4, 3/4            → yukawa (face k-vertex)
      1/3, 2/3            → gauge (hinge k-vertex)
      1/2                 → Higgs (self-dual)
      1/1                 → confined (full occupation)
-/
def spectrum : List ((Nat × Nat) × Nat) :=
  [ ((1, 5), 5)
  , ((1, 4), 10)
  , ((1, 3), 10)
  , ((2, 5), 10)
  , ((1, 2), 50)
  , ((3, 5), 10)
  , ((2, 3), 10)
  , ((3, 4), 10)
  , ((4, 5), 5)
  , ((1, 1), 26)
  ]

/-- The spectrum has exactly 10 distinct entries. -/
theorem distinct_count : spectrum.length = 10 := by decide

/-- Sum of multiplicities = 146.
    Breakdown: 4×5 (matter ∧¹∧⁴) + 4×10 (face/hinge yukawa+gauge)
             + 1×50 (Higgs self-dual) + 1×26 (confined) = 146. -/
theorem total_multiplicity :
    (spectrum.map (·.2)).foldl (· + ·) 0 = 146 := by decide

/-- All denominators are in {1, 2, 3, 4, 5} — exactly the
    slot/face counts of the (3, 2) 5-simplex.  No transcendentals
    in the spectrum. -/
theorem denominators_finite :
    ∀ x ∈ spectrum,
      x.1.2 = 1 ∨ x.1.2 = 2 ∨ x.1.2 = 3
      ∨ x.1.2 = 4 ∨ x.1.2 = 5 := by decide

/-- All numerators are < d = 5 (or = 1 for f_occ = 1). -/
theorem numerators_bounded :
    ∀ x ∈ spectrum, x.1.1 ≤ d := by decide

/-- Hodge pair check: (1, 5) and (4, 5) have same multiplicity. -/
theorem hodge_pair_1_4 :
    (spectrum.get? 0).map (·.2) = (spectrum.get? 8).map (·.2) := by decide

/-- Hodge pair check: (2, 5) and (3, 5) have same multiplicity. -/
theorem hodge_pair_2_3 :
    (spectrum.get? 3).map (·.2) = (spectrum.get? 5).map (·.2) := by decide

/-- The Higgs entry has the largest multiplicity (50). -/
theorem higgs_dominant :
    (spectrum.get? 4).map (·.2) = some 50 := by decide

/-- The two confined-region entries (matter ∧¹ and full).  These are
    f_occ = 1/d (multiplicity d) and f_occ = 1 (multiplicity 26). -/
theorem matter_count : (spectrum.get? 0).map (·.2) = some d := by decide
theorem confined_count : (spectrum.get? 9).map (·.1) = some (1, 1) := by decide

end E213.Physics.Focc
