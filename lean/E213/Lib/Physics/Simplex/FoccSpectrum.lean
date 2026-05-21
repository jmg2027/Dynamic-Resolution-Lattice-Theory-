import E213.Lib.Physics.Simplex.Counts

/-!
# f_occ spectrum — pattern occupation fractions on the (3, 2) 5-simplex

The 10 distinct rational f_occ values that govern all DRLT couplings
via the universal law `x = α_GUT × f_occ` (free regime).

Structure: each entry is `((num, den), multiplicity)`.  All denominators
are slot/face counts {1, 2, 3, 4, 5}.  Hodge-paired entries
(k ↔ d - k) give CPT symmetry.

This file is 0-axiom, decide-checked throughout.  No real numbers.
-/

namespace E213.Lib.Physics.Simplex.FoccSpectrum

open E213.Lib.Physics.Simplex.Counts

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

/-- ★ f_occ spectrum master — distinct count, total multiplicity,
    Hodge-pair invariance, denominator/numerator bounds, Higgs
    dominance, and matter/confined identifications. -/
theorem focc_spectrum_master :
    -- 10 distinct entries
    spectrum.length = 10
    -- Sum of multiplicities: 4×5 + 4×10 + 50 + 26 = 146
    ∧ (spectrum.map (·.2)).foldl (· + ·) 0 = 146
    -- All denominators in slot/face counts {1, 2, 3, 4, 5}
    ∧ (∀ x ∈ spectrum,
         x.1.2 = 1 ∨ x.1.2 = 2 ∨ x.1.2 = 3
         ∨ x.1.2 = 4 ∨ x.1.2 = 5)
    -- Numerator bound x.num ≤ d
    ∧ (∀ x ∈ spectrum, x.1.1 ≤ d)
    -- Hodge pair (1, 5) ↔ (4, 5) same multiplicity
    ∧ (spectrum.get? 0).map (·.2) = (spectrum.get? 8).map (·.2)
    -- Hodge pair (2, 5) ↔ (3, 5) same multiplicity
    ∧ (spectrum.get? 3).map (·.2) = (spectrum.get? 5).map (·.2)
    -- Higgs entry dominant: 50
    ∧ (spectrum.get? 4).map (·.2) = some 50
    -- Matter ∧¹ multiplicity = d
    ∧ (spectrum.get? 0).map (·.2) = some d
    -- Confined entry = (1, 1)
    ∧ (spectrum.get? 9).map (·.1) = some (1, 1) := by decide

end E213.Lib.Physics.Simplex.FoccSpectrum
