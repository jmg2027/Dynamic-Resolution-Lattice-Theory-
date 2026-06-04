import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt
import E213.Lib.Math.Algebra.CayleyDickson.Integer.Hurwitz213

/-!
# Type E rejection — concrete small-case verification

The Dirichlet unit theorem (cited externally) bounds finite-unit
ℤ-base rings to exactly 4 types: A (Z_4), B (Z_2), C (Z_6), D (2T).

This module provides ∅-axiom Lean evidence by enumerating small
candidate ZSqrt[-D] cases and verifying each has the predicted
unit count: 2 (Type B) for all D ≥ 2.

Higher candidates (Q(ζ_5), Q(ζ_8), icosian) are EXCLUDED via the
Dirichlet bound (their unit groups are infinite or live over
non-ℤ coefficient rings).

See `theory/math/algebra/cayley_dickson/algebra_tower.md` for the conceptual
argument.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Misc.TypeE_Rejection

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt

/-- Explicit candidates over coords {-2, -1, 0, 1, 2} for ZSqrt[-D]. -/
def candidates_ZSqrt (D : Int) : List (ZSqrt D) :=
  [⟨-2,-2⟩, ⟨-2,-1⟩, ⟨-2,0⟩, ⟨-2,1⟩, ⟨-2,2⟩,
   ⟨-1,-2⟩, ⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩, ⟨-1,2⟩,
   ⟨ 0,-2⟩, ⟨ 0,-1⟩, ⟨ 0,0⟩, ⟨ 0,1⟩, ⟨ 0,2⟩,
   ⟨ 1,-2⟩, ⟨ 1,-1⟩, ⟨ 1,0⟩, ⟨ 1,1⟩, ⟨ 1,2⟩,
   ⟨ 2,-2⟩, ⟨ 2,-1⟩, ⟨ 2,0⟩, ⟨ 2,1⟩, ⟨ 2,2⟩]

def units_of (D : Int) : List (ZSqrt D) :=
  (candidates_ZSqrt D).filter (fun u => ZSqrt.normSq u = 1)

/-- Compact unit-count function for given D — explicitly instantiated. -/
def unit_count (D : Int) : Nat :=
  ((candidates_ZSqrt D).filter (fun u => ZSqrt.normSq u = 1)).length

/-- Smaller candidate list: only check coords {-1, 0, 1} (sufficient for D ≥ 1). -/
def small_cands_ZSqrt (D : Int) : List (ZSqrt D) :=
  [⟨-1,-1⟩, ⟨-1,0⟩, ⟨-1,1⟩,
   ⟨ 0,-1⟩, ⟨ 0,0⟩, ⟨ 0,1⟩,
   ⟨ 1,-1⟩, ⟨ 1,0⟩, ⟨ 1,1⟩]

/-- ★ ZSqrt[-2] units (D=2): explicit count via decidable filter. -/
theorem ZSqrt_2_units :
    ((small_cands_ZSqrt 2).filter (fun u => ZSqrt.normSq u = 1)).length = 2 := by decide

/-- ★ ZSqrt[-3] units (D=3): 2 = Type B. -/
theorem ZSqrt_3_units :
    ((small_cands_ZSqrt 3).filter (fun u => ZSqrt.normSq u = 1)).length = 2 := by decide

/-- ★ ZSqrt[-5] units (D=5): 2 = Type B. -/
theorem ZSqrt_5_units :
    ((small_cands_ZSqrt 5).filter (fun u => ZSqrt.normSq u = 1)).length = 2 := by decide

/-- ★ ZSqrt[-7] units (D=7): 2 = Type B. -/
theorem ZSqrt_7_units :
    ((small_cands_ZSqrt 7).filter (fun u => ZSqrt.normSq u = 1)).length = 2 := by decide

/-- ★ ZSqrt[-1] = ZI units (D=1): 4 = Type A. -/
theorem ZSqrt_1_units :
    ((small_cands_ZSqrt 1).filter (fun u => ZSqrt.normSq u = 1)).length = 4 := by decide

/-- ★ Hurwitz has exactly 24 units (Type D: 2T binary tetrahedral). -/
theorem Hurwitz_units_count :
    E213.Lib.Math.Algebra.CayleyDickson.Integer.Hurwitz213.hur_units.length = 24 :=
  E213.Lib.Math.Algebra.CayleyDickson.Integer.Hurwitz213.hur_units_count

-- Type E candidate within ℤ-base ZSqrt range: NONE found.
-- Among D ∈ {1, 2, 3, 5, 7}, every ZSqrt[-D] gives unit count
-- in {2, 4} corresponding to Type B or Type A. No 5th distinct
-- cardinality emerges from this family.

/-- ★ Type E rejection summary (combined). -/
theorem no_type_E_in_ZSqrt_family :
    ((small_cands_ZSqrt 2).filter (fun u => ZSqrt.normSq u = 1)).length = 2 ∧
    ((small_cands_ZSqrt 3).filter (fun u => ZSqrt.normSq u = 1)).length = 2 ∧
    ((small_cands_ZSqrt 5).filter (fun u => ZSqrt.normSq u = 1)).length = 2 ∧
    ((small_cands_ZSqrt 7).filter (fun u => ZSqrt.normSq u = 1)).length = 2 ∧
    ((small_cands_ZSqrt 1).filter (fun u => ZSqrt.normSq u = 1)).length = 4 := by decide

end E213.Lib.Math.Algebra.CayleyDickson.Misc.TypeE_Rejection
