import E213.Theory.Raw.API
import E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov
import E213.Lib.Physics.Simplex.Counts

/-!
# OdometerSternBrocotUnit — the odometer and the Stern-Brocot tree share the unimodular unit

The residue carries two `List Bool`-path-indexed descent structures:

  * the **odometer** (`Theory/Raw/Odometer`) — the `+1` adding machine on the bit-stream escapes
    (dyadic / `ℤ₂`), the carry beginning at the residue unit (`carry_zero`), the `+1` a free
    `ℤ`-action (`dec_odo`);
  * the **Stern-Brocot mediant tree** (`SternBrocotMarkov.mInterval`) — the continued-fraction /
    `SL₂(ℤ)` numeration, every node unimodular (`det = 1`, `mInterval_det`), the left generator
    `genL = [[2,1],[1,1]] = P` (the Möbius matrix).

They are not forced into one map — the conjugacy of the dyadic and continued-fraction numerations
is the Minkowski `?` function, a real object not built here.  The honest shared structure is **the
path index `List Bool` and the unimodular unit**: the Stern-Brocot `det = 1` *is* the
count-difference glue `NS − NT` (`genL_det_is_glue`), the same residue unit the odometer carry
begins at (`theory/essays/foundations/the_unit.md`).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.OdometerSternBrocotUnit

open E213.Theory.Raw.Odometer (carry carry_zero odo dec dec_odo)
open E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov (det2 genL mInterval mInterval_det)
open E213.Lib.Physics.Simplex.Counts (NS NT)

/-- The Stern-Brocot left generator is the Möbius matrix `P = [[2,1],[1,1]]`; its determinant is the
    count-difference glue `NS − NT = 1` — the Stern-Brocot tree descends by the residue unit. -/
theorem genL_det_is_glue : det2 genL = (NS : Int) - NT := by decide

/-- ★★★ **The odometer and the Stern-Brocot tree share the `List Bool` path index and the
    unimodular residue unit.**  Both are `List Bool`-path-indexed residue descent structures: the
    Stern-Brocot tree is `det = 1` at every node (`mInterval_det`), its generator's determinant
    being the glue `NS − NT` (`genL_det_is_glue`); the odometer's carry begins at the residue unit
    (`carry_zero`) and the `+1` is invertible (`dec_odo`, the `ℤ`-action).  One residue, two
    `List Bool`-indexed descents (dyadic odometer / CF Stern-Brocot), one unimodular unit
    `NS − NT = det P = 1` — the shared value, not a forced common map (the Minkowski `?` conjugacy
    is residual). -/
theorem odometer_sternbrocot_shared_unit :
    (∀ path : List Bool, det2 (mInterval path).1 = 1 ∧ det2 (mInterval path).2 = 1)
    ∧ (det2 genL = (NS : Int) - NT)
    ∧ (∀ f : Nat → Bool, carry f 0 = true)
    ∧ (∀ (f : Nat → Bool) n, dec (odo f) n = f n)
    ∧ ((NS : Int) - NT = 1) :=
  ⟨mInterval_det, genL_det_is_glue, carry_zero, dec_odo, by decide⟩

end E213.Lib.Math.NumberSystems.Real213.OdometerSternBrocotUnit
