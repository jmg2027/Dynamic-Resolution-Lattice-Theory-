import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cochain.V5_3Decomp
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz

/-!
# Bridge helpers for bz5_3 case-splits

Pointwise PURE companions to V5_3Decomp.bz5_3, expressing the
on/off behavior of `bz5_3 β k` under hypotheses on `β k`.

Used in the per-α-component case-split for (5, 3, _) Leibniz
universal lifts.  Sister of `Leibniz22Bridge` (bz5_2 at codim-2)
and `Leibniz21Bridge` (bz5_1 at codim-1).

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1Bridge

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Cochain.V5_3Decomp (bz5_3)

/-- Pointwise (PURE): bz5_3 β k j = false (= Cochain.zero 5 3 j)
    when β k = false. -/
theorem bz5_3_false_at (β : Cochain 5 3) (k : Fin 10)
    (hβ : β k = false) (j : Fin 10) :
    bz5_3 β k j = Cochain.zero 5 3 j := by
  show ((k.val == j.val) && β k) = false
  rw [hβ]
  show ((k.val == j.val) && false) = false
  cases (k.val == j.val) <;> rfl

/-- Pointwise (PURE): bz5_3 β k j = basis 5 3 k j when β k = true. -/
theorem bz5_3_true_at (β : Cochain 5 3) (k : Fin 10)
    (hβ : β k = true) (j : Fin 10) :
    bz5_3 β k j = basis 5 3 k j := by
  show ((k.val == j.val) && β k) = basis 5 3 k j
  rw [hβ]
  show ((k.val == j.val) && true) = (k.val == j.val)
  cases (k.val == j.val) <;> rfl

end E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1Bridge
