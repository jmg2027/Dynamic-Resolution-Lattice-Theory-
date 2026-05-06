import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Universal.Prop51

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cup.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# Cup Leibniz universal at (5, 1, 1) — AW cup version

Test if Alexander–Whitney cup with overlap satisfies Leibniz
universally at the (5, 1, 1) Δ⁴ vertex case, where the original
cup failed (per LeibnizFinding).

  ∀ α β : Cochain 5 1,
    δ(α ⌣AW β) = δα ⌣AW β  XOR  α ⌣AW δβ
  in Cochain 5 2.

Pattern enumeration: 32 × 32 = 1024 (α, β) pairs × 10 indices.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Universal.Prop51 (pattern)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.Cup.Core (cup)

set_option maxHeartbeats 16000000 in
/-- Leibniz on every pattern pair — decide-checked. -/
theorem leibniz_pattern_5_1_1 :
    ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
      ∀ i : Fin (binom 5 2),
        delta (cupAW 5 1 1 (pattern a0 a1 a2 a3 a4)
                              (pattern b0 b1 b2 b3 b4)) i
          = xor (cupAW 5 2 1 (delta (pattern a0 a1 a2 a3 a4))
                              (pattern b0 b1 b2 b3 b4) i)
                (cupAW 5 1 2 (pattern a0 a1 a2 a3 a4)
                              (delta (pattern b0 b1 b2 b3 b4)) i) := by
  decide

/-- ★★★ Universal Leibniz Prop-lift at (5, 1, 1) — AW cup.
    ∅-axiom — chains `pattern_eq_at` (pointwise, no funext) through
    `cupAW_pointwise_eq` and `delta_pointwise_eq` to lift the
    decide-checked pattern result to arbitrary α, β. -/
theorem leibniz_universal_5_1_1
    (α β : Cochain 5 1) (i : Fin (binom 5 2)) :
    delta (cupAW 5 1 1 α β) i
      = xor (cupAW 5 2 1 (delta α) β i)
            (cupAW 5 1 2 α (delta β) i) :=
  let pα := pattern (α ⟨0, by decide⟩) (α ⟨1, by decide⟩)
                    (α ⟨2, by decide⟩) (α ⟨3, by decide⟩)
                    (α ⟨4, by decide⟩)
  let pβ := pattern (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)
                    (β ⟨2, by decide⟩) (β ⟨3, by decide⟩)
                    (β ⟨4, by decide⟩)
  let hα : ∀ j, α j = pα j :=
    E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at α
  let hβ : ∀ j, β j = pβ j :=
    E213.Lib.Math.Cohomology.Universal.Prop51.pattern_eq_at β
  let hδα : ∀ j, delta α j = delta pα j :=
    fun j => E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
              α pα hα j
  let hδβ : ∀ j, delta β j = delta pβ j :=
    fun j => E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
              β pβ hβ j
  let h_cup : ∀ j, cupAW 5 1 1 α β j = cupAW 5 1 1 pα pβ j :=
    fun j => E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
              α pα β pβ hα hβ j
  let h_lhs : delta (cupAW 5 1 1 α β) i = delta (cupAW 5 1 1 pα pβ) i :=
    E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
      (cupAW 5 1 1 α β) (cupAW 5 1 1 pα pβ) h_cup i
  let h_rhs1 : cupAW 5 2 1 (delta α) β i = cupAW 5 2 1 (delta pα) pβ i :=
    E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
      (delta α) (delta pα) β pβ hδα hβ i
  let h_rhs2 : cupAW 5 1 2 α (delta β) i = cupAW 5 1 2 pα (delta pβ) i :=
    E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
      α pα (delta β) (delta pβ) hα hδβ i
  let h_pat := leibniz_pattern_5_1_1
                  (α ⟨0, by decide⟩) (α ⟨1, by decide⟩) (α ⟨2, by decide⟩)
                  (α ⟨3, by decide⟩) (α ⟨4, by decide⟩)
                  (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩)
                  (β ⟨3, by decide⟩) (β ⟨4, by decide⟩) i
  -- Goal: delta (cupAW α β) i = xor (cupAW (δα) β i) (cupAW α (δβ) i)
  -- Chain: LHS = delta (cupAW pα pβ) i [h_lhs]
  --            = xor (cupAW (δpα) pβ i) (cupAW pα (δpβ) i) [h_pat]
  -- Then bring back to original via congrArg on h_rhs1.symm, h_rhs2.symm.
  let h_xor_eq : xor (cupAW 5 2 1 (delta pα) pβ i) (cupAW 5 1 2 pα (delta pβ) i)
               = xor (cupAW 5 2 1 (delta α) β i) (cupAW 5 1 2 α (delta β) i) :=
    by rw [h_rhs1, h_rhs2]
  h_lhs.trans (h_pat.trans h_xor_eq)

end E213.Lib.Math.Cohomology.CupAW.Leibniz
