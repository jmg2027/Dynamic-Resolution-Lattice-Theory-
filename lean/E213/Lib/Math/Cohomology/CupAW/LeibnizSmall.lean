import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Universal.Prop31

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Cup.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# Cup Leibniz at small atomic substrates — AW cup

  ∀ α β : Cochain n 1, δ(α ⌣AW β) = δα ⌣AW β XOR α ⌣AW δβ

For n = 3: 8 × 8 = 64 pairs × 3 indices = 192 evals.
Confirms the AW overlap convention is consistent with Leibniz
across multiple atomic substrates.
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizSmall

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.Universal.Prop31 (pattern)
open E213.Lib.Math.Cohomology.Cup.Core (cup)

/-- Leibniz on every (3, 1, 1) pattern pair. -/
theorem leibniz_pattern_3_1_1 :
    ∀ a0 a1 a2 b0 b1 b2 : Bool,
      ∀ i : Fin (binom 3 2),
        delta (cupAW 3 1 1 (pattern a0 a1 a2)
                            (pattern b0 b1 b2)) i
          = xor (cupAW 3 2 1 (delta (pattern a0 a1 a2))
                              (pattern b0 b1 b2) i)
                (cupAW 3 1 2 (pattern a0 a1 a2)
                              (delta (pattern b0 b1 b2)) i) := by
  decide

/-- ★★★ Universal Leibniz Prop-lift at (3, 1, 1) — AW cup.
    ∅-axiom — chains `pattern_eq_at` (pointwise, no funext) through
    `cupAW_pointwise_eq` and `delta_pointwise_eq` to lift the
    decide-checked pattern result to arbitrary α, β. -/
theorem leibniz_universal_3_1_1
    (α β : Cochain 3 1) (i : Fin (binom 3 2)) :
    delta (cupAW 3 1 1 α β) i
      = xor (cupAW 3 2 1 (delta α) β i)
            (cupAW 3 1 2 α (delta β) i) :=
  let pα := pattern (α ⟨0, by decide⟩) (α ⟨1, by decide⟩)
                    (α ⟨2, by decide⟩)
  let pβ := pattern (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)
                    (β ⟨2, by decide⟩)
  let hα : ∀ j, α j = pα j :=
    E213.Lib.Math.Cohomology.Universal.Prop31.pattern_eq_at α
  let hβ : ∀ j, β j = pβ j :=
    E213.Lib.Math.Cohomology.Universal.Prop31.pattern_eq_at β
  let hδα : ∀ j, delta α j = delta pα j :=
    fun j => E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
              α pα hα j
  let hδβ : ∀ j, delta β j = delta pβ j :=
    fun j => E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
              β pβ hβ j
  let h_cup : ∀ j, cupAW 3 1 1 α β j = cupAW 3 1 1 pα pβ j :=
    fun j => E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
              α pα β pβ hα hβ j
  let h_lhs : delta (cupAW 3 1 1 α β) i = delta (cupAW 3 1 1 pα pβ) i :=
    E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
      (cupAW 3 1 1 α β) (cupAW 3 1 1 pα pβ) h_cup i
  let h_rhs1 : cupAW 3 2 1 (delta α) β i = cupAW 3 2 1 (delta pα) pβ i :=
    E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
      (delta α) (delta pα) β pβ hδα hβ i
  let h_rhs2 : cupAW 3 1 2 α (delta β) i = cupAW 3 1 2 pα (delta pβ) i :=
    E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
      α pα (delta β) (delta pβ) hα hδβ i
  let h_pat := leibniz_pattern_3_1_1
                  (α ⟨0, by decide⟩) (α ⟨1, by decide⟩) (α ⟨2, by decide⟩)
                  (β ⟨0, by decide⟩) (β ⟨1, by decide⟩) (β ⟨2, by decide⟩) i
  let h_xor_eq : xor (cupAW 3 2 1 (delta pα) pβ i) (cupAW 3 1 2 pα (delta pβ) i)
               = xor (cupAW 3 2 1 (delta α) β i) (cupAW 3 1 2 α (delta β) i) :=
    by rw [h_rhs1, h_rhs2]
  h_lhs.trans (h_pat.trans h_xor_eq)

end E213.Lib.Math.Cohomology.CupAW.LeibnizSmall
