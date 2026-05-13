import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Universal.Prop41
import E213.Lib.Math.Cohomology.Universal.Prop42

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Physics.Simplex.Counts
/-!
# Cup AW Leibniz at mixed arities on Δ³ (n = 4)

  - (4, 1, 2): 16 × 64 = 1024 pattern pairs × 4 indices
  - (4, 2, 1): 64 × 16 = 1024 pattern pairs × 4 indices
  - (4, 2, 2): 64 × 64 = 4096 pattern pairs × 1 index

Each fits comfortably in a single Prop-level decide.
Together with (4, 1, 1) and (3, 1, 1), this closes Cup Leibniz
universal across all interior strata of Δ², Δ³.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Leibniz4Mixed

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Lib.Math.Cohomology.Universal.Prop41 (pattern)
open E213.Lib.Math.Cohomology.Universal.Prop42 renaming pattern → patternE

set_option maxHeartbeats 16000000 in
/-- ★ Pattern-level Leibniz at (4, 1, 2). -/
theorem leibniz_pattern_4_1_2 :
    ∀ a0 a1 a2 a3 : Bool,
      ∀ b0 b1 b2 b3 b4 b5 : Bool,
      ∀ i : Fin (binom 4 3),
        delta (cupAW 4 1 2 (pattern a0 a1 a2 a3)
                            (patternE b0 b1 b2 b3 b4 b5)) i
          = xor (cupAW 4 2 2 (delta (pattern a0 a1 a2 a3))
                              (patternE b0 b1 b2 b3 b4 b5) i)
                (cupAW 4 1 3 (pattern a0 a1 a2 a3)
                              (delta (patternE b0 b1 b2 b3 b4 b5)) i) := by
  decide

/-- ★★★ Universal Leibniz Prop-lift at (4, 1, 2).
    ∅-axiom — chains pattern_eq_at (Prop41 + Prop42) through
    cupAW/delta_pointwise_eq.  No funext. -/
theorem leibniz_universal_4_1_2
    (α : Cochain 4 1) (β : Cochain 4 2) (i : Fin (binom 4 3)) :
    delta (cupAW 4 1 2 α β) i
      = xor (cupAW 4 2 2 (delta α) β i)
            (cupAW 4 1 3 α (delta β) i) :=
  let pα := pattern (α ⟨0, by decide⟩) (α ⟨1, by decide⟩)
                    (α ⟨2, by decide⟩) (α ⟨3, by decide⟩)
  let pβ := patternE (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)
                     (β ⟨2, by decide⟩) (β ⟨3, by decide⟩)
                     (β ⟨4, by decide⟩) (β ⟨5, by decide⟩)
  let hα : ∀ j, α j = pα j :=
    E213.Lib.Math.Cohomology.Universal.Prop41.pattern_eq_at α
  let hβ : ∀ j, β j = pβ j :=
    E213.Lib.Math.Cohomology.Universal.Prop42.pattern_eq_at β
  let hδα : ∀ j, delta α j = delta pα j :=
    fun j => E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
              α pα hα j
  let hδβ : ∀ j, delta β j = delta pβ j :=
    fun j => E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
              β pβ hβ j
  let h_cup : ∀ j, cupAW 4 1 2 α β j = cupAW 4 1 2 pα pβ j :=
    fun j => E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
              α pα β pβ hα hβ j
  let h_lhs : delta (cupAW 4 1 2 α β) i = delta (cupAW 4 1 2 pα pβ) i :=
    E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
      (cupAW 4 1 2 α β) (cupAW 4 1 2 pα pβ) h_cup i
  let h_rhs1 : cupAW 4 2 2 (delta α) β i = cupAW 4 2 2 (delta pα) pβ i :=
    E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
      (delta α) (delta pα) β pβ hδα hβ i
  let h_rhs2 : cupAW 4 1 3 α (delta β) i = cupAW 4 1 3 pα (delta pβ) i :=
    E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
      α pα (delta β) (delta pβ) hα hδβ i
  let h_pat := leibniz_pattern_4_1_2
                  (α ⟨0, by decide⟩) (α ⟨1, by decide⟩)
                  (α ⟨2, by decide⟩) (α ⟨3, by decide⟩)
                  (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)
                  (β ⟨2, by decide⟩) (β ⟨3, by decide⟩)
                  (β ⟨4, by decide⟩) (β ⟨5, by decide⟩) i
  let h_xor_eq : xor (cupAW 4 2 2 (delta pα) pβ i) (cupAW 4 1 3 pα (delta pβ) i)
               = xor (cupAW 4 2 2 (delta α) β i) (cupAW 4 1 3 α (delta β) i) :=
    by rw [h_rhs1, h_rhs2]
  h_lhs.trans (h_pat.trans h_xor_eq)

set_option maxHeartbeats 16000000 in
/-- ★ Pattern-level Leibniz at (4, 2, 2). -/
theorem leibniz_pattern_4_2_2 :
    ∀ a0 a1 a2 a3 a4 a5 : Bool,
      ∀ b0 b1 b2 b3 b4 b5 : Bool,
      ∀ i : Fin (binom 4 4),
        delta (cupAW 4 2 2 (patternE a0 a1 a2 a3 a4 a5)
                            (patternE b0 b1 b2 b3 b4 b5)) i
          = xor (cupAW 4 3 2 (delta (patternE a0 a1 a2 a3 a4 a5))
                              (patternE b0 b1 b2 b3 b4 b5) i)
                (cupAW 4 2 3 (patternE a0 a1 a2 a3 a4 a5)
                              (delta (patternE b0 b1 b2 b3 b4 b5)) i) := by
  decide

/-- ★★★ Universal Leibniz Prop-lift at (4, 2, 2).
    ∅-axiom — same template as 4_1_2, both via Prop42.pattern_eq_at. -/
theorem leibniz_universal_4_2_2
    (α β : Cochain 4 2) (i : Fin (binom 4 4)) :
    delta (cupAW 4 2 2 α β) i
      = xor (cupAW 4 3 2 (delta α) β i)
            (cupAW 4 2 3 α (delta β) i) :=
  let pα := patternE (α ⟨0, by decide⟩) (α ⟨1, by decide⟩)
                     (α ⟨2, by decide⟩) (α ⟨3, by decide⟩)
                     (α ⟨4, by decide⟩) (α ⟨5, by decide⟩)
  let pβ := patternE (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)
                     (β ⟨2, by decide⟩) (β ⟨3, by decide⟩)
                     (β ⟨4, by decide⟩) (β ⟨5, by decide⟩)
  let hα : ∀ j, α j = pα j :=
    E213.Lib.Math.Cohomology.Universal.Prop42.pattern_eq_at α
  let hβ : ∀ j, β j = pβ j :=
    E213.Lib.Math.Cohomology.Universal.Prop42.pattern_eq_at β
  let hδα : ∀ j, delta α j = delta pα j :=
    fun j => E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
              α pα hα j
  let hδβ : ∀ j, delta β j = delta pβ j :=
    fun j => E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
              β pβ hβ j
  let h_cup : ∀ j, cupAW 4 2 2 α β j = cupAW 4 2 2 pα pβ j :=
    fun j => E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
              α pα β pβ hα hβ j
  let h_lhs : delta (cupAW 4 2 2 α β) i = delta (cupAW 4 2 2 pα pβ) i :=
    E213.Lib.Math.Cohomology.Delta.Pointwise.delta_pointwise_eq
      (cupAW 4 2 2 α β) (cupAW 4 2 2 pα pβ) h_cup i
  let h_rhs1 : cupAW 4 3 2 (delta α) β i = cupAW 4 3 2 (delta pα) pβ i :=
    E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
      (delta α) (delta pα) β pβ hδα hβ i
  let h_rhs2 : cupAW 4 2 3 α (delta β) i = cupAW 4 2 3 pα (delta pβ) i :=
    E213.Lib.Math.Cohomology.CupAW.Pointwise.cupAW_pointwise_eq
      α pα (delta β) (delta pβ) hα hδβ i
  let h_pat := leibniz_pattern_4_2_2
                  (α ⟨0, by decide⟩) (α ⟨1, by decide⟩)
                  (α ⟨2, by decide⟩) (α ⟨3, by decide⟩)
                  (α ⟨4, by decide⟩) (α ⟨5, by decide⟩)
                  (β ⟨0, by decide⟩) (β ⟨1, by decide⟩)
                  (β ⟨2, by decide⟩) (β ⟨3, by decide⟩)
                  (β ⟨4, by decide⟩) (β ⟨5, by decide⟩) i
  let h_xor_eq : xor (cupAW 4 3 2 (delta pα) pβ i) (cupAW 4 2 3 pα (delta pβ) i)
               = xor (cupAW 4 3 2 (delta α) β i) (cupAW 4 2 3 α (delta β) i) :=
    by rw [h_rhs1, h_rhs2]
  h_lhs.trans (h_pat.trans h_xor_eq)

end E213.Lib.Math.Cohomology.CupAW.Leibniz4Mixed
