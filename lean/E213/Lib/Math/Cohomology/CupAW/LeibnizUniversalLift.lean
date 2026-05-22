import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.Delta.Pointwise

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Leibniz universal lift template — G111 COH-3

Captures the structural pointwise-lift pattern shared by the 5
`leibniz_universal_*` proofs (5_1_1, 4_1_2, 4_2_2, +) in
`CupAW/Leibniz.lean` and `CupAW/Leibniz4Mixed.lean`.

Each universal lift body is a ~30-line `let` chain that, given α, β,
their patterns (pα, pβ), and a decide-checked
`leibniz_pattern_*` theorem, lifts to arbitrary α, β via two
`pattern_eq_at` chains through `cupAW_pointwise_eq` /
`delta_pointwise_eq`.

`leibniz_pointwise_lift` packages that lift: caller supplies
(α, β, pα, pβ, hα, hβ, h_pat) and gets back the universal Leibniz
equality at (α, β).  PURE.
-/

namespace E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.Pointwise (cupAW_pointwise_eq)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)

/-- ★ Generic Leibniz pointwise lift.  Given a pattern-level theorem
    `h_pat` at (pα, pβ) and pointwise equalities α ↔ pα, β ↔ pβ,
    conclude the universal Leibniz identity at (α, β).  PURE.

    Used by `leibniz_universal_{5_1_1, 4_1_2, 4_2_2, ...}` — each
    caller supplies the concrete (n, a, b) and the two pattern
    equalities from `Universal.Prop<NK>.pattern_eq_at`. -/
theorem leibniz_pointwise_lift
    (n a b : Nat)
    (α : Cochain n a) (β : Cochain n b)
    (pα : Cochain n a) (pβ : Cochain n b)
    (i_lhs : Fin (binom n (a + b - 1 + 1)))
    (i_rhs1 : Fin (binom n ((a+1) + b - 1)))
    (i_rhs2 : Fin (binom n (a + (b+1) - 1)))
    (hα : ∀ j, α j = pα j)
    (hβ : ∀ j, β j = pβ j)
    (h_pat : delta (cupAW n a b pα pβ) i_lhs
              = xor (cupAW n (a+1) b (delta pα) pβ i_rhs1)
                    (cupAW n a (b+1) pα (delta pβ) i_rhs2)) :
    delta (cupAW n a b α β) i_lhs
      = xor (cupAW n (a+1) b (delta α) β i_rhs1)
            (cupAW n a (b+1) α (delta β) i_rhs2) :=
  let hδα : ∀ j, delta α j = delta pα j :=
    fun j => delta_pointwise_eq α pα hα j
  let hδβ : ∀ j, delta β j = delta pβ j :=
    fun j => delta_pointwise_eq β pβ hβ j
  let h_cup : ∀ j, cupAW n a b α β j = cupAW n a b pα pβ j :=
    fun j => cupAW_pointwise_eq α pα β pβ hα hβ j
  let h_lhs : delta (cupAW n a b α β) i_lhs = delta (cupAW n a b pα pβ) i_lhs :=
    delta_pointwise_eq _ _ h_cup i_lhs
  let h_rhs1 : cupAW n (a+1) b (delta α) β i_rhs1
             = cupAW n (a+1) b (delta pα) pβ i_rhs1 :=
    cupAW_pointwise_eq (delta α) (delta pα) β pβ hδα hβ i_rhs1
  let h_rhs2 : cupAW n a (b+1) α (delta β) i_rhs2
             = cupAW n a (b+1) pα (delta pβ) i_rhs2 :=
    cupAW_pointwise_eq α pα (delta β) (delta pβ) hα hδβ i_rhs2
  let h_xor_eq : xor (cupAW n (a+1) b (delta pα) pβ i_rhs1)
                     (cupAW n a (b+1) pα (delta pβ) i_rhs2)
               = xor (cupAW n (a+1) b (delta α) β i_rhs1)
                     (cupAW n a (b+1) α (delta β) i_rhs2) :=
    by rw [h_rhs1, h_rhs2]
  h_lhs.trans (h_pat.trans h_xor_eq)

end E213.Lib.Math.Cohomology.CupAW.LeibnizUniversalLift
