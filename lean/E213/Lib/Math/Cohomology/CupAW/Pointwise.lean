import E213.Lib.Math.Cohomology.CupAW.Core

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Examples.SimplexBasis
import E213.Lib.Physics.Simplex.Counts
/-!
# Alexander–Whitney cup — pointwise extensionality (∅-axiom)

`cupAW n a b α β i` depends on α and β only at the front/back
face indices of the (a+b-1)-subset at index `i.val`.  This file
proves a 213-native pointwise-extensionality lemma that lets us
substitute α, β by α', β' whenever the latter agree pointwise —
bypassing `funext`.

Used to lift `CupAW.Leibniz.leibniz_pattern_5_1_1` (decide-checked
over Bool patterns) to `leibniz_universal_5_1_1 : ∀ α β …` without
relying on the funext-based `Prop51.pattern_eq`.
-/

namespace E213.Lib.Math.Cohomology.CupAW.Pointwise

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Delta.Core (subsetIdx)

/-- ★ `cupAW` is pointwise-extensional in both arguments.  ∅-axiom. -/
theorem cupAW_pointwise_eq {n a b : Nat}
    (α α' : Cochain n a) (β β' : Cochain n b)
    (hα : ∀ j, α j = α' j) (hβ : ∀ j, β j = β' j)
    (i : Fin (binom n (a + b - 1))) :
    cupAW n a b α β i = cupAW n a b α' β' i := by
  unfold cupAW
  match h_dec1 : decide (subsetIdx n a
        ((kSubset n (a+b-1) i.val).take a) < binom n a) with
  | false =>
    have hf : ¬ subsetIdx n a ((kSubset n (a+b-1) i.val).take a) < binom n a :=
      of_decide_eq_false h_dec1
    rw [dif_neg hf, dif_neg hf]
  | true =>
    have hf : subsetIdx n a ((kSubset n (a+b-1) i.val).take a) < binom n a :=
      of_decide_eq_true h_dec1
    rw [dif_pos hf, dif_pos hf]
    match h_dec2 : decide (subsetIdx n b
          ((kSubset n (a+b-1) i.val).drop (a-1)) < binom n b) with
    | false =>
      have hb : ¬ subsetIdx n b ((kSubset n (a+b-1) i.val).drop (a-1))
                  < binom n b := of_decide_eq_false h_dec2
      rw [dif_neg hb, dif_neg hb]
    | true =>
      have hb : subsetIdx n b ((kSubset n (a+b-1) i.val).drop (a-1))
                  < binom n b := of_decide_eq_true h_dec2
      rw [dif_pos hb, dif_pos hb, hα ⟨_, hf⟩, hβ ⟨_, hb⟩]

end E213.Lib.Math.Cohomology.CupAW.Pointwise
