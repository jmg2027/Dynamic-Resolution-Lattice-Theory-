import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.Bilinear
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Delta.Linear

/-!
# CupAW + δ value-level bilinear lemmas (∅-axiom)

Replacements for the funext-based `BilinearFunc.cupAW_add_*_eq` and
`delta_add_eq` rules used by `LeibnizAlgLift*` `simp only` chains.

Each lemma here is value-level (fixed output index `i`), uses
`Pointwise.cupAW_pointwise_eq` and `Delta.Pointwise.delta_pointwise_eq`
to lift the per-`j` distributivity through cupAW / delta — bypassing
funext entirely.
-/

namespace E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.Bilinear (cupAW_add_left cupAW_add_right)
open E213.Lib.Math.Cohomology.Delta.Linear (delta_add)
open E213.Lib.Math.Cohomology.CupAW.Pointwise (cupAW_pointwise_eq)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)

/-- δ pushed inside cupAW α (Cochain.add β β'): value-level (PURE)
    replacement for `delta_add_eq + cupAW_add_right_eq` simp chain. -/
theorem delta_cupAW_add_right (n a b : Nat)
    (α : Cochain n a) (β β' : Cochain n b)
    (i : Fin (binom n (a + b - 1 + 1))) :
    delta (cupAW n a b α (Cochain.add β β')) i
      = xor (delta (cupAW n a b α β) i) (delta (cupAW n a b α β') i) := by
  have h_pw : ∀ j, cupAW n a b α (Cochain.add β β') j
                 = Cochain.add (cupAW n a b α β) (cupAW n a b α β') j := by
    intro j
    show cupAW n a b α (Cochain.add β β') j
       = xor (cupAW n a b α β j) (cupAW n a b α β' j)
    exact cupAW_add_right n a b α β β' j
  have h_delta : delta (cupAW n a b α (Cochain.add β β')) i
               = delta (Cochain.add (cupAW n a b α β) (cupAW n a b α β')) i :=
    delta_pointwise_eq _ _ h_pw i
  rw [h_delta]
  exact delta_add n (a + b - 1) _ _ i

/-- δ pushed inside cupAW (Cochain.add α α') β: value-level. -/
theorem delta_cupAW_add_left (n a b : Nat)
    (α α' : Cochain n a) (β : Cochain n b)
    (i : Fin (binom n (a + b - 1 + 1))) :
    delta (cupAW n a b (Cochain.add α α') β) i
      = xor (delta (cupAW n a b α β) i) (delta (cupAW n a b α' β) i) := by
  have h_pw : ∀ j, cupAW n a b (Cochain.add α α') β j
                 = Cochain.add (cupAW n a b α β) (cupAW n a b α' β) j := by
    intro j
    show cupAW n a b (Cochain.add α α') β j
       = xor (cupAW n a b α β j) (cupAW n a b α' β j)
    exact cupAW_add_left n a b α α' β j
  have h_delta : delta (cupAW n a b (Cochain.add α α') β) i
               = delta (Cochain.add (cupAW n a b α β) (cupAW n a b α' β)) i :=
    delta_pointwise_eq _ _ h_pw i
  rw [h_delta]
  exact delta_add n (a + b - 1) _ _ i

/-- cupAW α (δ (Cochain.add β β')): pull δ across the add at value level. -/
theorem cupAW_delta_add_right (n a b : Nat)
    (α : Cochain n a) (β β' : Cochain n b)
    (i : Fin (binom n (a + (b + 1) - 1))) :
    cupAW n a (b + 1) α (delta (Cochain.add β β')) i
      = xor (cupAW n a (b + 1) α (delta β) i)
            (cupAW n a (b + 1) α (delta β') i) := by
  have h_pw : ∀ j, delta (Cochain.add β β') j
                 = Cochain.add (delta β) (delta β') j := by
    intro j
    show delta (Cochain.add β β') j = xor (delta β j) (delta β' j)
    exact delta_add n b β β' j
  have h_cup : cupAW n a (b + 1) α (delta (Cochain.add β β')) i
             = cupAW n a (b + 1) α (Cochain.add (delta β) (delta β')) i :=
    cupAW_pointwise_eq α α (delta (Cochain.add β β'))
      (Cochain.add (delta β) (delta β')) (fun _ => rfl) h_pw i
  rw [h_cup]
  exact cupAW_add_right n a (b + 1) α (delta β) (delta β') i

/-- cupAW (δ (Cochain.add α α')) β: pull δ across the add at value level. -/
theorem cupAW_delta_add_left (n a b : Nat)
    (α α' : Cochain n a) (β : Cochain n b)
    (i : Fin (binom n (a + 1 + b - 1))) :
    cupAW n (a + 1) b (delta (Cochain.add α α')) β i
      = xor (cupAW n (a + 1) b (delta α) β i)
            (cupAW n (a + 1) b (delta α') β i) := by
  have h_pw : ∀ j, delta (Cochain.add α α') j
                 = Cochain.add (delta α) (delta α') j := by
    intro j
    show delta (Cochain.add α α') j = xor (delta α j) (delta α' j)
    exact delta_add n a α α' j
  have h_cup : cupAW n (a + 1) b (delta (Cochain.add α α')) β i
             = cupAW n (a + 1) b (Cochain.add (delta α) (delta α')) β i :=
    cupAW_pointwise_eq (delta (Cochain.add α α'))
      (Cochain.add (delta α) (delta α')) β β h_pw (fun _ => rfl) i
  rw [h_cup]
  exact cupAW_add_left n (a + 1) b (delta α) (delta α') β i

end E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
