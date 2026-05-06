import E213.Lib.Math.Cohomology.Delta.Core

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.SimplexBasis
import E213.Lib.Physics.Simplex.Counts
/-!
# Coboundary δ — pointwise extensionality (∅-axiom)

`delta σ i` only depends on σ at finitely many evaluation points
(the faces of the (k+1)-subset at index `i.val`).  This file
proves a 213-native pointwise-extensionality lemma that lets us
substitute σ by τ whenever `∀ j, σ j = τ j` — bypassing `funext`
(which leaks `propext` + `Quot.sound`).

Used to lift `Universal.Prop5k.dsq_pattern` (decide-checked over
Bool patterns) to `dsq_zero_prop_5_k : ∀ σ : Cochain 5 k, ...`
without relying on the funext-based `pattern_eq σ : σ = pattern …`.
-/

namespace E213.Lib.Math.Cohomology.Delta.Pointwise

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Delta.Core (delta deltaAt subsetIdx)
open E213.Lib.Math.Cohomology.SimplexBasis (kSubset)

/-- `List.foldl` is pointwise-extensional in its step function.
    ∅-axiom — structural recursion + `Eq.subst` (▸). -/
theorem foldl_step_eq {α β : Type}
    (f g : β → α → β) (heq : ∀ b a, f b a = g b a) :
    ∀ (l : List α) (init : β), l.foldl f init = l.foldl g init
  | [], _ => rfl
  | hd :: tl, init =>
    show tl.foldl f (f init hd) = tl.foldl g (g init hd) from
    have step : f init hd = g init hd := heq init hd
    have rest : tl.foldl g (f init hd) = tl.foldl g (g init hd) :=
      step ▸ rfl
    (foldl_step_eq f g heq tl (f init hd)).trans rest

/-- `deltaAt n k σ τ_idx` depends on σ only at the face indices —
    given pointwise-equal σ, τ, the values agree.  ∅-axiom. -/
theorem deltaAt_pointwise_eq {n k : Nat} (σ τ : Cochain n k)
    (h : ∀ j, σ j = τ j) (τ_idx : Nat) :
    deltaAt n k σ τ_idx = deltaAt n k τ τ_idx := by
  show (List.range (k + 1)).foldl _ false
       = (List.range (k + 1)).foldl _ false
  apply foldl_step_eq
  intro acc i
  let f_idx := subsetIdx n k ((kSubset n (k+1) τ_idx).eraseIdx i)
  show (if hf : f_idx < binom n k
        then xor acc (σ ⟨f_idx, hf⟩) else acc)
       = (if hf : f_idx < binom n k
          then xor acc (τ ⟨f_idx, hf⟩) else acc)
  match h_dec : decide (f_idx < binom n k) with
  | true =>
    have hf : f_idx < binom n k := of_decide_eq_true h_dec
    rw [dif_pos hf, dif_pos hf, h ⟨f_idx, hf⟩]
  | false =>
    have hf : ¬ f_idx < binom n k := of_decide_eq_false h_dec
    rw [dif_neg hf, dif_neg hf]

/-- ★ `delta` is pointwise-extensional.  ∅-axiom replacement for
    `funext`-based reduction `σ = τ → delta σ = delta τ`. -/
theorem delta_pointwise_eq {n k : Nat} (σ τ : Cochain n k)
    (h : ∀ j, σ j = τ j) (i : Fin (binom n (k + 1))) :
    delta σ i = delta τ i :=
  deltaAt_pointwise_eq σ τ h i.val

end E213.Lib.Math.Cohomology.Delta.Pointwise
