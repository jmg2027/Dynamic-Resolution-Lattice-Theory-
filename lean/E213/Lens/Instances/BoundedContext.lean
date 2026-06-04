/-!
# Lens.Instances.BoundedContext — bounded-context lens

The pattern that makes `cutMulOuter_congr` and `cutSumAux_congr`
work as the engine of the funext refactor.  A function (possibly
infinite-domain) is viewed only through its **values within a
bounded query window** [0, N] — outside the window doesn't matter.

Concrete realisation:

  - For `cutMulOuter cx cy k m m2Bound n` (E213.Lib.Math.NumberSystems.Real213.Mul.CutMul),
    the relevant query window for `(m, k)` evaluation is `n ≤
    (m+1)*(k+1)`.  `cutMulOuter_congr` says: if `cx`, `cy` agree
    pointwise on this window, the outer aggregator gives identical
    results.
  - Similarly for `cutSumAux_congr` over `2*m`-wide window.

This lens enables pointwise IH propagation through recursive cut
operations without requiring full function equality.

Used heavily in: `cutMul_one_one_at`, `mvt_passthrough_unit_at`,
`Passthrough_at.mul_pass`, etc.
-/

namespace E213.Lens.Instances.BoundedContext

/-- The bounded view: function `f : Nat → α` projected to its
    values on `[0, N]`. -/
def project (N : Nat) (α : Type) (f : Nat → α) : Fin (N + 1) → α :=
  fun i => f i.val

/-- Bounded equivalence: two functions agree on the window `[0, N]`. -/
def boundedEq (N : Nat) {α : Type} (f g : Nat → α) : Prop :=
  ∀ i : Fin (N + 1), f i.val = g i.val

theorem boundedEq_refl (N : Nat) {α : Type} (f : Nat → α) :
    boundedEq N f f := fun _ => rfl

theorem boundedEq_symm {N : Nat} {α : Type} {f g : Nat → α}
    (h : boundedEq N f g) : boundedEq N g f := fun i => (h i).symm

theorem boundedEq_trans {N : Nat} {α : Type} {f g h : Nat → α}
    (hfg : boundedEq N f g) (hgh : boundedEq N g h) :
    boundedEq N f h := fun i => (hfg i).trans (hgh i)

end E213.Lens.Instances.BoundedContext
