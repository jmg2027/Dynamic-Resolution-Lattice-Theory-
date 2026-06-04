import E213.Lens.Lattice.Lattice
import E213.Lens.Lattice.Meet

/-!
# `IsInjectiveLens` — the injectivity layer of the refinement lattice

A Lens is **injective** when its `view` distinguishes every pair of Raws.  By
`refines_idLens_iff_injective`, injectivity is exactly *refining the identity Lens* `idLens` (the bottom
of the refinement order), so it is monotone *down* the order and inherited by meets, while the constant
Lens (the top) is maximally lossy.

This is the `∅`-axiom skeleton of the "Lens injectivity hierarchy"
(`seed/AXIOM/06_lens_readings.md` §6.7), and the frame in which the Markov slope/size readings sit:
"a reading is injective" = "it refines `idLens`"; the slope reading is injective at the oriented level
(`slope_path_inj`), and the size reading's injectivity is exactly the open kernel `H`
(`SternBrocotMarkov.markovMaxUnique_iff_orbitRealizabilityH`).
-/

namespace E213.Lens.Lattice.Injectivity

open E213.Theory E213.Lens
open E213.Lens.Instances.Identity
open E213.Lens.Lattice.Lattice
open E213.Lens.Lattice.Meet

/-- A Lens is **injective** when its `view` is injective — equivalently, its kernel is trivial (`=`). -/
def IsInjectiveLens {α : Type} (L : Lens α) : Prop := Function.Injective L.view

/-- **Injectivity = refining the identity Lens** (the bottom of the refinement order). -/
theorem isInjectiveLens_iff_refines_idLens {α : Type} (L : Lens α) :
    IsInjectiveLens L ↔ L.refines idLens :=
  (refines_idLens_iff_injective L).symm

/-- The identity Lens is injective — the canonical injective reading. -/
theorem isInjectiveLens_idLens : IsInjectiveLens idLens := by
  intro x y h
  rw [idLens_is_id, idLens_is_id] at h
  exact h

/-- ★★★★ **Monotone down the order**: a Lens refining an injective Lens is injective.  If `L.refines M`
    and `M` is injective, then `L`'s kernel is contained in `M`'s trivial kernel, so `L` is injective. -/
theorem isInjectiveLens_of_refines {α β : Type} {L : Lens α} {M : Lens β}
    (hLM : L.refines M) (hM : IsInjectiveLens M) : IsInjectiveLens L :=
  (isInjectiveLens_iff_refines_idLens L).mpr
    (Lens.refines_trans hLM ((isInjectiveLens_iff_refines_idLens M).mp hM))

/-- **Meet preserves injectivity**: if either factor is injective, the product (meet) is injective —
    the meet refines each factor. -/
theorem isInjectiveLens_prodLens_left {α β : Type} (L : Lens α) (M : Lens β)
    (hLsym : ∀ u v, L.combine u v = L.combine v u)
    (hMsym : ∀ u v, M.combine u v = M.combine v u)
    (hL : IsInjectiveLens L) : IsInjectiveLens (prodLens L M) :=
  isInjectiveLens_of_refines (prodLens_refines_fst L M hLsym hMsym) hL

/-- The **constant Lens is not injective** (Raw has the distinct atoms `a ≠ b`): the top of the
    refinement order is maximally lossy — it forgets every distinction. -/
theorem not_isInjectiveLens_constLens {α : Type} (e : α) :
    ¬ IsInjectiveLens (constLens e) := by
  intro hinj
  have hab : (Raw.a : Raw) = Raw.b :=
    hinj (by rw [constLens_view, constLens_view])
  exact absurd hab (by decide)

end E213.Lens.Lattice.Injectivity
