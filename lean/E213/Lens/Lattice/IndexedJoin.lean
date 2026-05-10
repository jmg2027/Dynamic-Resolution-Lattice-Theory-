import E213.Lens.LensCore
import E213.Theory.Raw.Fold
import E213.Theory.Raw.Rec
import E213.Lens.Lattice.JoinEquiv

/-!
# IndexedJoinLens: indexed-product (meet) Lens

The indexed *meet* — `iProdLens F` — over an arbitrary family
`{L_i}_{i ∈ I}`.  Codomain: dependent function space `(i : ι) → β i`.

The corresponding indexed *join* (`iJoinLens`) was removed under the
"design-by-funext/propext 금지" directive: it was constructed via
`universalLens (IJoinEquiv F) : Lens (Raw → Prop)` whose kernel
equality required propext + funext on Raw → Prop.

`IJoinEquiv` itself (the relation) was kept in `Lattice.JoinEquiv`
since it's an inductive Prop, not propext-tainted.
-/

namespace E213.Lens.Lattice.IndexedJoin

open E213.Theory E213.Theory.Internal E213.Lens

/-- **Indexed product Lens (meet)**: concrete meet of an arbitrary
    family `{L_i}` — codomain is the dependent function space.
    Each component is extracted as the view of (F i).2. -/
def iProdLens {ι : Type} (F : ι → (α : Type) × Lens α) :
    Lens ((i : ι) → (F i).1) where
  base_a := fun i => (F i).2.base_a
  base_b := fun i => (F i).2.base_b
  combine := fun f g i => (F i).2.combine (f i) (g i)

/-- iProdLens.view is a **pointwise** application — stated at each index `i`
    to avoid funext on the dependent function space `(j : ι) → (F j).1`.
    Pointwise sym `hAllSym` of each L_i suffices. -/
theorem iProdLens_view {ι : Type} (F : ι → (α : Type) × Lens α)
    (hAllSym : ∀ i (u v : (F i).1),
                (F i).2.combine u v = (F i).2.combine v u)
    (r : Raw) (i : ι) :
    (iProdLens F).view r i = (F i).2.view r := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      -- Reduce (F i).2.view on the slash via Raw.fold_slash with pointwise sym.
      have hL_fs : (F i).2.view (Raw.slash x y h)
                    = (F i).2.combine ((F i).2.view x) ((F i).2.view y) :=
        Raw.fold_slash _ _ _ (hAllSym i) x y h
      rw [hL_fs, ← ihx, ← ihy]
      -- Now reduce (iProdLens F).view on the slash by Raw/Tree.fold unfold,
      -- splitting on canonical-form cmp.  Funext-free.
      show (Raw.fold (iProdLens F).base_a (iProdLens F).base_b
              (iProdLens F).combine (Raw.slash x y h)) i
        = (F i).2.combine
            ((Raw.fold (iProdLens F).base_a (iProdLens F).base_b
                (iProdLens F).combine x) i)
            ((Raw.fold (iProdLens F).base_a (iProdLens F).base_b
                (iProdLens F).combine y) i)
      unfold Raw.slash Raw.fold
      split <;> rename_i hc
      · rfl
      · -- gt branch: the canonical form swaps x.val/y.val; pointwise sym
        -- on (F i).2.combine recovers the un-swapped form.
        show (F i).2.combine
              ((Tree.fold (iProdLens F).base_a (iProdLens F).base_b
                  (iProdLens F).combine y.val) i)
              ((Tree.fold (iProdLens F).base_a (iProdLens F).base_b
                  (iProdLens F).combine x.val) i)
            = (F i).2.combine
                ((Tree.fold (iProdLens F).base_a (iProdLens F).base_b
                    (iProdLens F).combine x.val) i)
                ((Tree.fold (iProdLens F).base_a (iProdLens F).base_b
                    (iProdLens F).combine y.val) i)
        exact hAllSym i _ _
      · exact absurd (Tree.cmp_eq_to_eq _ _ hc)
          (fun e => h (Subtype.ext e))

/-- iProdLens refines each L_i — lower bound.  Uses pointwise `iProdLens_view`. -/
theorem iProdLens_refines_each {ι : Type} (F : ι → (α : Type) × Lens α)
    (hAllSym : ∀ i (u v : (F i).1),
                (F i).2.combine u v = (F i).2.combine v u)
    (i : ι) :
    (iProdLens F).refines (F i).2 := by
  intro r r' h
  show (F i).2.view r = (F i).2.view r'
  have hview : (iProdLens F).view r = (iProdLens F).view r' := h
  -- Project to index i via the pointwise view lemma.
  rw [← iProdLens_view F hAllSym r i,
      ← iProdLens_view F hAllSym r' i, hview]

/-- **iProdLens universal property (greatest lower bound)**, stated
    **pointwise at each index** to avoid `funext` on the dependent
    function-space codomain.  Consumers needing the function-eq form
    of `L.refines (iProdLens F)` can apply `funext i` themselves at
    the cost of one isolated leak. -/
theorem iProdLens_is_greatest_pw {ι : Type} {α : Type}
    (F : ι → (β : Type) × Lens β) (L : Lens α)
    (hAllSym : ∀ i (u v : (F i).1),
                (F i).2.combine u v = (F i).2.combine v u)
    (hAll : ∀ i, L.refines (F i).2) :
    ∀ r r' : Raw, L.equiv r r' →
      ∀ i, (iProdLens F).view r i = (iProdLens F).view r' i := by
  intro r r' h i
  rw [iProdLens_view F hAllSym r i, iProdLens_view F hAllSym r' i]
  exact hAll i r r' h

end E213.Lens.Lattice.IndexedJoin
