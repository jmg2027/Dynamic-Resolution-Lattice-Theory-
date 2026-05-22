import E213.Lens.Universal.QuotLens
import E213.Lens.Lattice.JoinEquiv

/-!
# IndexedJoinLens: join of an arbitrary indexed family

If `JoinLens` is the binary join, this is the join of an arbitrary
family `{L_i}_{i ∈ I}`.

## Core

`IJoinEquiv F` (F : ι → Σ α, Lens α): least slash-congruence
containing each L_i.equiv, for an arbitrary family.

`iJoinLens F := universalLens (IJoinEquiv F)`: concrete Lens
realizing the indexed join.

For a finite family the result equals iterated binary join.
Provides new expressiveness for infinite families.
-/

namespace E213.Lens.Lattice.IndexedJoin

open E213.Theory E213.Lens
open E213.Lens.Lattice.JoinEquiv E213.Lens.Universal.QuotLens

/-- Indexed join equivalence: smallest slash-congruence containing
    each L_i.equiv, for an arbitrary family of Lenses. -/
inductive IJoinEquiv {ι : Type} (F : ι → (α : Type) × Lens α) :
    Raw → Raw → Prop where
  | ofL (i : ι) :
      (F i).2.equiv x y → IJoinEquiv F x y
  | refl (x : Raw) : IJoinEquiv F x x
  | symm : IJoinEquiv F x y → IJoinEquiv F y x
  | trans : IJoinEquiv F x y → IJoinEquiv F y z → IJoinEquiv F x z
  | slash_cong (hxy : x ≠ y) (hx'y' : x' ≠ y') :
      IJoinEquiv F x x' → IJoinEquiv F y y' →
      IJoinEquiv F (Raw.slash x y hxy) (Raw.slash x' y' hx'y')

/-- **Concrete indexed join Lens**: universalLens of IJoinEquiv. -/
def iJoinLens {ι : Type} (F : ι → (α : Type) × Lens α) :
    Lens (Raw → Prop) := universalLens (IJoinEquiv F)

/-- **kernel = IJoinEquiv**.  Direct consequence of universalLens. -/
theorem iJoinLens_kernel {ι : Type} (F : ι → (α : Type) × Lens α)
    (r r' : Raw) :
    (iJoinLens F).view r = (iJoinLens F).view r'
      ↔ IJoinEquiv F r r' := by
  apply universalLens_kernel_eq_E
  · exact fun x => IJoinEquiv.refl x
  · exact fun _ _ h => IJoinEquiv.symm h
  · exact fun _ _ _ h1 h2 => IJoinEquiv.trans h1 h2
  · exact fun _ _ _ _ hxy hx'y' h1 h2 =>
      IJoinEquiv.slash_cong hxy hx'y' h1 h2

/-- **Each L_i refines iJoinLens**: all L_i in the family have
    iJoinLens as a common upper bound. -/
theorem each_refines_iJoinLens {ι : Type} (F : ι → (α : Type) × Lens α)
    (i : ι) :
    (F i).2.refines (iJoinLens F) := by
  intro r r' h
  show (iJoinLens F).view r = (iJoinLens F).view r'
  rw [iJoinLens_kernel F r r']
  exact IJoinEquiv.ofL i h

/-- IJoinEquiv → N.equiv (helper for universal property). -/
private theorem ijoin_implies_N {ι : Type} {γ : Type}
    (F : ι → (α : Type) × Lens α) (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hAll : ∀ i, (F i).2.refines N)
    (r r' : Raw) (h : IJoinEquiv F r r') : N.equiv r r' := by
  induction h with
  | ofL i hL => exact hAll i _ _ hL
  | refl x => exact rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | slash_cong hxy hx'y' _ _ ih1 ih2 =>
      exact E213.Lens.Algebra.Congruence.Lens.equiv_slash_congruence
        N hNsym _ _ _ _ hxy hx'y' ih1 ih2

/-- **Universal property (indexed)**: iJoinLens is the least upper
    bound.  All L_i refine N + N.combine sym → iJoinLens refines N. -/
theorem iJoinLens_is_least {ι : Type} {γ : Type}
    (F : ι → (α : Type) × Lens α) (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hAll : ∀ i, (F i).2.refines N) :
    (iJoinLens F).refines N := by
  intro r r' h
  have hJE : IJoinEquiv F r r' := (iJoinLens_kernel F r r').mp h
  exact ijoin_implies_N F N hNsym hAll r r' hJE


open E213.Term.Internal (Tree)

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

/-- **iProdLens universal property (greatest lower bound), stated
    pointwise at each index**.  Any `L` that refines all `(F i).2`
    produces equal `iProdLens F`-views at every index `i`.  This is
    the ∅-axiom form: a function-equality reassembly
    `L.refines (iProdLens F)` would require `funext` (= `Quot.sound`
    in the Lean 4 kernel), so we expose only the pointwise statement.
    Downstream consumers reason pointwise at the chosen index. -/
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
