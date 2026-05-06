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

open E213.Firmware E213.Lens
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

end E213.Lens.Lattice.IndexedJoin

namespace E213.Lens.Lattice.IndexedJoin

open E213.Firmware E213.Lens

/-- **Indexed product Lens (meet)**: concrete meet of an arbitrary
    family `{L_i}` — codomain is the dependent function space.
    Each component is extracted as the view of (F i).2. -/
def iProdLens {ι : Type} (F : ι → (α : Type) × Lens α) :
    Lens ((i : ι) → (F i).1) where
  base_a := fun i => (F i).2.base_a
  base_b := fun i => (F i).2.base_b
  combine := fun f g i => (F i).2.combine (f i) (g i)

/-- iProdLens.view is a pointwise application — requires combine
    sym for each L_i. -/
theorem iProdLens_view {ι : Type} (F : ι → (α : Type) × Lens α)
    (hAllSym : ∀ i (u v : (F i).1),
                (F i).2.combine u v = (F i).2.combine v u)
    (r : Raw) :
    (iProdLens F).view r = fun i => (F i).2.view r := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hsym : ∀ u v : ((i : ι) → (F i).1),
          (iProdLens F).combine u v = (iProdLens F).combine v u := by
        intro u v; funext i
        exact hAllSym i (u i) (v i)
      have hfs : (iProdLens F).view (Raw.slash x y h)
                  = (iProdLens F).combine
                      ((iProdLens F).view x) ((iProdLens F).view y) := by
        apply Raw.fold_slash _ _ _ hsym
      rw [hfs, ihx, ihy]
      funext i
      have hL_fs : (F i).2.view (Raw.slash x y h)
                    = (F i).2.combine ((F i).2.view x) ((F i).2.view y) := by
        apply Raw.fold_slash _ _ _ (hAllSym i)
      rw [hL_fs]
      rfl

/-- iProdLens refines each L_i — lower bound. -/
theorem iProdLens_refines_each {ι : Type} (F : ι → (α : Type) × Lens α)
    (hAllSym : ∀ i (u v : (F i).1),
                (F i).2.combine u v = (F i).2.combine v u)
    (i : ι) :
    (iProdLens F).refines (F i).2 := by
  intro r r' h
  show (F i).2.view r = (F i).2.view r'
  have h1 : (iProdLens F).view r = fun j => (F j).2.view r :=
    iProdLens_view F hAllSym r
  have h2 : (iProdLens F).view r' = fun j => (F j).2.view r' :=
    iProdLens_view F hAllSym r'
  have hview : (iProdLens F).view r = (iProdLens F).view r' := h
  rw [h1, h2] at hview
  exact congrFun hview i

/-- **iProdLens universal property (greatest lower bound)**: any L
    that refines all (F i).2 also refines iProdLens F. -/
theorem iProdLens_is_greatest {ι : Type} {α : Type}
    (F : ι → (β : Type) × Lens β) (L : Lens α)
    (hAllSym : ∀ i (u v : (F i).1),
                (F i).2.combine u v = (F i).2.combine v u)
    (hAll : ∀ i, L.refines (F i).2) :
    L.refines (iProdLens F) := by
  intro r r' h
  show (iProdLens F).view r = (iProdLens F).view r'
  rw [iProdLens_view F hAllSym r, iProdLens_view F hAllSym r']
  funext i
  exact hAll i r r' h

end E213.Lens.Lattice.IndexedJoin
