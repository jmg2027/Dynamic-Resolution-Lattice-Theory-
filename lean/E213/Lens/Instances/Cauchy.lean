import E213.Lens.Universal.QuotLens
import E213.Lens.Lattice.IndexedJoin
import E213.Meta.Tactic.NatHelper

/-!
# LensCauchy: reduction of Cauchy completeness for 213

Proposed by Mingu (2026-04-25):
- ε → "resolution of Lens L".
- Cauchy → "for any fine Lens L, the sequence tail collapses to an
  L-class".
- Completeness → limit slash-congruence defined via universalLens.

## Definitions

**Lens-Cauchy**: sequence xs : ℕ → Raw is Cauchy with respect to
Lens L iff ∃ N, ∀ m n ≥ N, L.equiv (xs m) (xs n).

**Family-Cauchy**: Cauchy with respect to every L in a directed
family D.

## Key Insights

- Limit class = eventually-constant L-class of the sequence.
- Completeness = well-definedness of the limit class + capture via
  universalLens.
- No external metric / topology.  Uses only the Lens lattice.

This file is the framework starting point — the full ℝ-construction
is separate.
-/

namespace E213.Lens.Instances.Cauchy

open E213.Theory E213.Lens

/-- **Lens-Cauchy**: Cauchy with respect to a single Lens L. -/
def LensCauchy {α : Type} (L : Lens α) (xs : Nat → Raw) : Prop :=
  ∃ N, ∀ m n, m ≥ N → n ≥ N → L.equiv (xs m) (xs n)

/-- **Eventually-constant L-class**: the tail collapses to a single
    L-class. -/
def EventuallyClass {α : Type} (L : Lens α) (xs : Nat → Raw)
    (c : α) : Prop :=
  ∃ N, ∀ n, n ≥ N → L.view (xs n) = c

/-- **Cauchy ↔ EventuallyClass**: the two definitions are equivalent for a single Lens. -/
theorem cauchy_iff_eventually_class {α : Type} (L : Lens α)
    (xs : Nat → Raw) :
    LensCauchy L xs ↔ ∃ c, EventuallyClass L xs c := by
  constructor
  · intro ⟨N, h⟩
    refine ⟨L.view (xs N), N, ?_⟩
    intro n hn
    exact h n N hn (Nat.le_refl N)
  · intro ⟨c, N, h⟩
    refine ⟨N, ?_⟩
    intro m n hm hn
    show L.view (xs m) = L.view (xs n)
    rw [h m hm, h n hn]

/-- Uniqueness of the limit class: two EventuallyClasses are equal. -/
theorem eventually_class_unique {α : Type} (L : Lens α) (xs : Nat → Raw)
    (c c' : α) (h : EventuallyClass L xs c) (h' : EventuallyClass L xs c') :
    c = c' := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨N', hN'⟩ := h'
  let M := max N N'
  have hMN : M ≥ N := E213.Tactic.NatHelper.le_max_left N N'
  have hMN' : M ≥ N' := E213.Tactic.NatHelper.le_max_right N N'
  rw [← hN M hMN, hN' M hMN']



/-- **Cauchy witness structure**: explicit N + Cauchy property.
    Constructive (no Classical.choice). -/
structure CauchyData {α : Type} (L : Lens α) (xs : Nat → Raw) where
  N : Nat
  cauchy : ∀ m n, m ≥ N → n ≥ N → L.equiv (xs m) (xs n)

/-- **Limit class**: limit value computed directly from Cauchy data.
    The view at witness N is the limit (choice of N is irrelevant by
    the Cauchy property). -/
def limitClass {α : Type} {L : Lens α} {xs : Nat → Raw}
    (cd : CauchyData L xs) : α := L.view (xs cd.N)

/-- **Well-definedness of the limit class**: all tail elements have
    the same L.view as the limit value. -/
theorem limitClass_eq_tail {α : Type} (L : Lens α) (xs : Nat → Raw)
    (cd : CauchyData L xs) (n : Nat) (hn : n ≥ cd.N) :
    L.view (xs n) = limitClass cd := by
  unfold limitClass
  exact cd.cauchy n cd.N hn (Nat.le_refl cd.N)

/-- **Cauchy → ∃ limit class** (existential form).  Propositional
    form of CauchyData, but automatically extractable —
    `Cauchy → ∃ N witness` → CauchyData. -/
theorem cauchy_data_of {α : Type} (L : Lens α) (xs : Nat → Raw)
    (h : LensCauchy L xs) :
    ∃ cd : CauchyData L xs, True := by
  obtain ⟨N, hN⟩ := h
  exact ⟨⟨N, hN⟩, trivial⟩



/-- **Family-Cauchy**: Cauchy with respect to every (F i).2. -/
def FamilyCauchy {ι : Type} (F : ι → (α : Type) × Lens α)
    (xs : Nat → Raw) : Prop :=
  ∀ i, LensCauchy (F i).2 xs

/-- **Limit assignment structure**: explicit Cauchy witness for each i. -/
structure LimitAssignment {ι : Type} (F : ι → (α : Type) × Lens α)
    (xs : Nat → Raw) where
  data : ∀ i, CauchyData (F i).2 xs

/-- Limit value extraction — limit class for each i. -/
protected def LimitAssignment.limit {ι : Type} {F : ι → (α : Type) × Lens α}
    {xs : Nat → Raw} (la : LimitAssignment F xs) (i : ι) : (F i).1 :=
  limitClass (la.data i)


open E213.Theory E213.Lens E213.Lens.Lattice.IndexedJoin

/-- **Pointwise limit match**: the limit assignment of a family-Cauchy
    sequence agrees pointwise with the view of iProdLens F. -/
theorem pointwise_limit_match {ι : Type} (F : ι → (α : Type) × Lens α)
    (xs : Nat → Raw)
    (hAllSym : ∀ i (u v : (F i).1),
                (F i).2.combine u v = (F i).2.combine v u)
    (la : LimitAssignment F xs) (i : ι) :
    ∃ N, ∀ n, n ≥ N → (iProdLens F).view (xs n) i = la.limit i := by
  refine ⟨(la.data i).N, ?_⟩
  intro n hn
  rw [iProdLens_view F hAllSym (xs n)]
  exact limitClass_eq_tail (F i).2 xs (la.data i) n hn


open E213.Theory E213.Lens E213.Lens.Universal.QuotLens

/-- **Tail congruence**: minimum slash-congruence starting from the
    tail of sequence xs.  All tail elements (xs m, xs k) for m, k ≥ N
    collapse to a single class. -/
inductive TailCong (xs : Nat → Raw) (N : Nat) : Raw → Raw → Prop where
  | tail_eq (m k : Nat) (hm : m ≥ N) (hk : k ≥ N) :
      TailCong xs N (xs m) (xs k)
  | refl (r : Raw) : TailCong xs N r r
  | symm : TailCong xs N r r' → TailCong xs N r' r
  | trans :
      TailCong xs N r r' → TailCong xs N r' r'' → TailCong xs N r r''
  | slash_cong (hxy : x ≠ y) (hx'y' : x' ≠ y') :
      TailCong xs N x x' → TailCong xs N y y' →
      TailCong xs N (Raw.slash x y hxy) (Raw.slash x' y' hx'y')

/-- TailCong is a slash-congruence (directly via the slash_cong constructor). -/
theorem tailCong_slash_cong (xs : Nat → Raw) (N : Nat)
    (x x' y y' : Raw) (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hxx' : TailCong xs N x x') (hyy' : TailCong xs N y y') :
    TailCong xs N (Raw.slash x y hxy) (Raw.slash x' y' hx'y') :=
  TailCong.slash_cong hxy hx'y' hxx' hyy'

/-- **Limit Lens**: the universalLens of TailCong is the limit Lens of
    the sequence.  Integration of Q37.3 + Cauchy completeness. -/
def limitLens (xs : Nat → Raw) (N : Nat) : Lens (Raw → Prop) :=
  universalLens (TailCong xs N)

/-- **Kernel of limitLens = TailCong**.  Direct consequence of
    universalLens. -/
theorem limitLens_kernel (xs : Nat → Raw) (N : Nat) (r r' : Raw) :
    (limitLens xs N).view r = (limitLens xs N).view r'
      ↔ TailCong xs N r r' := by
  apply universalLens_kernel_eq_E
  · exact fun x => TailCong.refl x
  · exact fun _ _ h => TailCong.symm h
  · exact fun _ _ _ h1 h2 => TailCong.trans h1 h2
  · exact fun _ _ _ _ hxy hx'y' h1 h2 =>
      TailCong.slash_cong hxy hx'y' h1 h2

/-- **Tail collapse**: all tail elements (xs m, xs k) (m, k ≥ N)
    form a single class under limitLens.  Core expression of Cauchy
    completeness. -/
theorem limitLens_tail_collapse (xs : Nat → Raw) (N : Nat)
    (m k : Nat) (hm : m ≥ N) (hk : k ≥ N) :
    (limitLens xs N).view (xs m) = (limitLens xs N).view (xs k) :=
  (limitLens_kernel xs N (xs m) (xs k)).mpr (TailCong.tail_eq m k hm hk)

/-- TailCong ⊆ N.equiv (helper for universal property). -/
private theorem tailCong_implies_equiv {α : Type} (N : Lens α)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (xs : Nat → Raw) (M : Nat)
    (hCollapse : ∀ m k, m ≥ M → k ≥ M → N.equiv (xs m) (xs k))
    (r r' : Raw) (h : TailCong xs M r r') :
    N.equiv r r' := by
  induction h with
  | tail_eq m k hm hk => exact hCollapse m k hm hk
  | refl x => exact rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | slash_cong hxy hx'y' _ _ ih1 ih2 =>
      exact E213.Lens.Algebra.Congruence.Lens.equiv_slash_congruence
        N hNsym _ _ _ _ hxy hx'y' ih1 ih2

/-- **Universal property of limitLens (least tail-collapsing Lens)**:
    if any Lens N (with symmetric combine) collapses the tail, then
    limitLens refines N.  That is, limitLens is the finest
    tail-collapsing Lens — the universal characterization of the limit
    Lens of a Cauchy sequence. -/
theorem limitLens_is_least {α : Type} (N : Lens α)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (xs : Nat → Raw) (M : Nat)
    (hCollapse : ∀ m k, m ≥ M → k ≥ M → N.equiv (xs m) (xs k)) :
    (limitLens xs M).refines N := by
  intro r r' h
  have hTC : TailCong xs M r r' := (limitLens_kernel xs M r r').mp h
  exact tailCong_implies_equiv N hNsym xs M hCollapse r r' hTC

end E213.Lens.Instances.Cauchy
