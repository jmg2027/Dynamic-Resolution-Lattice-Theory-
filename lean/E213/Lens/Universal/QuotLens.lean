import E213.Lens.LensCore
import E213.Lens.Algebra.Congruence

/-!
# UniversalQuotLens: general solution of Q37.3

For **any slash-congruence E** (equivalence + slash preservation),
constructs a concrete Lens L_E with kernel = E.

## Construction

`L_E : Lens (Raw → Prop)`:
- `view r := fun s => E r s` (characteristic function: E-class of r).
- `combine f g := fun r' => ∃ X Y h, (∀ s, E X s ↔ f s) ∧
                  (∀ s, E Y s ↔ g s) ∧ E (Raw.slash X Y h) r'`.

## Core theorems

`L_E.view r = L_E.view r' ↔ E r r'` (kernel = E exactly).

→: standard consequence of funext + propext + E equivalence.
←: E r r' → ∀ s, E r s ↔ E r' s → funext → view r = view r'.

fold-structure of `combine`: from slash_cong.

## Significance

**General solution** of Q37.3 ("constructing a concrete Lens for any
slash-congruence").  True generalization of the Mod family restriction
(`ModJoinEquivGCD`).

No classical reasoning used; only funext + propext (Lean 4 core
baseline).
-/

namespace E213.Lens.Universal.QuotLens

open E213.Theory E213.Lens

variable (E : Raw → Raw → Prop)
variable (hrefl : ∀ r, E r r)
variable (hsymm : ∀ r r', E r r' → E r' r)
variable (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
variable (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
                   E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))

/-- Universal Lens for an arbitrary slash-congruence E. -/
def universalLens : Lens (Raw → Prop) where
  base_a := fun s => E Raw.a s
  base_b := fun s => E Raw.b s
  combine f g := fun r' => ∃ X : Raw, ∃ Y : Raw, ∃ h : X ≠ Y,
                           (∀ s, E X s ↔ f s) ∧
                           (∀ s, E Y s ↔ g s) ∧
                           E (Raw.slash X Y h) r'

/-- Symmetry of combine (renaming + slash_comm). -/
theorem universalLens_combine_sym (f g : Raw → Prop) :
    (universalLens E).combine f g = (universalLens E).combine g f := by
  funext r'
  apply propext
  constructor
  · rintro ⟨X, Y, h, hX, hY, hslashr'⟩
    refine ⟨Y, X, Ne.symm h, hY, hX, ?_⟩
    rwa [Raw.slash_comm Y X (Ne.symm h)]
  · rintro ⟨X, Y, h, hX, hY, hslashr'⟩
    refine ⟨Y, X, Ne.symm h, hY, hX, ?_⟩
    rwa [Raw.slash_comm Y X (Ne.symm h)]

/-- **Core theorem 1**: view r = (E r ·).  Raw.rec induction. -/
theorem universalLens_view_eq
    (hrefl : ∀ r, E r r)
    (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
    (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
              E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))
    (r : Raw) :
    (universalLens E).view r = (fun s => E r s) := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : (universalLens E).view (Raw.slash x y h)
                   = (universalLens E).combine
                       ((universalLens E).view x) ((universalLens E).view y) := by
        apply Raw.fold_slash
        intro u v; exact universalLens_combine_sym E u v
      rw [hfs, ihx, ihy]
      funext r'
      apply propext
      constructor
      · rintro ⟨X, Y, h', hX, hY, hslashr'⟩
        have hxX : E x X := by
          have hX_X : E X X := hrefl X
          exact (hX X).mp hX_X
        have hyY : E y Y := by
          have hY_Y : E Y Y := hrefl Y
          exact (hY Y).mp hY_Y
        have hslash_eq : E (Raw.slash x y h) (Raw.slash X Y h') :=
          hslash x X y Y h h' hxX hyY
        exact htrans _ _ _ hslash_eq hslashr'
      · intro hslashr'
        refine ⟨x, y, h, ?_, ?_, hslashr'⟩
        · intro s; exact Iff.rfl
        · intro s; exact Iff.rfl

/-! ## Reading-equivalence (∅-axiom) forms

`universalLens_combine_sym` / `universalLens_view_eq` state coherence as a
function `=` at `(Raw → Prop)`, which pulls `funext` (= `Quot.sound`) +
`propext`.  The residue's directionless slash only requires the readings to
*distinguish the same things*, i.e. a **pointwise `↔`**.  Stated that way both
are **∅-axiom** — they need no `funext`/`propext` (using `Raw.fold_slash_iff`
and `Iff.trans` rather than `rw` on an `↔`, which itself would pull `propext`). -/

/-- Combine symmetry as a Reading-equivalence — PURE. -/
theorem universalLens_combine_sym_pw (f g : Raw → Prop) (r' : Raw) :
    (universalLens E).combine f g r' ↔ (universalLens E).combine g f r' := by
  constructor
  · rintro ⟨X, Y, h, hX, hY, hs⟩
    exact ⟨Y, X, Ne.symm h, hY, hX, by rwa [Raw.slash_comm Y X (Ne.symm h)]⟩
  · rintro ⟨X, Y, h, hX, hY, hs⟩
    exact ⟨Y, X, Ne.symm h, hY, hX, by rwa [Raw.slash_comm Y X (Ne.symm h)]⟩

/-- `view r` as a Reading-equivalence: `view r s ↔ E r s` for all `s` — PURE.
    The pointwise form of `universalLens_view_eq`, via `Raw.fold_slash_iff`. -/
theorem universalLens_view_eq_pw
    (hrefl : ∀ r, E r r)
    (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
    (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
              E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))
    (r : Raw) : ∀ s, (universalLens E).view r s ↔ E r s := by
  induction r using Raw.rec with
  | a => intro s; exact Iff.rfl
  | b => intro s; exact Iff.rfl
  | slash x y h ihx ihy =>
      intro s
      refine (Raw.fold_slash_iff _ _ _
        (fun u v t => universalLens_combine_sym_pw E u v t) x y h s).trans ?_
      constructor
      · rintro ⟨X, Y, h', hX, hY, hslashr'⟩
        have hxX : E x X := (ihx X).mp ((hX X).mp (hrefl X))
        have hyY : E y Y := (ihy Y).mp ((hY Y).mp (hrefl Y))
        exact htrans _ _ _ (hslash x X y Y h h' hxX hyY) hslashr'
      · intro hE
        exact ⟨x, y, h, fun t => (ihx t).symm, fun t => (ihy t).symm, hE⟩

/-- **General solution of Q37.3**: kernel of universalLens E = E.
    Any slash-congruence E (equivalence + slash-preserving) is the
    kernel of a concrete Lens. -/
theorem universalLens_kernel_eq_E
    (hrefl : ∀ r, E r r)
    (hsymm : ∀ r r', E r r' → E r' r)
    (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
    (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
              E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))
    (r r' : Raw) :
    (universalLens E).view r = (universalLens E).view r' ↔ E r r' := by
  rw [universalLens_view_eq E hrefl htrans hslash r,
      universalLens_view_eq E hrefl htrans hslash r']
  constructor
  · intro h
    have hpt : ∀ s, E r s ↔ E r' s := by
      intro s
      have := congrFun h s
      exact Iff.of_eq this
    have h_r'r : E r' r := (hpt r).mp (hrefl r)
    exact hsymm _ _ h_r'r
  · intro hrr'
    funext s
    apply propext
    constructor
    · intro hrs; exact htrans _ _ _ (hsymm _ _ hrr') hrs
    · intro hr's; exact htrans _ _ _ hrr' hr's


/-- **Canonical form theorem**: for any Lens M, the kernel of
    universalLens M.equiv equals the kernel of M.  That is,
    universalLens is the canonical form of every Lens. -/
theorem universalLens_recovers (α : Type) (M : Lens α)
    (hMsym : ∀ u v, M.combine u v = M.combine v u)
    (r r' : Raw) :
    (universalLens M.equiv).view r = (universalLens M.equiv).view r'
      ↔ M.view r = M.view r' := by
  apply universalLens_kernel_eq_E
  · intro x; rfl
  · intro x y h; exact h.symm
  · intro x y z h1 h2; exact h1.trans h2
  · intro x x' y y' hxy hx'y' hxx' hyy'
    exact E213.Lens.Algebra.Congruence.Lens.equiv_slash_congruence
      M hMsym x x' y y' hxy hx'y' hxx' hyy'

/-- **Idempotence**: applying universalLens twice yields the same kernel.
    Direct expression of universalLens as a normalization map. -/
theorem universalLens_idempotent (α : Type) (M : Lens α)
    (r r' : Raw) :
    (universalLens (universalLens M.equiv).equiv).view r
       = (universalLens (universalLens M.equiv).equiv).view r'
    ↔ (universalLens M.equiv).view r = (universalLens M.equiv).view r' := by
  apply universalLens_kernel_eq_E
  · intro x; rfl
  · intro x y h; exact h.symm
  · intro x y z h1 h2; exact h1.trans h2
  · intro x x' y y' hxy hx'y' hxx' hyy'
    exact E213.Lens.Algebra.Congruence.Lens.equiv_slash_congruence
      (universalLens M.equiv) (universalLens_combine_sym M.equiv)
      x x' y y' hxy hx'y' hxx' hyy'

end E213.Lens.Universal.QuotLens
