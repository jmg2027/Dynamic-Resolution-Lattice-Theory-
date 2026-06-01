import E213.Lens.LensCore
import E213.Lens.ReadingEquiv
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

## Core theorem

`universalLens_kernel_eq_E_R`: `L_E.equivR r r' ↔ E r r'` (kernel = E exactly),
where `equivR` is the **Reading-equivalence** (pointwise `↔`): two Raws are the
same under `L_E` iff their readings distinguish the same things.  This is the
residue-native kernel — `∀ s, view r s ↔ view r' s` rather than Lean `=` of the
view-functions — so it is **∅-axiom** (no `funext`/`propext`), via
`Raw.fold_slash_iff`.

fold-structure of `combine`: from slash_cong, stated pointwise
(`universalLens_combine_sym_pw` / `combine_cong_pw`).

## Significance

**General solution** of Q37.3 ("constructing a concrete Lens for any
slash-congruence").  True generalization of the Mod family restriction
(`ModJoinEquivGCD`).  The closure facts (`recovers_R`, `idempotent_R`) make
`universalLens` the ∅-axiom canonical-form / normalization map on the Lens
space.
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

/-! ## Reading-equivalence (∅-axiom) forms

`universalLens` coherence is stated as a **pointwise `↔`** (Reading-equivalence),
the residue-native notion: the directionless slash only requires the readings to
*distinguish the same things*, never Lean `=` of the view-functions.  Stated that
way every theorem here is **∅-axiom** — using `Raw.fold_slash_iff` and
`Iff.trans` rather than `rw` on an `↔`/`funext` on a view-`=` (either of which
would pull `propext` / `Quot.sound`). -/

/-- Combine symmetry as a Reading-equivalence — PURE. -/
theorem universalLens_combine_sym_pw (f g : Raw → Prop) (r' : Raw) :
    (universalLens E).combine f g r' ↔ (universalLens E).combine g f r' := by
  constructor
  · rintro ⟨X, Y, h, hX, hY, hs⟩
    exact ⟨Y, X, Ne.symm h, hY, hX, by rwa [Raw.slash_comm Y X (Ne.symm h)]⟩
  · rintro ⟨X, Y, h, hX, hY, hs⟩
    exact ⟨Y, X, Ne.symm h, hY, hX, by rwa [Raw.slash_comm Y X (Ne.symm h)]⟩

/-- `view r` as a Reading-equivalence: `view r s ↔ E r s` for all `s` — PURE.
    The view characterisation in pointwise-`↔` form, via `Raw.fold_slash_iff`. -/
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

/-- `combine` respects pointwise `↔` in both arguments — the universalLens
    `combine`'s Reading-monotonicity.  PURE; holds for *any* `E`. -/
theorem universalLens_combine_cong_pw (f f' g g' : Raw → Prop)
    (hf : ∀ s, f s ↔ f' s) (hg : ∀ s, g s ↔ g' s) :
    ∀ r', (universalLens E).combine f g r' ↔ (universalLens E).combine f' g' r' := by
  intro r'
  constructor
  · rintro ⟨X, Y, h, hX, hY, hs⟩
    exact ⟨X, Y, h, fun s => (hX s).trans (hf s), fun s => (hY s).trans (hg s), hs⟩
  · rintro ⟨X, Y, h, hX, hY, hs⟩
    exact ⟨X, Y, h, fun s => (hX s).trans (hf s).symm, fun s => (hY s).trans (hg s).symm, hs⟩

/-- Fold/slash reduction as a pointwise `↔` — `view (slash x y h)` distinguishes
    the same things as `combine (view x) (view y)`.  PURE, via `Raw.fold_slash_iff`
    + the unconditional `combine_sym_pw`. -/
theorem universalLens_fold_pw (x y : Raw) (h : x ≠ y) :
    ∀ s, (universalLens E).view (Raw.slash x y h) s
      ↔ (universalLens E).combine ((universalLens E).view x)
           ((universalLens E).view y) s :=
  fun s => Raw.fold_slash_iff _ _ _
    (fun u v t => universalLens_combine_sym_pw E u v t) x y h s

/-- `(universalLens E).equivR` is a slash-congruence — the Reading-native
    (∅-axiom) form of `equiv_slash_congruence` at the `Raw → Prop` codomain,
    via the generic `Lens.equivG_slash_congruence` (recall `equivG = equivR`
    here).  Needs no symmetry hypothesis on `E`: the universalLens `combine`
    is unconditionally `↔`-symmetric and `↔`-monotone. -/
theorem universalLens_equivR_slash_congruence
    {x x' y y' : Raw} (hx : x ≠ y) (hx' : x' ≠ y')
    (hxx' : (universalLens E).equivR x x') (hyy' : (universalLens E).equivR y y') :
    (universalLens E).equivR (Raw.slash x y hx) (Raw.slash x' y' hx') :=
  Lens.equivG_slash_congruence (universalLens E)
    (fun a b hab => universalLens_fold_pw E a b hab)
    (fun a a' b b' ha hb => universalLens_combine_cong_pw E a a' b b' ha hb)
    hx hx' hxx' hyy'

/-- **Kernel = E, Reading-native** — the ∅-axiom hub, and the **general solution
    of Q37.3**: every slash-congruence `E` (equivalence + slash-preserving) is the
    Reading-equivalence kernel of a concrete Lens.  `equivR` (pointwise `↔`) is
    the residue-native kernel; this is the load-bearing theorem the whole
    refinement lattice / Cauchy machinery rests on, with no `funext`/`propext`. -/
theorem universalLens_kernel_eq_E_R
    (hrefl : ∀ r, E r r) (hsymm : ∀ r r', E r r' → E r' r)
    (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
    (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
              E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))
    (r r' : Raw) :
    (universalLens E).equivR r r' ↔ E r r' := by
  constructor
  · intro h
    have h2 := (universalLens_view_eq_pw E hrefl htrans hslash r' r').mpr (hrefl r')
    exact (universalLens_view_eq_pw E hrefl htrans hslash r r').mp ((h r').mpr h2)
  · intro hE s
    refine (universalLens_view_eq_pw E hrefl htrans hslash r s).trans ?_
    refine Iff.trans ?_ (universalLens_view_eq_pw E hrefl htrans hslash r' s).symm
    exact ⟨fun hh => htrans r' r s (hsymm r r' hE) hh, fun hh => htrans r r' s hE hh⟩

/-- **Canonical form, Reading-native (∅-axiom)**.  `universalLens M.equiv`
    recovers `M`'s kernel: its `equivR` kernel equals `M.equiv`.  So
    `universalLens` is the canonical form of every (commutative-combine) Lens,
    Reading-natively.  PURE, via `kernel_eq_E_R`. -/
theorem universalLens_recovers_R (α : Type) (M : Lens α)
    (hMsym : ∀ u v, M.combine u v = M.combine v u)
    (r r' : Raw) :
    (universalLens M.equiv).equivR r r' ↔ M.equiv r r' :=
  universalLens_kernel_eq_E_R M.equiv
    (fun _ => rfl) (fun _ _ h => h.symm) (fun _ _ _ h1 h2 => h1.trans h2)
    (fun x x' y y' hxy hx'y' hxx' hyy' =>
      E213.Lens.Algebra.Congruence.Lens.equiv_slash_congruence
        M hMsym x x' y y' hxy hx'y' hxx' hyy')
    r r'

/-- **Idempotence, Reading-native (∅-axiom)**.  Normalizing the (already-normal)
    `equivR` kernel of `universalLens E` again recovers it — `universalLens` is a
    fixed-point as a normalization map.  PURE: the inner relation's
    slash-congruence is `universalLens_equivR_slash_congruence`, needing no
    `=`-form `combine_sym`. -/
theorem universalLens_idempotent_R (r r' : Raw) :
    (universalLens ((universalLens E).equivR)).equivR r r'
      ↔ (universalLens E).equivR r r' :=
  universalLens_kernel_eq_E_R ((universalLens E).equivR)
    (fun x => Lens.equivR_refl _ x)
    (fun _ _ h => Lens.equivR_symm _ h)
    (fun _ _ _ h1 h2 => Lens.equivR_trans _ h1 h2)
    (fun _ _ _ _ hxy hx'y' hxx' hyy' =>
      universalLens_equivR_slash_congruence E hxy hx'y' hxx' hyy')
    r r'

end E213.Lens.Universal.QuotLens
