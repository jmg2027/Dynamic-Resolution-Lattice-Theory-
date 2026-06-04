import E213.Lens.LensCore

/-!
# Reading-native equivalence — 213's sameness on Lens codomains (∅-axiom)

The residue's notion of "same under `L`" is **distinguishing the same things**,
not Lean `=` of the view-values.  At a `Prop`-valued codomain (`Lens (Raw → Prop)`)
Lean `=` of views is an equality at a function-of-`Prop` codomain — it pulls
`funext` (= `Quot.sound`) + `propext`, importing identity beyond the
distinguishing content.  `Lens.equivR L x y := ∀ s, L.view x s ↔ L.view y s`
records the distinguishing content directly: a pointwise `↔`.  It is ∅-axiom and
carries the full equivalence structure (`refl` / `symm` / `trans`) and a
refinement order (`refinesR`); the single `=`-cost is isolated in the lone bridge
`equivR_to_equiv`.

`ReadingEq α` lifts this to the **codomain-polymorphic** primitive: per codomain
`α`, the relation `same` under which two `α`-readings count as the same
distinguishing.  At decidable codomains (`Bool`, `Nat`) `same` is `=` (already
∅-axiom); at `Raw → Prop` it is the pointwise `↔` (`equivR`).  `Lens.equivG` /
`Lens.refinesG` are the equivalence and refinement over `same`, reducing
definitionally to `equiv` / `refines` (default) and `equivR` / `refinesR`
(`Raw → Prop`).  This is the carrier of 213's one sameness across the Lens ring;
see `theory/lens/unified_equivalence.md`, `seed/AXIOM/06_lens_readings.md` §6.3,
and.
-/

namespace E213.Lens

open E213.Theory

/-- Reading-native equivalence for a `Prop`-valued Lens: `x` and `y` are the
    same under `L` iff `L` distinguishes them the same way, pointwise. -/
protected def Lens.equivR (L : Lens (Raw → Prop)) (x y : Raw) : Prop :=
  ∀ s, L.view x s ↔ L.view y s

protected theorem Lens.equivR_refl (L : Lens (Raw → Prop)) (x : Raw) :
    L.equivR x x := fun _ => Iff.rfl

protected theorem Lens.equivR_symm (L : Lens (Raw → Prop)) {x y : Raw} :
    L.equivR x y → L.equivR y x := fun h s => (h s).symm

protected theorem Lens.equivR_trans (L : Lens (Raw → Prop)) {x y z : Raw} :
    L.equivR x y → L.equivR y z → L.equivR x z := fun h1 h2 s => (h1 s).trans (h2 s)

/-- Reading-native refinement: `L` refines `M` iff `L`-sameness implies
    `M`-sameness (both pointwise).  The `Prop`-codomain counterpart of
    `Lens.refines`, ∅-axiom. -/
protected def Lens.refinesR (L M : Lens (Raw → Prop)) : Prop :=
  ∀ x y, L.equivR x y → M.equivR x y

protected theorem Lens.refinesR_refl (L : Lens (Raw → Prop)) : L.refinesR L :=
  fun _ _ h => h

protected theorem Lens.refinesR_trans {L M N : Lens (Raw → Prop)} :
    L.refinesR M → M.refinesR N → L.refinesR N :=
  fun h1 h2 x y h => h2 x y (h1 x y h)

/-- Bridge to the `=`-based `Lens.equiv`.  This is the **single** place the
    Lean-`=` cost (`funext` = `Quot.sound`, `propext`) is paid — every consumer
    that genuinely needs propositional `=` of views goes through here, and
    nothing else in the Reading-native development touches those axioms. -/
protected theorem Lens.equivR_to_equiv (L : Lens (Raw → Prop)) {x y : Raw}
    (h : L.equivR x y) : L.equiv x y := by
  show L.view x = L.view y
  funext s; exact propext (h s)

/-- The converse bridge is **free** (∅-axiom): any `=`-equivalence already gives
    the Reading-equivalence.  So results proven via the sealed `=`-forms transport
    to `equivR` at no cost; only the `equivR → =` direction above pays.  This is
    the precise cost asymmetry — `=` ⟹ `↔` free, `↔` ⟹ `=` costs `funext`/`propext`
    — that makes migrating the refinement lattice onto `equivR`/`refinesR`
    mechanical. -/
protected theorem Lens.equivR_of_equiv (L : Lens (Raw → Prop)) {x y : Raw}
    (h : L.equiv x y) : L.equivR x y :=
  fun s => h ▸ Iff.rfl

/-! ## Codomain-polymorphic Reading-equivalence (∅-axiom)

`equivR`/`refinesR` solve the `Prop`-codomain case, but the refinement lattice
has consumers at other codomains: a source Lens `L : Lens α` for *arbitrary* `α`
(the lenses being joined), the `Raw → Prop` join targets, and the dependent
product meets (`iProdLens : Lens ((i : ι) → (F i).1)`).  A single
refinement relation across these needs a notion of "two `α`-readings count as
the same distinguishing" that is *polymorphic in the codomain* `α` — `=` at the
decidable codomains (`Nat`, `Bool`, any `α` with no finer reading-sameness),
pointwise `↔` at `Raw → Prop`, and so on.

`ReadingEq α` supplies exactly that relation, with the equivalence laws.  The
`propext` cost is confined to the *one* `Prop`-codomain instance's content (the
`↔`) and is **not** an axiom of the laws themselves; every law below is ∅-axiom.
`Lens.equivG`/`Lens.refinesG` are then the codomain-polymorphic equivalence and
refinement, and they reduce **definitionally** to `equiv` (default instance) and
to `equivR` (the `Raw → Prop` instance) — so existing PURE `=`-form and
`equivR`-form results plug in with no bridge. -/

/-- Reading-sameness on a Lens codomain `α`: the relation under which two
    `α`-readings count as the same distinguishing.  An equivalence relation;
    nothing else is assumed.  See `seed/AXIOM/06_lens_readings.md` §6.3. -/
class ReadingEq (α : Type) where
  /-- The reading-sameness relation. -/
  same : α → α → Prop
  /-- Reflexivity. -/
  same_refl : ∀ a, same a a
  /-- Symmetry. -/
  same_symm : ∀ {a b}, same a b → same b a
  /-- Transitivity. -/
  same_trans : ∀ {a b c}, same a b → same b c → same a c

/-- Default reading-sameness: Lean `=`.  Low priority so a finer codomain
    instance (e.g. the `Raw → Prop` pointwise-`↔` below) wins.  PURE — the laws
    are `Eq.refl`/`Eq.symm`/`Eq.trans`. -/
instance (priority := low) instReadingEqEq (α : Type) : ReadingEq α where
  same := Eq
  same_refl := Eq.refl
  same_symm := Eq.symm
  same_trans := Eq.trans

/-- Reading-sameness at `Raw → Prop`: pointwise `↔` — two readings are the same
    iff they distinguish the same `s` for every `s`.  This is exactly the body
    of `equivR`; the `propext` lives in the `↔` payload, never in the laws (which
    are `Iff.rfl`/`.symm`/`.trans`, all PURE). -/
instance instReadingEqRawProp : ReadingEq (Raw → Prop) where
  same f g := ∀ s, f s ↔ g s
  same_refl _ := fun _ => Iff.rfl
  same_symm h := fun s => (h s).symm
  same_trans h1 h2 := fun s => (h1 s).trans (h2 s)

/-- Codomain-polymorphic Reading-equivalence: `x` and `y` are the same under `L`
    iff their `α`-readings are reading-same.  Reduces to `equiv` at the default
    instance and to `equivR` at `Raw → Prop` — both definitionally. -/
protected def Lens.equivG {α : Type} [ReadingEq α] (L : Lens α) (x y : Raw) : Prop :=
  ReadingEq.same (L.view x) (L.view y)

protected theorem Lens.equivG_refl {α} [ReadingEq α] (L : Lens α) (x : Raw) :
    L.equivG x x := ReadingEq.same_refl _

protected theorem Lens.equivG_symm {α} [ReadingEq α] (L : Lens α) {x y : Raw} :
    L.equivG x y → L.equivG y x := ReadingEq.same_symm

protected theorem Lens.equivG_trans {α} [ReadingEq α] (L : Lens α) {x y z : Raw} :
    L.equivG x y → L.equivG y z → L.equivG x z := ReadingEq.same_trans

/-- Codomain-polymorphic refinement: `L`-sameness implies `M`-sameness, each at
    its own codomain's reading-sameness.  The `=`-cost of stating a `Raw → Prop`
    target's sameness as `=` is gone — the target reduces to `equivR`. -/
protected def Lens.refinesG {α β : Type} [ReadingEq α] [ReadingEq β]
    (L : Lens α) (M : Lens β) : Prop :=
  ∀ x y, L.equivG x y → M.equivG x y

protected theorem Lens.refinesG_refl {α} [ReadingEq α] (L : Lens α) :
    L.refinesG L := fun _ _ h => h

protected theorem Lens.refinesG_trans {α β γ} [ReadingEq α] [ReadingEq β] [ReadingEq γ]
    {L : Lens α} {M : Lens β} {N : Lens γ} :
    L.refinesG M → M.refinesG N → L.refinesG N :=
  fun h1 h2 x y h => h2 x y (h1 x y h)

/-- At `Raw → Prop`, `equivG` **is** `equivR` (definitional). -/
protected theorem Lens.equivG_eq_equivR (L : Lens (Raw → Prop)) (x y : Raw) :
    L.equivG x y = L.equivR x y := rfl

/-- At the default instance, `equivG` **is** the `=`-based `equiv` (definitional).
    Lets `=`-form hypotheses feed `equivG`-stated lemmas with no bridge. -/
protected theorem Lens.equivG_eq_equiv {α} (L : Lens α) (x y : Raw) :
    L.equivG x y = L.equiv x y := rfl

/-! ### Slash-congruence for `equivG`

The `equivG` reading-sameness is a slash-congruence whenever the codomain's
`combine` respects it and the fold reduces through it — the two facts every
concrete Lens supplies (`Raw.fold_slash`/`Raw.fold_slash_iff` for the reduction,
`combine`-monotonicity for the respect).  Stated generically so both the default
(`=`, via `Raw.fold_slash`) and `Raw → Prop` (`↔`, via `Raw.fold_slash_iff`)
instances reuse it. -/
protected theorem Lens.equivG_slash_congruence {α} [ReadingEq α] (L : Lens α)
    (hfold : ∀ (x y : Raw) (h : x ≠ y),
      ReadingEq.same (L.view (Raw.slash x y h)) (L.combine (L.view x) (L.view y)))
    (hcomb : ∀ a a' b b' : α,
      ReadingEq.same a a' → ReadingEq.same b b' →
      ReadingEq.same (L.combine a b) (L.combine a' b'))
    {x x' y y' : Raw} (hx : x ≠ y) (hx' : x' ≠ y')
    (hxx' : L.equivG x x') (hyy' : L.equivG y y') :
    L.equivG (Raw.slash x y hx) (Raw.slash x' y' hx') :=
  ReadingEq.same_trans (hfold x y hx)
    (ReadingEq.same_trans (hcomb _ _ _ _ hxx' hyy')
      (ReadingEq.same_symm (hfold x' y' hx')))

end E213.Lens
