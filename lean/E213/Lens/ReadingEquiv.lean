import E213.Lens.LensCore

/-!
# Reading-native equivalence for `Prop`-valued Lenses (∅-axiom)

`Lens.equiv L x y := L.view x = L.view y` records "same reading under `L`" as
Lean propositional `=`.  For a `Prop`-valued Lens (`Lens (Raw → Prop)`) that is
an equality at a function-of-`Prop` codomain, so it pulls `funext`
(= `Quot.sound`) + `propext` — the source of the whole sealed-DIRTY
`combine_sym` / `view_eq` / kernel / `refines` family.

But the residue's distinguishing content only asks that two readings
**distinguish the same things** — a pointwise `↔`, not Lean `=` of the
view-values.  `Lens.equivR` records exactly that.  It is ∅-axiom and carries the
full equivalence structure (`refl` / `symm` / `trans`) and a refinement order
(`refinesR`) purely.  The single `=`-cost is isolated in one bridge,
`equivR_to_equiv` (the only declaration here that is not PURE).

This is the 213-native notion of Lens sameness: "`L` distinguishes `x` and `y`
the same way", matching `theory/lens/unified_equivalence.md` ("equivalence is one
Lens-arrow") and `seed/AXIOM/06_lens_readings.md` §6.3.  For decidable codomains
(`Bool`, `Nat`) the `=`-based `Lens.equiv` is already PURE and needs no
counterpart; the issue is precisely the `Prop`-valued case captured here.
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

end E213.Lens
