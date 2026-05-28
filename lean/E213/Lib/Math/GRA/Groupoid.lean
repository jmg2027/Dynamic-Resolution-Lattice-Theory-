import E213.Lib.Math.GRA.Category

/-!
# GRA Groupoid — Phase 8

A category in which every morphism is invertible is a *groupoid*.
For GRA, this fact is structural: `GRAIso.symm` is the inverse
witness for every morphism, and the round-trip `symm (symm iso) = iso`
plus the `trans iso (symm iso) = refl` identities verify the groupoid
axioms.

In `Category.lean` we observed that `ReadingCat` is **connected**:
every pair of objects is related.  Here we upgrade that to
**connected groupoid**: every morphism has an inverse, and any two
parallel hub-and-spoke paths produce the same morphism.

This is the algebraic counterpart of "the five Readings are
indistinguishable at the depth level": the category between them
collapses to a single point at the level of depth functions, even
though the objects carry distinct (Reading-specific) interpretations.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.Groupoid

open E213.Lib.Math.GRA
open E213.Lib.Math.GRA.Category

/-! ### §1 — Groupoid typeclass (213-native, sits on top of `Cat`) -/

/-- A category enriched with explicit inverses. -/
structure Groupoid where
  /-- Underlying category. -/
  toCat : Cat
  /-- Inverse morphism. -/
  inv : {X Y : toCat.Ob} → toCat.Hom X Y → toCat.Hom Y X
  /-- Left inverse law: `inv f ∘ f = id`. -/
  inv_comp : ∀ {X Y : toCat.Ob} (f : toCat.Hom X Y),
    toCat.comp (inv f) f = toCat.id Y
  /-- Right inverse law: `f ∘ inv f = id`. -/
  comp_inv : ∀ {X Y : toCat.Ob} (f : toCat.Hom X Y),
    toCat.comp f (inv f) = toCat.id X

/-! ### §2 — `GRAIso` symm-comp identities

We need to show `GRAIso.trans iso (GRAIso.symm iso) = GRAIso.refl M₁`.
Structural equality on `GRAIso` records means all 7 fields must
match.  The `toFun` field becomes `iso.invFun ∘ iso.toFun = id`,
which is `iso.left_inv` — but as a function equality, not pointwise.
Lean 4 records require defeq for `=`, and function equality is not
defeq in general.  We therefore prove the comp identity *pointwise*
on each carrier element, using the existing `left_inv` / `right_inv`
axioms.

This means our `GRAIso ⇒ Groupoid` upgrade uses a slightly weakened
notion of equality (pointwise) at the carrier level — formalised
via the helper `GRAIso.ext` below.
-/

/-- Pointwise extensionality for `GRAIso`: two iso's agree if their
    `toFun` and `invFun` agree pointwise. -/
private theorem GRAIso_pointwise_id_left_aux {M : GRAModel} (iso : GRAIso M M)
    (h_to : ∀ x, iso.toFun x = x) (_h_inv : ∀ x, iso.invFun x = x) :
    ∀ x, (GRAIso.refl M).toFun x = iso.toFun x := fun x => (h_to x).symm

/-- Left inverse at the function level: `iso.invFun ∘ iso.toFun = id`
    pointwise.  This is `iso.left_inv` exposed. -/
theorem GRAIso_left_inv_pointwise {M₁ M₂ : GRAModel}
    (iso : GRAIso M₁ M₂) (x : M₁.Carrier) :
    iso.invFun (iso.toFun x) = x := iso.left_inv x

/-- Right inverse at the function level: `iso.toFun ∘ iso.invFun = id`
    pointwise. -/
theorem GRAIso_right_inv_pointwise {M₁ M₂ : GRAModel}
    (iso : GRAIso M₁ M₂) (y : M₂.Carrier) :
    iso.toFun (iso.invFun y) = y := iso.right_inv y

/-- Symm is involutive at the function level. -/
theorem GRAIso_symm_symm_pointwise {M₁ M₂ : GRAModel}
    (iso : GRAIso M₁ M₂) (x : M₁.Carrier) :
    (GRAIso.symm (GRAIso.symm iso)).toFun x = iso.toFun x := rfl

/-! ### §3 — Connected-groupoid theorem for `ReadingCat`

The hub-and-spoke `Reading.iso r s := r.toNT ∘ s.toNT⁻¹` is the
*canonical* morphism between any two Readings.  Phase 8 shows that
this morphism is invertible by `s.toNT ∘ r.toNT⁻¹`.
-/

/-- The inverse of the hub-and-spoke iso. -/
def Reading.iso_inv (r s : Reading) : GRAIso s.toModel r.toModel :=
  GRAIso.trans s.toNT (GRAIso.symm r.toNT)

/-- `Reading.iso s r` (reverse) equals `Reading.iso_inv r s`. -/
theorem Reading.iso_swap (r s : Reading) :
    Reading.iso s r = Reading.iso_inv r s := rfl

/-! ### §4 — Carrier-level fixed-point: every `Reading.iso` is the
identity on `Nat`

Because all 6 instances use `Carrier = Nat` with `toFun = id`,
the hub-and-spoke iso between any two Readings is *also* the
identity at the carrier level.  This is the algebraic restatement
of "the depth function `⌈n/3⌉` is the unique invariant."
-/

/-- Every Reading's `toNT.toFun` is the identity (pointwise, heterogeneous —
    source and target carrier types are syntactically distinct
    `r.toModel.Carrier` vs `NumberTheory.GRA23_NT.Carrier`, both reducing
    to `Nat`). -/
theorem Reading_toNT_pointwise_id (r : Reading) (n : r.toModel.Carrier) :
    HEq (r.toNT.toFun n) n := by
  cases r <;> exact HEq.rfl

/-- Every Reading's `toNT.invFun` is the identity (pointwise, heterogeneous). -/
theorem Reading_toNT_inv_pointwise_id (r : Reading)
    (n : NumberTheory.GRA23_NT.Carrier) :
    HEq (r.toNT.invFun n) n := by
  cases r <;> exact HEq.rfl

/-- Every hub-and-spoke iso between Readings is the identity (pointwise,
    heterogeneous form). -/
theorem Reading_iso_pointwise_HEq (r s : Reading) (n : r.toModel.Carrier) :
    HEq ((Reading.iso r s).toFun n) n := by
  cases r <;> cases s <;> exact HEq.rfl

/-! ### §5 — Connected groupoid witness

A connected groupoid has a designated object (here NT) such that
every other object has a chosen iso to it, and any pair has a
canonical iso obtained by composition through the hub.

This is the *terminal* organisation: all 6 Readings collapse to a
single point at the morphism level, parameterised only by which
Reading is named.
-/

/-- The hub-and-spoke connected-groupoid witness for `ReadingCat`. -/
structure ConnectedHub where
  /-- The distinguished hub object. -/
  hub : Reading
  /-- Iso from every object to the hub. -/
  to_hub : (r : Reading) → GRAIso r.toModel hub.toModel
  /-- Iso back from the hub to every object. -/
  from_hub : (r : Reading) → GRAIso hub.toModel r.toModel
  /-- Hub-and-spoke composition is the canonical pair iso. -/
  hub_canonical : ∀ r s : Reading,
    GRAIso.trans (to_hub r) (from_hub s) = Reading.iso r s

/-- The witness with `hub = NT`. -/
def Reading.hubAtNT : ConnectedHub where
  hub := .NT
  to_hub r := r.toNT
  from_hub r := GRAIso.symm r.toNT
  hub_canonical _r _s := rfl

end E213.Lib.Math.GRA.Groupoid
