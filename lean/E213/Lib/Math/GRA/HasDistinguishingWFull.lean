import E213.Lib.Math.GRA.HasDistinguishingW
import E213.Lib.Math.GRA.DepthFunctor

/-!
# GRA HasDistinguishingW full instance on `GRA23` — Phase 21

Phase 20 defined `HasDistinguishingW.{u, v}` (the weakened
typeclass with iso-symmetric `combine_sym`) and built the key
`productSwapIso` witness.  Phase 21 now constructs a **full
instance** on `GRA23` (the (2, 3)-packaged GRA-model type from
Phase 10).

The hard part is the **categorical distinctness**: the two
distinguished atoms must not be iso (under the chosen `Equiv =
GRAIso`).  We pick:

  · `a = ⟨trivial23, rfl, rfl⟩` — the trivial (2, 3)-model
    with `TrivialCarrier` (one element)
  · `b = ⟨NumberTheory.GRA23_NT, rfl, rfl⟩` — the hub model
    with `Nat` carrier

A `GRAIso trivial23 NumberTheory.GRA23_NT` would give a bijection
`TrivialCarrier ↔ Nat`, which is impossible because
`TrivialCarrier` has one element and `Nat` has at least two
(`0 ≠ 1`).

The proof uses `right_inv` of the iso: any two `Nat` values
must have the *same* preimage under `invFun` (since
`TrivialCarrier` has only `.star`), but `right_inv` forces them
to be distinct.  PURE by `cases` on `TrivialCarrier`.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.HasDistinguishingWFull

open E213.Lib.Math.GRA
open E213.Lib.Math.GRA.Monoidal (product trivial23 TrivialCarrier)
open E213.Lib.Math.GRA.DepthFunctor (GRA23)
open E213.Lib.Math.GRA.HasDistinguishingW (HasDistinguishingW productSwapIso)

/-! ### §1 — Categorical distinctness of `trivial23` and `GRA23_NT`

The key Phase 21 ingredient: no `GRAIso` exists between the
trivial one-element model and the Nat-carrier model.
-/

/-- All elements of `TrivialCarrier` are equal (subsingleton). -/
private theorem trivialCarrier_subsingleton :
    ∀ x y : TrivialCarrier, x = y := by
  intro x y
  cases x; cases y; rfl

/-- **No iso from `trivial23` to `GRA23_NT`**.  A would-be iso
    has `invFun : Nat → TrivialCarrier`, and since
    `TrivialCarrier` is a subsingleton, `invFun 0 = invFun 1`.
    Then `right_inv` forces `0 = toFun (invFun 0) = toFun (invFun 1)
    = 1` — contradiction.

    `def` rather than `theorem` because `GRAIso` is `Type`-valued
    (carries data), so `GRAIso _ _ → False` is in `Type 1`, not
    `Prop`. -/
def trivial23_not_iso_NT :
    GRAIso trivial23 NumberTheory.GRA23_NT → False := by
  intro iso
  -- The carrier of `NumberTheory.GRA23_NT` is `NTCarrier = Nat` by abbrev,
  -- but Lean's type-class search doesn't always unfold `.Carrier`.  We
  -- bypass by binding Nat-typed witnesses directly and casting through the
  -- iso fields.
  --
  -- Strategy: apply iso.invFun to two distinct Nat values; both land
  -- in TrivialCarrier (subsingleton); their images under iso.toFun
  -- collide.
  let zero_nat : NumberTheory.GRA23_NT.Carrier :=
    (0 : Nat)  -- definitionally Nat
  let one_nat : NumberTheory.GRA23_NT.Carrier :=
    (1 : Nat)
  -- The carrier of trivial23 is TrivialCarrier (subsingleton)
  have h_inv_eq : iso.invFun zero_nat = iso.invFun one_nat :=
    trivialCarrier_subsingleton _ _
  have hr0 : iso.toFun (iso.invFun zero_nat) = zero_nat := iso.right_inv _
  have hr1 : iso.toFun (iso.invFun one_nat) = one_nat := iso.right_inv _
  rw [h_inv_eq] at hr0
  -- hr0 : iso.toFun (iso.invFun one_nat) = zero_nat
  -- hr1 : iso.toFun (iso.invFun one_nat) = one_nat
  -- So zero_nat = one_nat, i.e., (0 : Nat) = 1
  have h01 : zero_nat = one_nat := hr0.symm.trans hr1
  -- This is Nat-level 0 = 1 (by definitional unfolding), decidably false.
  have h01_nat : (0 : Nat) = (1 : Nat) := h01
  exact absurd h01_nat (by decide)

/-! ### §2 — Extended typeclass with categorical distinctness

`HasDistinguishingWFull` extends `HasDistinguishingW` with a
`distinct_equiv : ¬ Equiv a b` field — the categorical
distinctness condition.
-/

/-- `HasDistinguishingW` augmented with categorical
    distinctness: the two atoms are not `Equiv`. -/
structure HasDistinguishingWFull.{u, v} (α : Type u) extends
    HasDistinguishingW.{u, v} α where
  /-- The two atoms are not Equiv (categorical distinctness). -/
  distinct_equiv : Equiv a b → False

/-! ### §3 — Combine on `GRA23`

The monoidal product `Monoidal.product` requires (2, 3)
parameter hypotheses.  We package them with `GRA23` so that
`combine : GRA23 → GRA23 → GRA23` is well-defined.
-/

/-- The monoidal product on `GRA23`, using the packaged
    parameter witnesses. -/
def gra23Combine (M N : GRA23) : GRA23 where
  model := product M.model N.model M.gen1_eq M.gen2_eq N.gen1_eq N.gen2_eq
  gen1_eq := rfl
  gen2_eq := rfl

/-- Equiv on `GRA23`: `GRAIso` between the underlying models. -/
def gra23Equiv (M N : GRA23) : Type := GRAIso M.model N.model

/-- Reflexivity of `gra23Equiv`. -/
def gra23Equiv_refl (M : GRA23) : gra23Equiv M M := GRAIso.refl M.model

/-- Symmetry. -/
def gra23Equiv_symm {M N : GRA23} (iso : gra23Equiv M N) : gra23Equiv N M :=
  GRAIso.symm iso

/-- Transitivity. -/
def gra23Equiv_trans {M N P : GRA23}
    (iso₁ : gra23Equiv M N) (iso₂ : gra23Equiv N P) : gra23Equiv M P :=
  GRAIso.trans iso₁ iso₂

/-- Combine is iso-symmetric via `productSwapIso`. -/
def gra23Combine_sym (M N : GRA23) :
    gra23Equiv (gra23Combine M N) (gra23Combine N M) :=
  productSwapIso M.model N.model M.gen1_eq M.gen2_eq N.gen1_eq N.gen2_eq

/-! ### §4 — Distinguished atoms on `GRA23` -/

/-- The `GRA23` value wrapping `trivial23`. -/
def trivial23_gra23 : GRA23 :=
  ⟨trivial23, rfl, rfl⟩

/-- The `GRA23` value wrapping `NumberTheory.GRA23_NT`. -/
def ntGRA23 : GRA23 :=
  ⟨NumberTheory.GRA23_NT, rfl, rfl⟩

/-- The two atoms are not iso: any would-be iso between the
    underlying models reduces to `trivial23_not_iso_NT`.

    `def` rather than `theorem` because `gra23Equiv` returns
    `Type` (carrying `GRAIso` data), so this is a
    `(Type 0) → False`-valued construction in `Type 1`, not a
    `Prop`-valued proof. -/
def trivial23_gra23_not_iso_ntGRA23 :
    gra23Equiv trivial23_gra23 ntGRA23 → False :=
  trivial23_not_iso_NT

/-! ### §5 — The full `HasDistinguishingWFull` instance on `GRA23`

Putting it all together: monoidal product + GRAIso equivalence
+ trivial-vs-NT distinguished atoms gives a full categorical
instance.
-/

/-- **Phase 21 capstone**: a full `HasDistinguishingWFull`
    instance on `GRA23`.  The two atoms are `trivial23` and
    `GRA23_NT`, the combine is monoidal product, the
    equivalence is GRAIso, and the iso-symmetric combine_sym
    is the swap iso from Phase 20.  The categorical
    distinctness is witnessed by `trivial23_not_iso_NT`.

    This realises the "natural Cat-level Reading" content:
    a `Type 1` carrier with categorically-distinct atoms,
    natural combine, and iso-symmetric combine_sym. -/
def gra23HasDistinguishingWFull :
    HasDistinguishingWFull.{1, 1} GRA23 where
  a := trivial23_gra23
  b := ntGRA23
  combine := gra23Combine
  Equiv := gra23Equiv
  refl := gra23Equiv_refl
  symm := gra23Equiv_symm
  trans := gra23Equiv_trans
  combine_sym := gra23Combine_sym
  distinct_equiv := trivial23_gra23_not_iso_ntGRA23

/-! ### §6 — Existence statement -/

/-- The existence of a categorically-distinct
    `HasDistinguishingWFull` instance at `Type 1` is now a
    Lean theorem.  The "Cat-as-Reading-of-GRA" content is
    formalised. -/
theorem hasDistinguishingWFull_witness :
    Nonempty (HasDistinguishingWFull.{1, 1} GRA23) :=
  ⟨gra23HasDistinguishingWFull⟩

end E213.Lib.Math.GRA.HasDistinguishingWFull
