import E213.Lib.Math.Algebra.GRA.GRAModel
import E213.Lib.Math.Algebra.GRA.Common
import E213.Lib.Math.Algebra.GRA.Monoidal
import E213.Lib.Math.Algebra.GRA.DepthFunctor
import E213.Lib.Math.Algebra.GRA.Category

/-!
# GRA HasDistinguishing213 — unified distinguishing typeclass

A consolidation pass over Phases 19–21 (`HasDistinguishingU`,
`HasDistinguishingW`, `HasDistinguishingWFull`).  Those three
were exploratory variants — each pinned one variation point:

  · Phase 19 `HasDistinguishingU.{u}` — universe-polymorphic
    over the base `HasDistinguishing` (strict `combine_sym`)
  · Phase 20 `HasDistinguishingW.{u, v}` — weakened
    `combine_sym` to hold up to an `Equiv` relation
  · Phase 21 `HasDistinguishingWFull` — added
    `distinct_equiv : Equiv a b → False` (categorical
    distinctness)

The exploration phase is over: every concrete instance
satisfies the strongest form (Phase 21).  The strict-equality
case is the `Equiv := Eq` instantiation of the same shape.
This file collapses the three into one universe-polymorphic
typeclass.

## The single typeclass

```lean
structure HasDistinguishing213.{u, v} (α : Type u) where
  a, b           : α
  combine        : α → α → α
  Equiv          : α → α → Sort v
  refl/symm/trans
  combine_sym    : ∀ x y, Equiv (combine x y) (combine y x)
  distinct_equiv : Equiv a b → False
```

For the strict case, instantiate `Equiv := Eq`, so
`distinct_equiv` reads as `Eq a b → False`, equivalently
`a ≠ b` — recovering the original strict distinctness.

For the categorical case (e.g., GRA23), instantiate
`Equiv := GRAIso` (Type-valued).

`Lens.SemanticAtom.HasDistinguishing` (at `Type 0`, sealed-by-
design per `STRICT_ZERO_AXIOM.md` category (a) — Prop-as-
distinguishing thesis) is structurally the
`HasDistinguishing213.{0, 0} α` form with `Equiv := Eq`, but
is left independent because its sealing rationale binds it to
the Lens-internal Prop-distinguishing role.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.GRA

open E213.Lib.Math.Algebra.GRA.DepthFunctor (GRA23)
open E213.Lib.Math.Algebra.GRA.Monoidal (product trivial23 TrivialCarrier)
open E213.Lib.Math.Algebra.GRA.Category (Reading)

/-! ### §1 — The unified typeclass -/

/-- The unified 213-native distinguishing structure.

    Universe-polymorphic in `u` (carrier universe) and `v`
    (equivalence-relation universe).  `Sort v`-valued `Equiv`
    accommodates both Prop-valued (Eq, when `v = 0`) and
    Type-valued (GRAIso, when `v ≥ 1`) equivalences.

    `distinct_equiv : Equiv a b → False` is the categorical
    distinctness condition — for `Equiv := Eq`, this reads as
    the original `a ≠ b`. -/
structure HasDistinguishing213.{u, v} (α : Type u) where
  /-- First atom. -/
  a : α
  /-- Second atom. -/
  b : α
  /-- Binary combination. -/
  combine : α → α → α
  /-- Equivalence relation (Sort-valued, allowing iso data). -/
  Equiv : α → α → Sort v
  /-- Reflexivity. -/
  refl : ∀ x, Equiv x x
  /-- Symmetry. -/
  symm : ∀ {x y : α}, Equiv x y → Equiv y x
  /-- Transitivity. -/
  trans : ∀ {x y z : α}, Equiv x y → Equiv y z → Equiv x z
  /-- Combination is commutative up to `Equiv`. -/
  combine_sym : ∀ x y, Equiv (combine x y) (combine y x)
  /-- The two atoms are not `Equiv` (categorical distinctness;
      reads as `a ≠ b` when `Equiv := Eq`). -/
  distinct_equiv : Equiv a b → False

/-! ### §2 — Swap iso for `Monoidal.product` (from Phase 20)

The natural categorical witness of "product is commutative up
to iso": for any `M₁, M₂` and the (2, 3)-parameter hypotheses,
there is a `GRAIso` between `product M₁ M₂` and `product M₂ M₁`.
The underlying map is the pair-swap `(a, b) ↦ (b, a)`.
-/

/-- Swap iso between `product M₁ M₂` and `product M₂ M₁`. -/
def productSwapIso (M₁ M₂ : GRAModel)
    (h1 : M₁.gen1 = 2) (h2 : M₁.gen2 = 3)
    (k1 : M₂.gen1 = 2) (k2 : M₂.gen2 = 3) :
    GRAIso (product M₁ M₂ h1 h2 k1 k2) (product M₂ M₁ k1 k2 h1 h2) where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  grade_comm p := by
    cases p with
    | mk x y =>
      show M₂.grade y + M₁.grade x = M₁.grade x + M₂.grade y
      rw [Nat.add_comm]
  oplus_comm p q := by cases p; cases q; rfl
  otimes_comm p q := by cases p; cases q; rfl

/-- The swap iso is involutive at the function level. -/
theorem productSwapIso_involutive (M₁ M₂ : GRAModel)
    (h1 : M₁.gen1 = 2) (h2 : M₁.gen2 = 3)
    (k1 : M₂.gen1 = 2) (k2 : M₂.gen2 = 3)
    (p : (product M₁ M₂ h1 h2 k1 k2).Carrier) :
    (productSwapIso M₂ M₁ k1 k2 h1 h2).toFun
      ((productSwapIso M₁ M₂ h1 h2 k1 k2).toFun p) = p := by
  cases p; rfl

/-- The product's grade is symmetric in its arguments. -/
theorem product_grade_sym (M₁ M₂ : GRAModel)
    (h1 : M₁.gen1 = 2) (h2 : M₁.gen2 = 3)
    (k1 : M₂.gen1 = 2) (k2 : M₂.gen2 = 3)
    (p : (product M₁ M₂ h1 h2 k1 k2).Carrier) :
    (product M₁ M₂ h1 h2 k1 k2).grade p =
    (product M₂ M₁ k1 k2 h1 h2).grade
      ((productSwapIso M₁ M₂ h1 h2 k1 k2).toFun p) := by
  cases p with
  | mk x y =>
    show M₁.grade x + M₂.grade y = M₂.grade y + M₁.grade x
    rw [Nat.add_comm]

/-- Existence statement: monoidal product is commutative up to
    `GRAIso`.  Phase 20's `combine_sym` witness. -/
theorem product_combine_sym_witness (M₁ M₂ : GRAModel)
    (h1 : M₁.gen1 = 2) (h2 : M₁.gen2 = 3)
    (k1 : M₂.gen1 = 2) (k2 : M₂.gen2 = 3) :
    Nonempty (GRAIso (product M₁ M₂ h1 h2 k1 k2)
                     (product M₂ M₁ k1 k2 h1 h2)) :=
  ⟨productSwapIso M₁ M₂ h1 h2 k1 k2⟩

/-! ### §3 — Categorical-distinctness lemma (from Phase 21)

The headline distinctness witness: no `GRAIso` exists between
`trivial23` (one-element `TrivialCarrier`) and
`NumberTheory.GRA23_NT` (`Nat` carrier).
-/

private theorem trivialCarrier_subsingleton :
    ∀ x y : TrivialCarrier, x = y := by
  intro x y; cases x; cases y; rfl

/-- No `GRAIso` from `trivial23` to `GRA23_NT`.

    Cardinality argument: any would-be iso has
    `invFun : Nat → TrivialCarrier`, but `TrivialCarrier` is
    a subsingleton, so `iso.invFun 0 = iso.invFun 1`.  Then
    `right_inv` forces `0 = 1`, contradiction. -/
def trivial23_not_iso_NT :
    GRAIso trivial23 NumberTheory.GRA23_NT → False := by
  intro iso
  let zero_nat : NumberTheory.GRA23_NT.Carrier := (0 : Nat)
  let one_nat : NumberTheory.GRA23_NT.Carrier := (1 : Nat)
  have h_inv_eq : iso.invFun zero_nat = iso.invFun one_nat :=
    trivialCarrier_subsingleton _ _
  have hr0 : iso.toFun (iso.invFun zero_nat) = zero_nat := iso.right_inv _
  have hr1 : iso.toFun (iso.invFun one_nat) = one_nat := iso.right_inv _
  rw [h_inv_eq] at hr0
  have h01 : zero_nat = one_nat := hr0.symm.trans hr1
  have h01_nat : (0 : Nat) = (1 : Nat) := h01
  exact absurd h01_nat (by decide)

/-! ### §4 — GRA23 instance (categorical case, Equiv := GRAIso) -/

/-- The monoidal product on `GRA23`. -/
def gra23Combine (M N : GRA23) : GRA23 where
  model := product M.model N.model M.gen1_eq M.gen2_eq N.gen1_eq N.gen2_eq
  gen1_eq := rfl
  gen2_eq := rfl

/-- `Equiv` on `GRA23`: `GRAIso` between underlying models. -/
def gra23Equiv (M N : GRA23) : Type := GRAIso M.model N.model

def gra23Equiv_refl (M : GRA23) : gra23Equiv M M := GRAIso.refl M.model

def gra23Equiv_symm {M N : GRA23} (iso : gra23Equiv M N) : gra23Equiv N M :=
  GRAIso.symm iso

def gra23Equiv_trans {M N P : GRA23}
    (iso₁ : gra23Equiv M N) (iso₂ : gra23Equiv N P) : gra23Equiv M P :=
  GRAIso.trans iso₁ iso₂

/-- Combine is iso-symmetric via `productSwapIso`. -/
def gra23Combine_sym (M N : GRA23) :
    gra23Equiv (gra23Combine M N) (gra23Combine N M) :=
  productSwapIso M.model N.model M.gen1_eq M.gen2_eq N.gen1_eq N.gen2_eq

/-- The `GRA23` value wrapping `trivial23`. -/
def trivial23_gra23 : GRA23 := ⟨trivial23, rfl, rfl⟩

/-- The `GRA23` value wrapping `NumberTheory.GRA23_NT`. -/
def ntGRA23 : GRA23 := ⟨NumberTheory.GRA23_NT, rfl, rfl⟩

/-- Distinctness for the GRA23 case.  Categorical: no `GRAIso`. -/
def trivial23_gra23_not_iso_ntGRA23 :
    gra23Equiv trivial23_gra23 ntGRA23 → False :=
  trivial23_not_iso_NT

/-- **The categorical-case instance**: full `HasDistinguishing213`
    on `GRA23 : Type 1` with `Equiv := GRAIso` (Type-valued).
    Replaces former `gra23HasDistinguishingWFull` (Phase 21). -/
def gra23HasDistinguishing213 :
    HasDistinguishing213.{1, 1} GRA23 where
  a := trivial23_gra23
  b := ntGRA23
  combine := gra23Combine
  Equiv := gra23Equiv
  refl := gra23Equiv_refl
  symm := gra23Equiv_symm
  trans := gra23Equiv_trans
  combine_sym := gra23Combine_sym
  distinct_equiv := trivial23_gra23_not_iso_ntGRA23

/-! ### §5 — ULift Reading instance (strict case, Equiv := Eq)

The `Type 1` instance via `ULift.{1, 0}` of the `Reading` enum.
With `Equiv := Eq`, this is the strict-equality form Phase 19
demonstrated, now expressed as a `HasDistinguishing213.{1, 0}`
instance.
-/

/-- The strict-commutative combine on `Reading` (used by both
    the `Type 0` and the lifted `Type 1` instances). -/
def readingCombine (r s : Reading) : Reading :=
  if r = s then r else .NT

theorem readingCombine_sym (r s : Reading) :
    readingCombine r s = readingCombine s r := by
  unfold readingCombine
  by_cases h : r = s
  · subst h; rfl
  · have h' : s ≠ r := fun heq => h heq.symm
    rw [if_neg h, if_neg h']

/-- The `Type 0` strict-equality instance on `Reading`. -/
def readingHasDistinguishing213 : HasDistinguishing213.{0, 0} Reading where
  a := .NT
  b := .Graph
  combine := readingCombine
  Equiv := Eq
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans
  combine_sym := readingCombine_sym
  distinct_equiv := by intro h; exact absurd h (by decide)

/-- Combine on the lifted carrier. -/
def liftedCombine (r s : ULift.{1, 0} Reading) : ULift.{1, 0} Reading :=
  ULift.up (readingCombine r.down s.down)

theorem liftedCombine_sym (r s : ULift.{1, 0} Reading) :
    liftedCombine r s = liftedCombine s r := by
  show ULift.up (readingCombine r.down s.down) =
       ULift.up (readingCombine s.down r.down)
  rw [readingCombine_sym]

private theorem lifted_distinct :
    (ULift.up Reading.NT : ULift.{1, 0} Reading) ≠ ULift.up Reading.Graph := by
  intro h
  have : Reading.NT = Reading.Graph := congrArg ULift.down h
  exact absurd this (by decide)

/-- **The strict-case instance**: full `HasDistinguishing213` on
    `ULift.{1, 0} Reading : Type 1` with `Equiv := Eq`.
    Replaces former `liftedReadingHasDistinguishingU` (Phase 19). -/
def liftedReadingHasDistinguishing213 :
    HasDistinguishing213.{1, 0} (ULift.{1, 0} Reading) where
  a := ULift.up Reading.NT
  b := ULift.up Reading.Graph
  combine := liftedCombine
  Equiv := Eq
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans
  combine_sym := liftedCombine_sym
  distinct_equiv := lifted_distinct

/-! ### §6 — Existence statements -/

/-- Categorical-case witness (Equiv := GRAIso). -/
theorem hasDistinguishing213_GRA23_witness :
    Nonempty (HasDistinguishing213.{1, 1} GRA23) :=
  ⟨gra23HasDistinguishing213⟩

/-- Strict-case witness (Equiv := Eq), at `Type 1` via ULift. -/
theorem hasDistinguishing213_ULiftReading_witness :
    Nonempty (HasDistinguishing213.{1, 0} (ULift.{1, 0} Reading)) :=
  ⟨liftedReadingHasDistinguishing213⟩

end E213.Lib.Math.Algebra.GRA
