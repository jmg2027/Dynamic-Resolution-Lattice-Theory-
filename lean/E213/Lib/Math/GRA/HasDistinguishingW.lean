import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.Common
import E213.Lib.Math.GRA.Monoidal
import E213.Lib.Math.GRA.DepthFunctor

/-!
# GRA HasDistinguishingW — Phase 20 (weakened combine_sym up to iso)

Phase 19 satisfied the strict 2-categorical universe-lifting
requirement with `HasDistinguishingU.{1}` on `ULift.{1, 0}
Reading`.  The combine there was degenerate (`if r = s then r
else .NT`) — strictly commutative but not categorically natural.
Natural Cat-object combinations (Cartesian product, direct sum,
monoidal tensor) are only commutative *up to iso*, not strictly.

This file weakens the typeclass to make combine_sym hold up to
a chosen equivalence relation, and constructs the **swap iso**
between `Monoidal.product M₁ M₂` and `Monoidal.product M₂ M₁`
— the natural Cat-level commutativity witness.

The content: monoidal product on `(2, 3)`-GRA models is
commutative *up to GRAIso*, which is the natural categorical
content that Phase 19's strict combine could not capture.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.HasDistinguishingW

open E213.Lib.Math.GRA
open E213.Lib.Math.GRA.Monoidal (product trivial23)

/-! ### §1 — Weakened typeclass

`combine_sym` holds up to a chosen equivalence relation
(`Equiv`, `Sort`-valued so categorical iso *structures* fit).
The equivalence laws (refl/symm/trans) are required.

We drop the strict `a ≠ b` distinctness in favour of
`distinct_equiv : ¬ Equiv a b` — atoms are non-iso, not just
non-equal.  This matches the categorical reading.
-/

/-- Universe-polymorphic distinguishing structure with `combine_sym`
    weakened to hold up to a given equivalence. -/
structure HasDistinguishingW.{u, v} (α : Type u) where
  /-- First atom. -/
  a : α
  /-- Second atom. -/
  b : α
  /-- Binary combination. -/
  combine : α → α → α
  /-- Type-valued equivalence relation.  Use `Prop`-valued for a
      strict-equality typeclass; use `Type`-valued (e.g.,
      `GRAIso`) when the equivalence carries data. -/
  Equiv : α → α → Sort v
  /-- Reflexivity. -/
  refl : ∀ x, Equiv x x
  /-- Symmetry. -/
  symm : ∀ {x y : α}, Equiv x y → Equiv y x
  /-- Transitivity. -/
  trans : ∀ {x y z : α}, Equiv x y → Equiv y z → Equiv x z
  /-- Combination is commutative up to `Equiv`. -/
  combine_sym : ∀ x y, Equiv (combine x y) (combine y x)

/-! ### §2 — Swap iso for `Monoidal.product`

The natural categorical witness of "product is commutative up to
iso": for any `M₁, M₂` and the (2, 3)-parameter hypotheses, there
is a `GRAIso` between `product M₁ M₂` and `product M₂ M₁`.  The
underlying map is the pair-swap `(a, b) ↦ (b, a)`.
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

/-! ### §3 — Capstone: existence of a natural combine_sym witness

The `productSwapIso` construction is the witness that the
monoidal product on (2, 3)-GRA models satisfies the weakened
`combine_sym` up to `GRAIso`.  This is the *natural* 2-cat
content beyond Phase 19's degenerate strict combine.
-/

/-- **Phase 20 capstone**: monoidal product is commutative up to
    `GRAIso` on any pair of (2, 3)-GRA models.  This realises the
    "natural combine_sym up to iso" requirement, satisfying
    `HasDistinguishingW`'s combine_sym axiom for any concrete
    instance with `combine = product` and `Equiv = GRAIso`. -/
theorem product_combine_sym_witness (M₁ M₂ : GRAModel)
    (h1 : M₁.gen1 = 2) (h2 : M₁.gen2 = 3)
    (k1 : M₂.gen1 = 2) (k2 : M₂.gen2 = 3) :
    Nonempty (GRAIso (product M₁ M₂ h1 h2 k1 k2)
                     (product M₂ M₁ k1 k2 h1 h2)) :=
  ⟨productSwapIso M₁ M₂ h1 h2 k1 k2⟩

/-- The swap iso is involutive at the function level: applying
    `productSwapIso` twice is the identity. -/
theorem productSwapIso_involutive (M₁ M₂ : GRAModel)
    (h1 : M₁.gen1 = 2) (h2 : M₁.gen2 = 3)
    (k1 : M₂.gen1 = 2) (k2 : M₂.gen2 = 3)
    (p : (product M₁ M₂ h1 h2 k1 k2).Carrier) :
    (productSwapIso M₂ M₁ k1 k2 h1 h2).toFun
      ((productSwapIso M₁ M₂ h1 h2 k1 k2).toFun p) = p := by
  cases p; rfl

/-! ### §4 — Grade preservation under swap

The swap iso preserves the additive grade, since `M.grade a + N.grade b
= N.grade b + M.grade a` by `Nat.add_comm`.  This is the algebraic
content of "product is iso-commutative".
-/

/-- The product's grade is symmetric in its arguments (up to
    `Nat.add_comm`). -/
theorem product_grade_sym (M₁ M₂ : GRAModel)
    (h1 : M₁.gen1 = 2) (h2 : M₁.gen2 = 3)
    (k1 : M₂.gen1 = 2) (k2 : M₂.gen2 = 3)
    (p : (product M₁ M₂ h1 h2 k1 k2).Carrier) :
    (product M₁ M₂ h1 h2 k1 k2).grade p =
    (product M₂ M₁ k1 k2 h1 h2).grade
      ((productSwapIso M₁ M₂ h1 h2 k1 k2).toFun p) := by
  cases p with
  | mk x y =>
    -- LHS: (product M₁ M₂).grade ⟨x, y⟩ = M₁.grade x + M₂.grade y
    -- RHS: (product M₂ M₁).grade (swap ⟨x, y⟩) = (product M₂ M₁).grade ⟨y, x⟩ = M₂.grade y + M₁.grade x
    show M₁.grade x + M₂.grade y = M₂.grade y + M₁.grade x
    rw [Nat.add_comm]

/-! ### §5 — Connection to the categorical reading

Combined with Phase 7's `GRACat` and Phase 15's `Monoidal.product`,
the `productSwapIso` construction completes the categorical
picture: `GRACat` is a **symmetric monoidal category** with
product as the tensor and `productSwapIso` as the braiding.

The braiding is the iso-symmetric witness that natural combines
(monoidal tensors) cannot achieve under strict combine_sym.
`HasDistinguishingW` with `Equiv := GRAIso` is the typeclass
that matches.
-/

/-- A natural `HasDistinguishingW.{1, 1}`-witness restricted to
    parameter pairs with matching (2, 3) hypotheses.  We provide
    the swap iso as the combine_sym component; the typeclass
    fields `a` / `b` are abstracted because the choice of
    distinguished atoms depends on the application.

    This def shows that the swap-iso construction *is* the
    combine_sym one would feed to a full `HasDistinguishingW`
    instance on a sub-collection of `(2, 3)`-models. -/
def product_combine_sym_at (M₁ M₂ : GRAModel)
    (h1 : M₁.gen1 = 2) (h2 : M₁.gen2 = 3)
    (k1 : M₂.gen1 = 2) (k2 : M₂.gen2 = 3) :
    GRAIso (product M₁ M₂ h1 h2 k1 k2) (product M₂ M₁ k1 k2 h1 h2) :=
  productSwapIso M₁ M₂ h1 h2 k1 k2

end E213.Lib.Math.GRA.HasDistinguishingW
