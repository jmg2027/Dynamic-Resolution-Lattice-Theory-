import E213.Lib.Math.Algebra.GRA.GRAModel
import E213.Lib.Math.Algebra.GRA.Common
import E213.Lib.Math.Algebra.GRA.NumberTheory
import E213.Lib.Math.Algebra.GRA.Hom

/-!
# GRA Monoidal Product — Phase 15

The category `GRACat` of GRA models carries a **monoidal product**:
given two (2, 3)-GRA models `M₁` and `M₂`, their product
`M₁ ⊗_GRA M₂` is a (2, 3)-GRA model with carrier
`M₁.Carrier × M₂.Carrier`, grade `(a, b) ↦ M₁.grade a + M₂.grade b`,
and component-wise `⊕` and `⊗`.

The monoidal unit is the **trivial (2, 3)-GRA model**: a one-point
carrier with grade `≡ 0`, both operations the unique element, and
the depth function inherited from `Common.depth_formula`.

This file:
  * defines `product : GRAModel → GRAModel → GRAModel`
  * proves the product of two (2, 3)-models is again a (2, 3)-GRA
    model (all 7 axioms verified)
  * defines the trivial unit `trivial23`
  * gives the diagonal hom `M → product M M` (which IS a `GRAHom`,
    since `M.grade x + M.grade x = 2 · M.grade x`, but that fails
    the `grade_comm` axiom unless `M.grade x = 0`; we therefore
    only provide the *unit-paired* hom `M → product trivial23 M`)

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.GRA.Monoidal

open E213.Lib.Math.Algebra.GRA
open E213.Lib.Math.Algebra.GRA.Hom

/-! ### §1 — The trivial (2, 3)-GRA model -/

/-- Single-element carrier. -/
inductive TrivialCarrier : Type where
  | star

/-- Grade of the trivial carrier is 0. -/
def trivialGrade : TrivialCarrier → Nat := fun _ => 0

/-- Trivial ⊕. -/
def trivialOplus : TrivialCarrier → TrivialCarrier → TrivialCarrier :=
  fun _ _ => .star

/-- Trivial ⊗. -/
def trivialOtimes : TrivialCarrier → TrivialCarrier → TrivialCarrier :=
  fun _ _ => .star

/-- Depth on the trivial model is the universal `⌈n/3⌉`. -/
def trivialDepth (n : Nat) : Nat := (n + 2) / 3

/-- The trivial (2, 3)-GRA model.  Only one element, grade ≡ 0. -/
def trivial23 : GRAModel where
  Carrier := TrivialCarrier
  grade := trivialGrade
  oplus := trivialOplus
  otimes := trivialOtimes
  gen1 := 2
  gen2 := 3
  depth := trivialDepth
  ax_gen1_lt_gen2 := Common.two_lt_three
  ax_coprime := Common.coprime_2_3
  ax_grade_oplus := fun _ _ => rfl
  ax_grade_otimes := fun _ _ => Nat.zero_le _
  ax_reach := fun n hn => Common.reach_23 n hn
  ax_depth_eq := fun n _hn => Common.depth_formula n
  ax_greedy := fun n _hn => Common.greedy_form n

/-! ### §2 — Monoidal product of two GRA models -/

/-- The product carrier: pairs. -/
def ProductCarrier (M₁ M₂ : GRAModel) : Type := M₁.Carrier × M₂.Carrier

/-- Product grade: sum of component grades. -/
def productGrade (M₁ M₂ : GRAModel) :
    ProductCarrier M₁ M₂ → Nat :=
  fun p => M₁.grade p.1 + M₂.grade p.2

/-- Product ⊕: component-wise. -/
def productOplus (M₁ M₂ : GRAModel) :
    ProductCarrier M₁ M₂ → ProductCarrier M₁ M₂ → ProductCarrier M₁ M₂ :=
  fun p q => (M₁.oplus p.1 q.1, M₂.oplus p.2 q.2)

/-- Product ⊗: component-wise. -/
def productOtimes (M₁ M₂ : GRAModel) :
    ProductCarrier M₁ M₂ → ProductCarrier M₁ M₂ → ProductCarrier M₁ M₂ :=
  fun p q => (M₁.otimes p.1 q.1, M₂.otimes p.2 q.2)

/-! ### §3 — Product axioms (A2 + A3) -/

private theorem product_grade_oplus (M₁ M₂ : GRAModel)
    (p q : ProductCarrier M₁ M₂) :
    productGrade M₁ M₂ (productOplus M₁ M₂ p q) =
    productGrade M₁ M₂ p + productGrade M₁ M₂ q := by
  show M₁.grade (M₁.oplus p.1 q.1) + M₂.grade (M₂.oplus p.2 q.2) =
       (M₁.grade p.1 + M₂.grade p.2) + (M₁.grade q.1 + M₂.grade q.2)
  rw [M₁.ax_grade_oplus, M₂.ax_grade_oplus]
  rw [Nat.add_assoc (M₁.grade p.1) (M₁.grade q.1) _,
      ← Nat.add_assoc (M₁.grade q.1) (M₂.grade p.2) _,
      Nat.add_comm (M₁.grade q.1) (M₂.grade p.2),
      Nat.add_assoc (M₂.grade p.2) (M₁.grade q.1) _,
      ← Nat.add_assoc (M₁.grade p.1) (M₂.grade p.2) _]

private theorem product_grade_otimes (M₁ M₂ : GRAModel)
    (p q : ProductCarrier M₁ M₂) :
    productGrade M₁ M₂ (productOtimes M₁ M₂ p q) ≤
    productGrade M₁ M₂ p + productGrade M₁ M₂ q := by
  show M₁.grade (M₁.otimes p.1 q.1) + M₂.grade (M₂.otimes p.2 q.2) ≤
       (M₁.grade p.1 + M₂.grade p.2) + (M₁.grade q.1 + M₂.grade q.2)
  have h1 := M₁.ax_grade_otimes p.1 q.1
  have h2 := M₂.ax_grade_otimes p.2 q.2
  have hcomb := Nat.add_le_add h1 h2
  apply Nat.le_trans hcomb
  rw [Nat.add_assoc (M₁.grade p.1) (M₁.grade q.1) _,
      ← Nat.add_assoc (M₁.grade q.1) (M₂.grade p.2) _,
      Nat.add_comm (M₁.grade q.1) (M₂.grade p.2),
      Nat.add_assoc (M₂.grade p.2) (M₁.grade q.1) _,
      ← Nat.add_assoc (M₁.grade p.1) (M₂.grade p.2) _]
  exact Nat.le.refl

/-! ### §4 — The product (2, 3)-GRA model -/

/-- The monoidal product of two (2, 3)-GRA models. -/
def product (M₁ M₂ : GRAModel)
    (_h1 : M₁.gen1 = 2) (_h2 : M₁.gen2 = 3)
    (_k1 : M₂.gen1 = 2) (_k2 : M₂.gen2 = 3) : GRAModel where
  Carrier := ProductCarrier M₁ M₂
  grade := productGrade M₁ M₂
  oplus := productOplus M₁ M₂
  otimes := productOtimes M₁ M₂
  gen1 := 2
  gen2 := 3
  depth := fun n => (n + 2) / 3
  ax_gen1_lt_gen2 := Common.two_lt_three
  ax_coprime := Common.coprime_2_3
  ax_grade_oplus := product_grade_oplus M₁ M₂
  ax_grade_otimes := product_grade_otimes M₁ M₂
  ax_reach := fun n hn => Common.reach_23 n hn
  ax_depth_eq := fun n _hn => Common.depth_formula n
  ax_greedy := fun n _hn => Common.greedy_form n

/-! ### §5 — Left-unit hom: `trivial23 ⊗ M → M`

When the left factor is the trivial unit, `productGrade
trivial23 M (star, x) = 0 + M.grade x = M.grade x`, so the
projection `(star, x) ↦ x` IS a `GRAHom`.
-/

/-- Left-unit projection: `trivial23 ⊗ M → M`. -/
def leftUnitHom (M : GRAModel)
    (k1 : M.gen1 = 2) (k2 : M.gen2 = 3) :
    GRAHom (product trivial23 M rfl rfl k1 k2) M where
  toFun := fun p => p.2
  grade_comm := fun p => by
    show M.grade p.2 = trivialGrade p.1 + M.grade p.2
    show M.grade p.2 = 0 + M.grade p.2
    rw [Nat.zero_add]
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

/-- Right-unit projection: `M ⊗ trivial23 → M`. -/
def rightUnitHom (M : GRAModel)
    (k1 : M.gen1 = 2) (k2 : M.gen2 = 3) :
    GRAHom (product M trivial23 k1 k2 rfl rfl) M where
  toFun := fun p => p.1
  grade_comm := fun p => by
    show M.grade p.1 = M.grade p.1 + trivialGrade p.2
    show M.grade p.1 = M.grade p.1 + 0
    rw [Nat.add_zero]
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

/-! ### §6 — Sanity: the product of two `NT` models is again
a (2, 3)-model with grade = sum -/

/-- `product NT NT` has grade `(a, b) ↦ a + b`. -/
theorem product_NT_NT_grade (p : Nat × Nat) :
    (product NumberTheory.GRA23_NT NumberTheory.GRA23_NT
      rfl rfl rfl rfl).grade p = p.1 + p.2 := rfl

end E213.Lib.Math.Algebra.GRA.Monoidal
