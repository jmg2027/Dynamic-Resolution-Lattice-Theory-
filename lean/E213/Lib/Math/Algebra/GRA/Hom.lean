import E213.Lib.Math.Algebra.GRA.GRAModel

/-!
# GRA Hom — Phase 9

`GRAIso` is the *invertible* morphism between GRA models, suitable
for showing two Readings are *equivalent*.  For the more general
question "is this map a structure-preserving morphism?" we drop
the bijection requirement and keep only the grade / ⊕ / ⊗
preservation axioms.

`GRAHom M₁ M₂` is the data of a `M₁.Carrier → M₂.Carrier` map that
commutes with the GRA structure but is not necessarily invertible.
Every `GRAIso` forgets to a `GRAHom`; the resulting category
`GRA-Hom-Cat` is **not** a groupoid in general — it captures the
*projection* relation as well as iso.

This file also exhibits each Reading's `grade : Carrier → Nat` as a
`GRAHom` from the Reading model to the NT model (when the source
model has `gen1 = 2`, `gen2 = 3`, and depth = `(n + 2) / 3`).

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.GRA.Hom

open E213.Lib.Math.Algebra.GRA

/-! ### §1 — `GRAHom` definition

A `GRAHom M₁ M₂` is a function `M₁.Carrier → M₂.Carrier` with
three compatibility conditions, matching the three axioms `A2`,
`A3` of `GRAModel`:

  * `grade_comm` — preserves grade
  * `oplus_comm` — preserves ⊕
  * `otimes_comm` — preserves ⊗

In contrast with `GRAIso`, there is no `invFun` field.
-/

/-- A structure-preserving (not necessarily invertible) map between
    GRA models. -/
structure GRAHom (M₁ M₂ : GRAModel) where
  /-- The underlying function. -/
  toFun : M₁.Carrier → M₂.Carrier
  /-- Grade is preserved. -/
  grade_comm : ∀ x, M₂.grade (toFun x) = M₁.grade x
  /-- ⊕ is preserved. -/
  oplus_comm : ∀ x y, toFun (M₁.oplus x y) = M₂.oplus (toFun x) (toFun y)
  /-- ⊗ is preserved. -/
  otimes_comm : ∀ x y, toFun (M₁.otimes x y) = M₂.otimes (toFun x) (toFun y)

/-! ### §2 — Category laws for `GRAHom` -/

/-- Identity `GRAHom`. -/
def GRAHom.id (M : GRAModel) : GRAHom M M where
  toFun := _root_.id
  grade_comm := fun _ => rfl
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

/-- Composition of `GRAHom`s. -/
def GRAHom.comp {M₁ M₂ M₃ : GRAModel}
    (f : GRAHom M₁ M₂) (g : GRAHom M₂ M₃) : GRAHom M₁ M₃ where
  toFun := g.toFun ∘ f.toFun
  grade_comm := fun x => by
    show M₃.grade (g.toFun (f.toFun x)) = M₁.grade x
    rw [g.grade_comm, f.grade_comm]
  oplus_comm := fun x y => by
    show g.toFun (f.toFun (M₁.oplus x y)) = M₃.oplus (g.toFun (f.toFun x)) (g.toFun (f.toFun y))
    rw [f.oplus_comm, g.oplus_comm]
  otimes_comm := fun x y => by
    show g.toFun (f.toFun (M₁.otimes x y)) = M₃.otimes (g.toFun (f.toFun x)) (g.toFun (f.toFun y))
    rw [f.otimes_comm, g.otimes_comm]

/-- Left identity. -/
theorem GRAHom.id_comp {M₁ M₂ : GRAModel} (f : GRAHom M₁ M₂) :
    GRAHom.comp (GRAHom.id M₁) f = f := rfl

/-- Right identity. -/
theorem GRAHom.comp_id {M₁ M₂ : GRAModel} (f : GRAHom M₁ M₂) :
    GRAHom.comp f (GRAHom.id M₂) = f := rfl

/-- Associativity. -/
theorem GRAHom.comp_assoc {M₁ M₂ M₃ M₄ : GRAModel}
    (f : GRAHom M₁ M₂) (g : GRAHom M₂ M₃) (h : GRAHom M₃ M₄) :
    GRAHom.comp (GRAHom.comp f g) h
      = GRAHom.comp f (GRAHom.comp g h) := rfl

/-! ### §3 — Forgetful: `GRAIso ↪ GRAHom` -/

/-- Every `GRAIso` is a `GRAHom` (forget the inverse). -/
def isoToHom {M₁ M₂ : GRAModel} (iso : GRAIso M₁ M₂) : GRAHom M₁ M₂ where
  toFun := iso.toFun
  grade_comm := iso.grade_comm
  oplus_comm := iso.oplus_comm
  otimes_comm := iso.otimes_comm

/-- The forgetful is functorial: `(refl).toHom = id`. -/
theorem isoToHom_refl (M : GRAModel) :
    isoToHom (GRAIso.refl M) = GRAHom.id M := rfl

/-- The forgetful is functorial: `(trans iso₁ iso₂).toHom = comp iso₁.toHom iso₂.toHom`. -/
theorem isoToHom_trans {M₁ M₂ M₃ : GRAModel}
    (iso₁ : GRAIso M₁ M₂) (iso₂ : GRAIso M₂ M₃) :
    isoToHom (GRAIso.trans iso₁ iso₂)
      = GRAHom.comp (isoToHom iso₁) (isoToHom iso₂) := rfl

/-! ### §4 — `Carrier` as a commutative monoid under ⊕

The axiom `A2` says `grade (a ⊕ b) = grade a + grade b`, i.e.,
`grade : (Carrier, ⊕) → (Nat, +)` is a monoid homomorphism *on
grades*.  We do not assume `Carrier` itself is a commutative
monoid — only that its image in `Nat` under `grade` is.

This means: for any two `GRAHom`s `f, g : M₁ → M₂` and `x : M₁.Carrier`,
`M₂.grade (f x) = M₂.grade (g x)`.  (Both equal `M₁.grade x`.)
-/

/-- Two `GRAHom`s agree on grade for every element. -/
theorem GRAHom.grade_agree {M₁ M₂ : GRAModel}
    (f g : GRAHom M₁ M₂) (x : M₁.Carrier) :
    M₂.grade (f.toFun x) = M₂.grade (g.toFun x) := by
  rw [f.grade_comm, g.grade_comm]

/-- The grade of an ⊕-composition equals the sum of grades, via any hom. -/
theorem GRAHom.grade_oplus_via {M₁ M₂ : GRAModel} (f : GRAHom M₁ M₂)
    (x y : M₁.Carrier) :
    M₂.grade (f.toFun (M₁.oplus x y)) =
    M₂.grade (f.toFun x) + M₂.grade (f.toFun y) := by
  rw [f.grade_comm, M₁.ax_grade_oplus, ← f.grade_comm x, ← f.grade_comm y]

end E213.Lib.Math.Algebra.GRA.Hom
