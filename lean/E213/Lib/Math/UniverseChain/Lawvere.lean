import E213.Lib.Math.Infinity.Cantor

/-!
# Lawvere fixed-point theorem (∅-axiom)

The unifying mechanism behind Russell, Curry, Girard, and Cantor.

## Statement

For any types `X`, `A` and `f : X → X → A`, if `f` is *point-
surjective* — i.e. for every `φ : X → A` some `x : X` satisfies
`f x = φ` — then every endomorphism `g : A → A` has a fixed
point.

## Why this matters for self-reference

Russell / Curry / Girard / Cantor are all instances of:

  > If `X` admits a surjection onto `X → A`, then every `g : A → A`
  > has a fixed point in `A`.

The *paradoxes* arise when we exhibit `g : A → A` with **no**
fixed point (e.g. `g = !` on `A = Bool` for Cantor; `g = (· → ⊥)`
on `A = Prop` for Curry); the surjection-existence assumption is
then contradicted, so the surjection cannot exist.

## ∅-axiom

The proof is the classical diagonal — pure term-mode
construction.  No `propext`, no `Quot.sound`, no `Classical`.
-/

namespace E213.Lib.Math.UniverseChain.Lawvere

/-- **Lawvere fixed-point theorem.** If `f : X → X → A` is point-
    surjective then every `g : A → A` has a fixed point. -/
theorem lawvere_fixed_point {X A : Type}
    (f : X → X → A)
    (hf : ∀ φ : X → A, ∃ x : X, f x = φ)
    (g : A → A) : ∃ a : A, g a = a :=
  match hf (fun x => g (f x x)) with
  | ⟨x_g, hx_g⟩ =>
      ⟨f x_g x_g, (congrFun hx_g x_g).symm⟩

/-- The endomorphism `!` on `Bool` has no fixed point. -/
theorem not_has_no_fixed_point : ¬ ∃ b : Bool, (!b) = b
  | ⟨true,  hb⟩ => Bool.noConfusion hb
  | ⟨false, hb⟩ => Bool.noConfusion hb

/-- **Cantor via Lawvere.**  The non-existence of a fixed point of
    `!` on `Bool` directly *contrapositive*-implies the non-existence
    of a `Bool`-surjection from any `X`. -/
theorem cantor_via_lawvere (X : Type) :
    ¬ ∃ f : X → X → Bool, Function.Surjective f
  | ⟨f, hf⟩ =>
      not_has_no_fixed_point (lawvere_fixed_point f hf (fun b => !b))

/-- ★★★ **The Lawvere–Cantor link.**  Both forms agree
    (the existing `Infinity.Cantor.cantor_general` is recovered). -/
theorem cantor_lawvere_agree (X : Type) :
    (¬ ∃ f : X → X → Bool, Function.Surjective f)
    ∧ (¬ ∃ f : X → X → Bool, Function.Surjective f) :=
  ⟨cantor_via_lawvere X, E213.Infinity.cantor_general⟩

end E213.Lib.Math.UniverseChain.Lawvere
