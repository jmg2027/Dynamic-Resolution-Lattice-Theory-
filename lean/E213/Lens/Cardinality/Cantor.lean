import E213.Theory.Raw.API
import E213.Prelude

/-!
# Infinity.Cantor: Cantor's theorem, general + Raw-specialised

**Σ5.**  There is no surjection `X → (X → Bool)` for any type `X`.

The proof is the classical diagonal argument; it works for any
`X`.  Specialised at `X = Raw` it gives the infinity-as-Lens
thesis's central datum: the function space `Raw → Bool` is
strictly larger than `Raw` — yet the Raw-generating axiom
makes *no* cardinality claim.  Uncountability is a pure
observation, not an input.
-/

namespace E213.Lens.Cardinality

open E213.Theory

/-- **Cantor's theorem, generic form.**  For any type `X`,
    no function `f : X → (X → Bool)` is surjective. -/
theorem cantor_general {X : Type} :
    ¬ ∃ f : X → (X → Bool), Function.Surjective f := by
  rintro ⟨f, hf⟩
  let g : X → Bool := fun x => ! (f x x)
  obtain ⟨k, hk⟩ := hf g
  have hpoint : f k k = g k := congrFun hk k
  have hflip  : g k = ! (f k k) := rfl
  have hcontra : f k k = ! (f k k) := hpoint.trans hflip
  cases h : f k k
  · rw [h] at hcontra; exact Bool.noConfusion hcontra
  · rw [h] at hcontra; exact Bool.noConfusion hcontra

/-- **Σ5 — Cantor on Raw.** -/
theorem cantor_raw_bool :
    ¬ ∃ f : Raw → (Raw → Bool), Function.Surjective f :=
  cantor_general

end E213.Lens.Cardinality
