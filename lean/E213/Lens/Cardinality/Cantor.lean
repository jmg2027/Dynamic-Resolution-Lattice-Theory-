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

/-! ## Cantor factors through the invariant-separation schema (one schema, cover-dependent `P`)

A multi-agent dialectic established that `cantor_general` is **not** a separate flavor of
non-surjection from the residue's spine escapes — it is an instance of the *same* schema
`CoResidue.escape_by_invariant` (an inhabitant lacking a property `P` that every cover-image has is
in the image of none).  The single separator is the **cover-dependent** (self-referential)
predicate `P_f φ := ∃ x, φ x = f x x` ("φ agrees with `f`'s own diagonal somewhere").  The genuine
distinction from the spine escapes is therefore *not* "two schemas" but the **self-reference of the
separator**: cover-independent / intrinsic (`hasFloorPath`, the *named* residue) vs cover-dependent /
diagonal (`P_f`, the *reached-by-none* residue forced by the cover's own self-application). -/

open E213.Theory.Raw.CoResidue (escape_by_invariant)

/-- `!b = b` is impossible (the fixpoint-free flip). -/
theorem bnot_self_ne : ∀ b : Bool, (! b) = b → False
  | true  => fun h => Bool.noConfusion h
  | false => fun h => Bool.noConfusion h

/-- ★★★ **Cantor factors through `escape_by_invariant`.**  The diagonal non-surjection is the
    invariant-separation schema at the **cover-dependent** separator `P_f φ := ∃ x, φ x = f x x`:
    every row `f a` satisfies it (at `x = a`, `rfl`); the flip `g x := !(f x x)` satisfies it
    nowhere (`bnot_self_ne`).  So `cantor_general` and the spine escapes (`gspine_escapes_via_schema`)
    are *one* schema — differing only in whether the separator is self-referential (this, Cantor)
    or intrinsic (`hasFloorPath`).  ∅-axiom. -/
theorem cantor_as_invariant {X : Type} :
    ¬ ∃ f : X → (X → Bool), Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨k, hk⟩ := hf (fun x => ! (f x x))
  exact escape_by_invariant f (fun φ => ∃ x, φ x = f x x) (fun x => ! (f x x))
    (fun ⟨x, hx⟩ => bnot_self_ne (f x x) hx) (fun a => ⟨a, rfl⟩) k hk

end E213.Lens.Cardinality
