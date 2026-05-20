import E213.Lens.Cardinality.Countable
import E213.Lens.Cardinality.Cantor
import E213.Prelude

/-!
# Infinity.BoolSpace: concrete `ℕ → (Raw → Bool)` injection

A companion to Σ5 (Cantor): an *explicit* injection
`nToRawBool : ℕ → (Raw → Bool)` showing that the function
space `Raw → Bool` has at least ℕ-many distinct members.

Combined with `cantor_raw_bool` (no surjection Raw → (Raw
→ Bool)), this pins down the strict inequality:
`Raw → Bool` is strictly larger than `Raw` (and at least
ℕ-sized, but in fact uncountable by Cantor).

Construction: `nToRawBool n` is the indicator of the
singleton `{rawTower n}` — true on exactly that one Raw.
Injectivity of `rawTower` (proved in `Countable`) lifts
to injectivity of `nToRawBool`.
-/

namespace E213.Lens.Cardinality

open E213.Theory

/-- Indicator of `{rawTower n}`. -/
def nToRawBool (n : Nat) : Raw → Bool :=
  fun r => decide (r = rawTower n)

/-- `nToRawBool n` evaluated at `rawTower n` is `true`. -/
theorem nToRawBool_self (n : Nat) :
    nToRawBool n (rawTower n) = true :=
  decide_eq_true (Eq.refl (rawTower n))

/-- `nToRawBool n` evaluated at `rawTower m` is `false`
    when `n ≠ m`. -/
theorem nToRawBool_other (n m : Nat) (hne : n ≠ m) :
    nToRawBool n (rawTower m) = false :=
  decide_eq_false (fun heq => hne (rawTower_injective heq).symm)

/-- **`nToRawBool` is injective.** -/
theorem nToRawBool_injective : Function.Injective nToRawBool := by
  intro n m heq
  have h1 : nToRawBool n (rawTower n) = nToRawBool m (rawTower n) :=
    congrFun heq _
  have h2 : nToRawBool m (rawTower n) = true := h1.symm.trans (nToRawBool_self n)
  have h3 : rawTower n = rawTower m := of_decide_eq_true h2
  exact rawTower_injective h3



/-- **`Raw → Bool` has at least ℕ-many distinct elements.** -/
theorem boolSpace_at_least_countable :
    ∃ f : Nat → (Raw → Bool), Function.Injective f :=
  ⟨nToRawBool, nToRawBool_injective⟩

/-- **Strict cardinality gap.**  There is an injection ℕ →
    (Raw → Bool) *and* no surjection Raw → (Raw → Bool).
    Combined with Σ3 (Raw ≥ ℕ), this establishes that
    the function space is strictly larger than Raw as a
    Cantor-style cardinality relation. -/
theorem cantor_gap_witnessed :
    (∃ f : Nat → (Raw → Bool), Function.Injective f)
      ∧ (¬ ∃ h : Raw → (Raw → Bool), Function.Surjective h) :=
  ⟨boolSpace_at_least_countable, cantor_raw_bool⟩

end E213.Lens.Cardinality
