import E213.Lib.Math.Cauchy.CasoratianStep
import E213.Lens.Number

/-!
# CasoratianSigned — the *signed* Casoratian law, with the sign as a ℕ-pair swap

`CasoratianStep.casoratian_step` proved the subtraction-free `ℕ` identity behind
`c₂(n)·Cₙ = −c₀(n)·Cₙ₋₁`, but deliberately stopped short of the *signed* closed form
(`Cₙ = ±5/n²`, `±6/n³`), noting that needed an `ℤ` ambient.

That ambient is **not external to 213**.  An integer is, 213-natively, a *pair of `ℕ`* — the
`signedLens ⟨1, −1, +⟩` reading of Raw, materialised as `Lens.Number.Nat213.Tower.NatPairToInt`:
`(a, b) : ℕ × ℕ` is the integer `a − b`, two pairs equal iff diagonally translated
(`npairEquiv (a,b) (c,d) ⟺ a + d = b + c`).  The "minus" is not an imported operation; it is
**which of the two ℕ-axes** a quantity sits on — the residue's binary distinguishing itself.
Negation is the **swap** of the two axes (`swap_realizes_negation`).

Read this way, the Casoratian `Cₙ = aₙ·bₙ₋₁ − aₙ₋₁·bₙ` is the pair `(aₙ·bₙ₋₁, aₙ₋₁·bₙ)`, its
negation is the swap, and the *signed* step law `c₂·Cₙ = −c₀·Cₙ₋₁` is precisely the
`npairEquiv` of the scaled pair against the **swapped** scaled predecessor:

    npairEquiv (scale c₂ Cₙ) (scale c₀ (swap Cₙ₋₁)).

Unfolding the pair operations, this `npairEquiv` is *exactly* `casoratian_step` — so the
signed law holds ∅-axiom over `ℕ`, with the sign carried by the swap.  No `ℤ` type, no
`propext`; the integer is the pair, the minus is the axis-choice.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.CasoratianSigned

open E213.Lens.Number.Nat213.Tower.NatPairToInt (NPair npairEquiv)
open E213.Lib.Math.Cauchy.CasoratianStep (casoratian_step)

/-- Negation as the swap of the two ℕ-axes (the residue's binary distinguishing: which
    component carries the quantity). -/
def neg (p : NPair) : NPair := (p.2, p.1)

/-- Scale both ℕ-axes by `c`. -/
def scale (c : Nat) (p : NPair) : NPair := (c * p.1, c * p.2)

/-- The Casoratian as a difference-pair: `x − y` is the pair `(x, y)`.  For the 3-term
    recurrence at level `n`, `Cₙ = aₙ·bₙ₋₁ − aₙ₋₁·bₙ = casPair (aₙ·bₙ₋₁) (aₙ₋₁·bₙ)`. -/
def casPair (x y : Nat) : NPair := (x, y)

/-- ★★★ **The signed Casoratian step law, ∅-axiom over `ℕ`.**  For any solutions `a, b` of
    `c₂·x₂ = c₁·x₁ + c₀·x₀`, the scaled Casoratian pair `scale c₂ Cₙ` (with
    `Cₙ = casPair (a₂·b₁) (a₁·b₂)`) is `npairEquiv` to the scaled **swapped** predecessor
    `scale c₀ (neg Cₙ₋₁)` (with `Cₙ₋₁ = casPair (a₁·b₀) (a₀·b₁)`).  This *is* the signed
    `c₂·Cₙ = −c₀·Cₙ₋₁`: the negation is the axis-swap, the equality is the diagonal quotient,
    and unfolding the pair operations reduces it to `casoratian_step` verbatim.  The sign is
    native — it is the pair, not an imported `ℤ`. -/
theorem casoratian_signed
    (c₂ c₁ c₀ a₀ a₁ a₂ b₀ b₁ b₂ : Nat)
    (ha : c₂ * a₂ = c₁ * a₁ + c₀ * a₀)
    (hb : c₂ * b₂ = c₁ * b₁ + c₀ * b₀) :
    npairEquiv (scale c₂ (casPair (a₂ * b₁) (a₁ * b₂)))
               (scale c₀ (neg (casPair (a₁ * b₀) (a₀ * b₁)))) := by
  show c₂ * (a₂ * b₁) + c₀ * (a₁ * b₀) = c₂ * (a₁ * b₂) + c₀ * (a₀ * b₁)
  exact casoratian_step c₂ c₁ c₀ a₀ a₁ a₂ b₀ b₁ b₂ ha hb

/-! ## §2 — the sign is period-2 (the Oscillate outcome); the magnitude is Converge/Escape

The Casoratian carries **two co-present readings** (the `SelfReferenceThreeOutcomes` frame):
its **magnitude** telescopes by the outer coefficients (`CasoratianStep.telescope` —
the Nat-Converge / residue-Escape axis), and its **sign** is the ℕ-pair axis, toggled by
`neg` (swap).  The sign reading is the **Oscillate** outcome: `neg` is an involution (period
exactly 2, no fixed point off the diagonal), so iterating the signed step law produces a
sign that depends only on the *parity* of negative-axis steps — constant for ζ(3) (`c₀ =
−(n−1)³`, the multiplier `−c₀` keeps the axis) and alternating `(−1)ⁿ` for ζ(2) (`c₀ = +n²`,
each step swaps).  Same Bool toggle as `Bool213.SelfReferenceForms.bool_min_period_two`. -/

/-- ★ **Negation is an involution** — the sign toggle has period exactly 2 (`neg∘neg = id`),
    the Oscillate outcome on the ℕ-pair axis.  Two Casoratian steps restore the axis; the
    accumulated sign over `n` steps is the parity of negative-axis steps. -/
theorem neg_neg (p : NPair) : neg (neg p) = p := rfl

/-- Scaling commutes with the sign toggle: `scale c (neg p) = neg (scale c p)` — the
    magnitude (Converge/Escape, telescoped) and the sign (Oscillate, `neg`) are independent
    readings of the one pair. -/
theorem scale_neg (c : Nat) (p : NPair) : scale c (neg p) = neg (scale c p) := rfl

end E213.Lib.Math.Cauchy.CasoratianSigned
