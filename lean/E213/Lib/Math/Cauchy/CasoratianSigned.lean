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

/-! ## §3 — the signed telescope: ζ(3)'s `1/n³` Casoratian as a constant-sign ℕ-pair

With the sign native (a ℕ-pair axis), the telescoping of the signed step law runs *on the
pair*, carrying the sign exactly.  For ζ(3) the trailing coefficient `c₀ = −(n−1)³` is on the
negative axis, so `−c₀` keeps the axis: every step is swap-free and the Casoratian holds one
**constant** sign.  This section telescopes that swap-free case to the closed pair form
`scale (∏ P) Cₙ ~ scale (∏ Q) C₀` — the `1/n³` denominator with a fixed sign, ∅-axiom, no
`ℤ`.  (ζ(2)'s `c₀ = +n²` is on the positive axis ⟹ a swap each step ⟹ the sign is
`iterNeg n` = `(−1)ⁿ`; the period-2 `iterNeg` infrastructure below carries it.) -/

open E213.Lens.Number.Nat213.Tower.NatPairToInt (npairEquiv_refl npairEquiv_trans)
open E213.Lib.Math.Cauchy.CasoratianStep (prodFrom)
open E213.Tactic.NatHelper (mul_assoc)

/-- `scale (a·b) p = scale a (scale b p)` — scaling factors through the pair. -/
theorem scale_mul (a b : Nat) (p : NPair) : scale (a * b) p = scale a (scale b p) := by
  show (a * b * p.1, a * b * p.2) = (a * (b * p.1), a * (b * p.2))
  rw [mul_assoc a b p.1, mul_assoc a b p.2]

/-- Scaling factors commute: `scale a (scale b p) = scale b (scale a p)`. -/
theorem scale_comm (a b : Nat) (p : NPair) : scale a (scale b p) = scale b (scale a p) := by
  rw [← scale_mul a b p, ← scale_mul b a p, Nat.mul_comm a b]

/-- `npairEquiv` is a congruence for `scale`: equal integers stay equal when scaled. -/
theorem scale_congr (c : Nat) {p q : NPair} (h : npairEquiv p q) :
    npairEquiv (scale c p) (scale c q) := by
  have h' : p.1 + q.2 = p.2 + q.1 := h
  show c * p.1 + c * q.2 = c * p.2 + c * q.1
  rw [← Nat.mul_add c p.1 q.2, ← Nat.mul_add c p.2 q.1, h']

/-- `npairEquiv` is a congruence for the sign toggle `neg`. -/
theorem neg_congr {p q : NPair} (h : npairEquiv p q) : npairEquiv (neg p) (neg q) :=
  (show p.1 + q.2 = p.2 + q.1 from h).symm

/-- Apply the sign toggle `n` times — the accumulated sign over `n` swaps. -/
def iterNeg : Nat → NPair → NPair
  | 0,   p => p
  | k+1, p => neg (iterNeg k p)

/-- The accumulated sign has period 2 (the Oscillate outcome): `iterNeg (k+2) = iterNeg k`. -/
theorem iterNeg_succ_succ (k : Nat) (p : NPair) : iterNeg (k+2) p = iterNeg k p :=
  neg_neg (iterNeg k p)

/-- Scaling commutes through the accumulated sign: `scale c (iterNeg n p) = iterNeg n (scale
    c p)` (magnitude and sign independent at every depth). -/
theorem scale_iterNeg (c : Nat) : ∀ n p, scale c (iterNeg n p) = iterNeg n (scale c p)
  | 0,   _ => rfl
  | n+1, p => by
      show scale c (neg (iterNeg n p)) = neg (iterNeg n (scale c p))
      rw [scale_neg, scale_iterNeg c n p]

/-- ★★★ **The constant-sign signed telescope (ζ(3) shape).**  If the pair Casoratian `C`
    obeys the swap-free step law `P(k+1)·C(k+1) = Q(k+1)·C(k)` (as a `npairEquiv`, with `Q =
    −c₀ = (n−1)³` on the same axis — ζ(3)'s case), then it telescopes to
    `scale (∏_{k≤n} P k) (C n) ~ scale (∏_{k≤n} Q k) (C 0)` — the running products of the
    outer coefficients carry the Casoratian back to `C 0` with **one constant sign**.  For
    ζ(3) (`P = n³`, `Q = (n−1)³`) this is exactly the `1/n³` Casoratian denominator, sign
    included, ∅-axiom over ℕ-pairs (no `ℤ`).  Proof: `npairEquiv` transitivity through the
    `scale`-congruence and `scale`-commutation. -/
theorem telescope_pair (P Q : Nat → Nat) (C : Nat → NPair)
    (h : ∀ k, npairEquiv (scale (P (k+1)) (C (k+1))) (scale (Q (k+1)) (C k))) :
    ∀ n, npairEquiv (scale (prodFrom P n) (C n)) (scale (prodFrom Q n) (C 0))
  | 0   => npairEquiv_refl _
  | n+1 => by
      show npairEquiv (scale (prodFrom P n * P (n+1)) (C (n+1)))
                      (scale (prodFrom Q n * Q (n+1)) (C 0))
      rw [scale_mul (prodFrom P n) (P (n+1)) (C (n+1)),
          scale_mul (prodFrom Q n) (Q (n+1)) (C 0)]
      refine npairEquiv_trans (scale_congr (prodFrom P n) (h n)) ?_
      rw [scale_comm (prodFrom P n) (Q (n+1)) (C n),
          scale_comm (prodFrom Q n) (Q (n+1)) (C 0)]
      exact scale_congr (Q (n+1)) (telescope_pair P Q C h n)

/-- ★★★ **The alternating-sign signed telescope (ζ(2) shape).**  If the pair Casoratian `C`
    obeys the swap-each-step law `P(k+1)·C(k+1) = Q(k+1)·(neg C(k))` (as a `npairEquiv`, with
    `Q = c₀ = n²` on the positive axis — ζ(2)'s case, where `−c₀` swaps), then it telescopes
    to `scale (∏ P) (C n) ~ iterNeg n (scale (∏ Q) (C 0))` — the running products carry the
    Casoratian back to `C 0` with the **accumulated sign `(−1)ⁿ`** (`iterNeg n`, period 2).
    For ζ(2) (`P = (n+1)²`, `Q = n²`) this is exactly the alternating `±5/n²` Casoratian,
    sign included, ∅-axiom over ℕ-pairs (no `ℤ`). -/
theorem telescope_pair_alt (P Q : Nat → Nat) (C : Nat → NPair)
    (h : ∀ k, npairEquiv (scale (P (k+1)) (C (k+1))) (scale (Q (k+1)) (neg (C k)))) :
    ∀ n, npairEquiv (scale (prodFrom P n) (C n)) (iterNeg n (scale (prodFrom Q n) (C 0)))
  | 0   => npairEquiv_refl _
  | n+1 => by
      show npairEquiv (scale (prodFrom P n * P (n+1)) (C (n+1)))
                      (iterNeg (n+1) (scale (prodFrom Q n * Q (n+1)) (C 0)))
      rw [scale_mul (prodFrom P n) (P (n+1)) (C (n+1))]
      refine npairEquiv_trans (scale_congr (prodFrom P n) (h n)) ?_
      rw [scale_comm (prodFrom P n) (Q (n+1)) (neg (C n)), scale_neg (prodFrom P n) (C n)]
      have rhs_eq : iterNeg (n+1) (scale (prodFrom Q n * Q (n+1)) (C 0))
                  = scale (Q (n+1)) (neg (iterNeg n (scale (prodFrom Q n) (C 0)))) := by
        show neg (iterNeg n (scale (prodFrom Q n * Q (n+1)) (C 0)))
           = scale (Q (n+1)) (neg (iterNeg n (scale (prodFrom Q n) (C 0))))
        rw [Nat.mul_comm (prodFrom Q n) (Q (n+1)), scale_mul (Q (n+1)) (prodFrom Q n) (C 0),
            ← scale_iterNeg (Q (n+1)) n (scale (prodFrom Q n) (C 0)),
            ← scale_neg (Q (n+1)) (iterNeg n (scale (prodFrom Q n) (C 0)))]
      rw [rhs_eq]
      exact scale_congr (Q (n+1)) (neg_congr (telescope_pair_alt P Q C h n))

end E213.Lib.Math.Cauchy.CasoratianSigned
