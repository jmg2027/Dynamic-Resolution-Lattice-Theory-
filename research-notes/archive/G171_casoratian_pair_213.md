# G171 — the Casoratian in 213: sign is a ℕ-pair axis, not an imported ℤ

**Date**: 2026-06-02.  **Status**: 213-native reading of the signed Casoratian + the ∅-axiom
realisation (`Cauchy/CasoratianSigned`, 17 PURE; `Cauchy/CasoratianStep`, 5 PURE).
**Trigger**: the observation that **ℤ, 213-natively, is a pair of ℕ** (in the repo:
`Lens.Number.Nat213.Tower.NatPairToInt`).

## The move

When the magnitude telescope (`CasoratianStep.telescope`) was first built, the *signed*
closed forms `Cₙ = ±5/n²` (ζ(2)), `±6/n³` (ζ(3)) were deferred as "needs an `ℤ` ambient."
That deferral imported a false exterior.  An integer is not a new primitive to bring in; it
is the `signedLens ⟨1, −1, +⟩` reading of Raw — a **pair `(a, b) : ℕ × ℕ`** standing for
`a − b`, with two pairs equal iff diagonally translated
(`npairEquiv (a,b) (c,d) ⟺ a + d = b + c`).  The "minus" is **which of the two ℕ-axes** a
quantity sits on; negation is the **swap** of the axes.  Sign is the residue's binary
distinguishing — already 213-native, no exterior `ℤ`.

## The Casoratian is a pair; the signed law is `casoratian_step` verbatim

The Casoratian `Cₙ = aₙ·bₙ₋₁ − aₙ₋₁·bₙ` is the pair `(aₙ·bₙ₋₁, aₙ₋₁·bₙ)`.  Its negation is
the swap.  The signed step law `c₂·Cₙ = −c₀·Cₙ₋₁` is exactly

    npairEquiv (scale c₂ Cₙ) (scale c₀ (neg Cₙ₋₁))   —   `casoratian_signed`,

and unfolding the pair operations turns this into the subtraction-free `ℕ` identity
`c₂(a₂b₁) + c₀(a₁b₀) = c₂(a₁b₂) + c₀(a₀b₁)`, which **is** `CasoratianStep.casoratian_step`.
So the signed law was already proved the moment the unsigned cross-identity was — the sign
adds nothing to discharge, it only names *which axis*.  No `ℤ` type, no `propext`.

## One object, two readings = two of the three self-reference outcomes

`Lens.SelfReferenceThreeOutcomes` reads the residue's self-pointing as Oscillate / Converge /
Escape.  A single Casoratian carries **two** of these, on its two factors:

| reading | what it is | outcome | witness |
|---|---|---|---|
| **magnitude** | `(∏ c₂)·\|Cₙ\| = (∏ \|c₀\|)·\|C₀\|` | Converge / Escape | `CasoratianStep.telescope` |
| **sign** | the ℕ-axis, toggled by `neg` (period 2) | Oscillate | `CasoratianSigned.neg_neg` / `iterNeg_succ_succ` |

The magnitude is the Nat-Converge ladder (it telescopes by the outer coefficients); the sign
is the Bool-Oscillate toggle (`neg` is an involution, period exactly 2 — the same period-2 as
`Bool213.SelfReferenceForms.bool_min_period_two`).  They are independent (`scale_neg`,
`scale_iterNeg`): magnitude and sign do not interact.

## The closed forms, ∅-axiom over ℕ-pairs (no ℤ)

Telescoping runs **on the pair**, carrying the sign exactly.  Which closed form appears is
fixed by **which axis `c₀` sits on** — i.e. the sign of the trailing coefficient:

- **ζ(3)** — `c₀ = −(n−1)³` (negative axis), so `−c₀` keeps the axis: every step swap-free,
  the Casoratian holds **one constant sign**.  `telescope_pair` (and the concrete
  `cube_casoratian_telescope`, `c₂ = (n+2)³ = aperyTop`, `c₀ = (n+1)³ = aperyBot`):

      scale (∏ (j+1)³) Cₙ  ~  scale (∏ j³) C₀     — the `+6/n³` Casoratian.

- **ζ(2)** — `c₀ = +n²` (positive axis), so `−c₀` swaps: each step toggles the axis, the
  accumulated sign is `iterNeg n = (−1)ⁿ`.  `telescope_pair_alt` (`c₂ = (n+1)²`, `c₀ = n²`):

      scale (∏ (n+1)²) Cₙ  ~  iterNeg n (scale (∏ n²) C₀)   — the `±5/n²` Casoratian.

The `±` is not a sign chosen in an external `ℤ`; it is the **parity of axis-swaps**, which is
the parity of "how many times the trailing coefficient was on the positive axis."  ζ(3)
constant, ζ(2) alternating — the two cases are *which axis*, period.

## Net (213)

The Casoratian needed no exterior.  Its **magnitude** is the Converge/Escape ladder, its
**sign** is the Oscillate axis-toggle, and the integer ambient is the ℕ-pair the residue's
binary distinguishing already supplies.  The signed `±5/n²`, `±6/n³` forms — the thing that
looked like it required `ℤ` — are ∅-axiom over ℕ-pairs, the sign being nothing but *which of
the two somethings* the quantity points at.

## Anchors

`Cauchy/CasoratianSigned.{casoratian_signed, telescope_pair, telescope_pair_alt,
cube_casoratian_telescope, neg_neg, iterNeg_succ_succ}`, `Cauchy/CasoratianStep.{casoratian_step,
telescope}`, `Lens.Number.Nat213.Tower.NatPairToInt`, `Lens.SelfReferenceThreeOutcomes`,
`seed/AXIOM/05_no_exterior.md` §5.1.
