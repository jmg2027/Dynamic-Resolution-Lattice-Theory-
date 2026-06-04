# Marathon — the Eisenstein split converse (`p ≡ 1 mod 3 ⟹ p = a²−ab+b²`)

**Date**: 2026-06-04.  **Status**: open marathon (multi-session).  **Tier**: 1.

The capstone arc (`theory/math/numbertheory/eisenstein_period_arithmetic.md`) closed the
*necessary* side of the disc-`−3` representation (the χ₋₃ fingerprint) and the structural
foundations (class number one, the Euclidean covering bound).  This marathon targets the
*sufficient* side — the split converse — the disc-`−3` Fermat theorem:

> Every prime `p ≡ 1 (mod 3)` is a value of `a² − ab + b²` (`= N(π)` for a prime `π ∈ ℤ[ω]`).

## Two pillars

**Pillar I — quadratic-residue input.**  `p ≡ 1 (mod 3) ⟹ ∃ x, p ∣ x² + x + 1` (a
primitive cube root of unity mod `p`, i.e. an order-3 element of `(ℤ/p)ˣ`).  Needs the
cyclic structure of `(ℤ/p)ˣ` (primitive-root theorem) or a counting substitute.  The repo's
`ModArith` carries Fermat's little theorem universal in `p` (`UniversalFLT`) — a starting
foothold.

**Pillar II — Euclidean descent.**  `p ∣ x²+x+1` and `p ∤ (x − ω)` in `ℤ[ω]` ⟹ `p` is not
prime in `ℤ[ω]` ⟹ `p = N(π)`.  Rests on `ℤ[ω]` being norm-Euclidean (hence gcd / UFD).

## Phased plan

  - **Phase 1 — norm-Euclidean property of `ℤ[ω]`.**
    - 1a — centered integer division: `∀ A (N>0), ∃ q r, A = qN + r ∧ 2|r| ≤ N`.
    - 1b — the division step: `∀ α β, β ≠ 0 → ∃ γ ρ, α = βγ + ρ ∧ ‖ρ‖² < ‖β‖²`
      (round each coordinate of `α·conj β` by `‖β‖²`, then `covering_bound`).
  - **Phase 2 — gcd / divisibility in `ℤ[ω]`.**  Euclidean algorithm (well-founded on
    `‖·‖²`), gcd existence, the "non-prime ⟹ proper norm factor" descent.
  - **Phase 3 — Pillar I.**  The order-3 element mod `p` for `p ≡ 1 mod 3` (the hard
    number-theory pillar; may itself be a sub-marathon via the primitive-root theorem).
  - **Phase 4 — assembly.**  `p ≡ 1 mod 3 ⟹ p ∣ x²+x+1 ⟹ p = N(π) = a²−ab+b²`, closing the
    split converse, which upgrades `EisensteinSplitting`'s witnesses to the full theorem.

## Honest scope

Phase 1–2 are reachable with the pure `ℕ`/`ℤ` infrastructure (`div_add_mod`, `mod_lt`,
`covering_bound`, ZOmega `conj`/`normSq_mul`).  Phase 3 (primitive roots) is the deep pillar
and may not close from inside the reflection provers without a substantial cyclicity proof.
The transcendental period value remains separately out of reach (cubic AGM / `L(1,χ₋₃)`).

## Progress

  - **Phase 0 (done)** — `covering_bound` (`EisensteinEuclidean`): covering radius² ≤ 3/4 < 1.
  - **Phase 1a (DONE)** — `ModArith.CenteredDivision.centered_div` (2 PURE): centered division
    `∀ A (N>0), ∃ q r, A = qN + r ∧ 2|r| ≤ N`, built exactly per the scouting below.
  - **Phase 1b-infra (DONE)** — `Meta.Int213.OrderMul` (4 PURE): the pure `Int` multiplicative
    order lemmas the descent's final inequality needs (`mul_le_mul_right_nonneg`,
    `mul_le_mul_left_nonneg`, `int_sign` trichotomy, `mul_nonpos_of_nonneg_of_nonpos`) — the
    core versions are `propext`-dirty.  Remaining Phase 1b: the ZOmega assembly
    `∃ γ, ‖α−βγ‖² < ‖β‖²` using `β·conjβ = ofInt ‖β‖²`, `normSq_mul`, `covering_bound`,
    `centered_div`, and these order lemmas (sign-trichotomy contradiction `N ≤ ‖ρ‖² ⟹ 2N² ≤ 0`).
  - **Phase 1a (scouting record)** — centered division `∀ A (N>0), ∃ q r, A = qN + r ∧ 2|r| ≤ N`.
    Toolkit: pure Nat `AddMod213.div_add_mod` + `Nat.mod_lt` (both PURE) for the ordinary
    remainder, then center (subtract `N` when `2·(a%N) > N`).  **Purity caveat**: the core
    subtraction lemmas `Nat.sub_add_cancel`, `Nat.add_sub_cancel`, `Int.ofNat_sub` are
    `propext`-dirty — must route through the repo's pure replacements
    `NatRing213.nat_sub_add_cancel`, `NatRing213.nat_add_sub_self_right`,
    `Int213.Order.ofNat_sub_ofNat` (`ofNat b − ofNat a = subNatNat b a`).  Bound argument
    (`2(N−m) ≤ N` from `N < 2m`): `N−m ≤ m` via `Nat.sub_le_sub_right` (PURE) on `N ≤ 2m`,
    then `2(N−m) = (N−m)+(N−m) ≤ (N−m)+m = N`.  The negative-`A` case reduces by negation.
    Next increment: assemble this, then Phase 1b (the `ℤ[ω]` division step via `conj` +
    `normSq_mul` + `covering_bound`).
