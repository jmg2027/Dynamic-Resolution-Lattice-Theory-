# `Meta/Nat/` — ring-independent Nat helper lemmas

Pure-Nat helper lemmas that don't depend on the Theory / Lens
ring distinction.  Promoted from `Lib/Math/NatHelpers/` 2026-05-13
(Session E) — these were ring-independent and belonged in Meta.

## Files (18)

  - `PureNat.lean`         — pure-Nat building blocks
  - `NatDiv213.lean`       — `Nat.div` lemmas (213-internal pattern)
  - `AddMod213.lean`       — `Nat.add` mod-arithmetic
  - `MulMod213.lean`       — `Nat.mul` mod-arithmetic
  - `ModPow213.lean`       — modular exponentiation lemmas
  - `Gcd213.lean`          — GCD without Mathlib (Euclidean)
  - `IntHelpers.lean`      — Int helpers (built on Nat)
  - `Max213.lean`          — max / min combinators
  - `Beq213.lean`          — `Nat.beq` cancellation helpers
  - `BinomSymm.lean`       — binomial-coefficient symmetry
  - `EncodePair213.lean`   — injective `ℕ × ℕ → ℕ` pairing
  - `NatRing213.lean`      — ring-shaped `Nat` rearrangement lemmas
  - `PolyNat.lean`         — ∅-axiom reflection prover, univariate `Nat`
                             polynomial identities (`poly_id`)
  - `PolyNatM.lean`        — multivariate `PolyNat` reflection core
  - `PolyNatMTactic.lean`  — tactic frontend for `PolyNatM`
  - `PowBasic.lean`        — `Nat.pow` comparison toolkit, arbitrary base
                             (base-2: `Meta/Tactic/Pow213`)
  - `RootFloor.lean`       — integer `s`-th root, floor reading
                             (`rootFloor_pow` calibration; the graded
                             rate generator's probe schedule)
  - `Valuation.lean`       — the `q`-adic valuation `vp q n` over ℕ

## Top-level

  - `Meta/Nat.lean` aggregator

## Where to add new files

  - New Nat lemma (ring-indep)   → `<name>213.lean`
  - Int helper                   → `IntHelpers.lean` (consolidate
                                    where possible)
  - Pairing / encoding           → `EncodePair213` or new
                                    `Encode<...>.lean`

## Discipline

Files in this cluster MUST be ring-independent (no Theory / Lens
/ Lib imports beyond `E213.Prelude`).  Promotion criteria:
  - Pure Nat / Int arithmetic
  - Used across multiple rings
  - No commitment to the 213 axiom set (Raw / Lens)
