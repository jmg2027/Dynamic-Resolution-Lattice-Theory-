# `Meta/Nat/` — ring-independent Nat helper lemmas

Pure-Nat helper lemmas that don't depend on the Theory / Lens
ring distinction.  Promoted from `Lib/Math/NatHelpers/` 2026-05-13
(Session E) — these were ring-independent and belonged in Meta.

## Files (8)

  - `PureNat.lean`         — pure-Nat building blocks
  - `NatDiv213.lean`       — `Nat.div` lemmas (213-internal pattern)
  - `AddMod213.lean`       — `Nat.add` mod-arithmetic
  - `Gcd213.lean`          — GCD without Mathlib (Euclidean)
  - `IntHelpers.lean`      — Int helpers (built on Nat)
  - `Max213.lean`          — max / min combinators
  - `BinomSymm.lean`       — binomial-coefficient symmetry
  - `EncodePair213.lean`   — injective `ℕ × ℕ → ℕ` pairing

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
