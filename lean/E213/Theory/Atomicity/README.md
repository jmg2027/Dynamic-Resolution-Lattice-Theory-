# Firmware/Atomicity/ — Raw axiom shape forced uniqueness

These are the proofs that the Raw axiom's atomic structure (d=5, NS=3,
NT=2, primitive sizes {2,3}, arity k=2, alive-pair (1,1)) is the
**unique consistent choice** under abstract structural conditions.

## Theoretical role

Each file is a pure-ℕ theorem.  None of them imports `Firmware/Raw.lean`.
They are NOT consequences of Raw — they are **predictions of Raw's
shape from outside**.  The Firmware Raw axiom is then justified
*because* it instantiates the unique structure these theorems force.

This is what previously sat in `OS/` (a misnomer) and has now been
migrated into Firmware/ where it belongs theoretically: the shape-
forcing proof obligations of the axiom layer.

## Files

| File | Proof |
|---|---|
| `Five.lean` | n = 2a + 3b alive-unique ⇔ n = 5 |
| `PairForcing.lean` | (2, 3) is the unique coprime pair with a unique atomic n |
| `NonDecomposable.lean` | {2, 3} are exactly the non-decomposable integers ≥ 2 |
| `Alive.lean` | "alive" predicate (both atom-multiplicities odd) |
| `ArityForcing.lean` | k = 2 is the unique non-degenerate, non-vacuous arity |
| `ArityForcingGeneral.lean` | for N < k, no Reachable relation exists (pigeonhole) |
| `PrimitiveSizes.lean` | atom set {pairSize=2, closureSize=3} from the axiom |

## Migration history

  - 2026-05-01: created as `OS/` (misnomer)
  - 2026-05-XX: migrated to `Firmware/Atomicity/` per architectural
    correction.  See HANDOFF for details.

The general-purpose `Pigeonhole.lean` was moved separately to
`Math/Pigeonhole.lean` (universal Fin infrastructure, not atomicity-
specific).
