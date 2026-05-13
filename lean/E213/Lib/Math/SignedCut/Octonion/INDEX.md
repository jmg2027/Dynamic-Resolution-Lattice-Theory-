# `SignedCut/Octonion/` — octonion multiplication + non-associativity

SignedCut applied at Cayley-Dickson level-4 (octonion).  Multiplication
table, generic rule, non-associativity witness.  Quaternion (level-3)
included as cousin for cross-reference.

## Files (6)

  - `OctonionBasisAlgebra.lean`    — octonion basis e₁..e₇
  - `OctonionMulTable.lean`        — explicit 8×8 mul table
  - `OctonionMulRule.lean`         — generic mul rule
  - `OctonionNonAssociativity.lean`— non-assoc witness (vs quaternion)
  - `QuaternionMulTable.lean`      — quaternion 4×4 mul table
  - `QuaternionMulRule.lean`       — quaternion generic mul rule

## Companion sub-clusters (in `SignedCut/`)

  - `Core/`     — base signed-cut
  - `CD/`       — CD level operations
  - `Hurwitz/`  — Hurwitz integer signed
  - `Level/`    — level tower

## Where to add new files

  - Higher-level (Sedenion, level-5)  → `Sedenion<...>.lean`
  - Non-associativity / quasi-axiom   → `<Level>NonAssociativity*`
  - Mul rule / table                  → `<Level>Mul{Rule,Table}.lean`
