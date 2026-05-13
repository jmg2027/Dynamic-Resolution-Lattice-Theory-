# `Real213/Mul/` — cut-level multiplication algebra

Multiplication on Real213 cuts: `cutMul`, `cutInv`, `cutPow`, plus
auxiliary scaling, doubling, distance, polynomial, and binary
operations.  Companion to `Sum/` (addition).

## Files (15)

### Core multiplication
  - `CutMul.lean`               — base `cutMul` definition
  - `CutMulOne.lean`            — `cutMul x 1 = x`
  - `CutMulComm.lean`           — commutativity
  - `CutMulConstConst.lean`     — const · const
  - `CutMulDetermined.lean`     — determined-output specialisation
  - `CutMulTest.lean`           — concrete numeric tests

### Inverse + power
  - `CutInv.lean`               — `cutInv` (reciprocal)
  - `CutPow.lean`               — `cutPow n`
  - `CutPowConst.lean`          — power on constants

### Polynomial
  - `CutPoly.lean`              — polynomial evaluation
  - `CutAlgebraic.lean`         — algebraic combinator

### Auxiliary scaling / distance
  - `ConstCutScale.lean`        — constant scaling
  - `CutBinary.lean`            — binary representation
  - `CutDouble.lean`            — doubling
  - `CutDistance.lean`          — distance between cuts

## Top-level

  - `Real213.lean` umbrella (no `Mul.lean` aggregator — files are
    directly imported by sibling sub-clusters)

## Where to add new files

  - New mul lemma         → `CutMul<name>.lean`
  - Inverse / power       → `CutInv<...>` / `CutPow<...>`
  - Polynomial extension  → `CutPoly` / `CutAlgebraic`
  - Numeric test          → `Cut<op>Test`
