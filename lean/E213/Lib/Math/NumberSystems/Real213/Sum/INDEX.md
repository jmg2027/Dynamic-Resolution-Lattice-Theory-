# `Real213/Sum/` — cut-level addition algebra

Addition on Real213 cuts: `cutSum`, plus signed sum, identity laws,
commutativity, and general/pointwise variants.

## Files (11)

### Core addition
  - `CutSum.lean`            — base `cutSum` definition
  - `CutSumZero.lean`        — `cutSum x 0 = x`
  - `CutSumOne.lean`         — `cutSum x 1` lemmas
  - `CutSumComm.lean`        — commutativity
  - `CutSumDetermined.lean`  — determined-output specialisation
  - `CutSumTest.lean`        — concrete numeric tests

### Generality / pointwise
  - `CutSumGeneral.lean`     — general form
  - `CutSumPointwise.lean`   — pointwise variant
  - `CutSumEq.lean`          — sum-equality lemmas

### Signed sum
  - `Signed.lean`            — signed-cut carrier
  - `SignedSum.lean`         — signed-sum operation

## Where to add new files

  - New sum lemma      → `CutSum<name>.lean`
  - Signed extension   → `Signed*` / `SignedSum*`
  - Numeric test       → `CutSumTest`
