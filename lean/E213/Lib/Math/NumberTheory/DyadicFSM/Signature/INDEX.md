# `DyadicFSM/Signature/` — FSM signature + walk universality

Signature shapes for dyadic FSMs: classifier, prediction, bipartite
variant, walk-universal theorem, conjecture-statement file.

## Files (6)

  - `Signature.lean`           — base signature shape
  - `Classifier.lean`          — signature classifier
  - `SignaturePredict.lean`    — signature-prediction theorem
  - `SignatureBipartite.lean`  — bipartite signature variant
  - `WalkUniversal.lean`       — walk-universality theorem
  - `PeriodClosure.lean`       — universal signature period-closure lemmas

## Where to add new files

  - New signature shape         → `Signature<...>`
  - Predictor / classifier      → `<...>Classifier` / `<...>Predict`
  - Universality theorem        → `<...>Universal`
  - Period-closure lemma        → `PeriodClosure<...>`

## Companion sub-clusters (in `DyadicFSM/`)

  - `ArithFSM/`     — Tier 1 multi-state FSM
  - `Pell/`         — Pell-equation FSM
  - `Pisano/`       — Pisano predictor chain
  - `Product/`      — product FSM
  - `Forward/`      — forward propagation
  - `Tier/`         — tier hierarchy
