# `DyadicFSM/Pisano/` — Pisano-period predictors

Predictor for the Pisano period (Fibonacci sequence mod N) at
selected moduli.  Each `Predictor<N>` provides a per-modulus
witness; `Predictor` is the generic base.

## Files (9)

### Generic
  - `Predictor.lean`     — generic Pisano predictor base

### Per-modulus predictors (8 chain — semantic-chain retained
                            per HANDOFF backlog decision)
  - `Predictor6.lean`    — N = 6
  - `Predictor7.lean`    — N = 7
  - `Predictor8.lean`    — N = 8
  - `Predictor11.lean`   — N = 11
  - `Predictor14.lean`   — N = 14
  - `Predictor17.lean`   — N = 17
  - `Predictor20.lean`   — N = 20
  - `Predictor22.lean`   — N = 22

## Note (CLAUDE.md rule 7 deviation)

Per-modulus predictor files are normally consolidation candidates
(CLAUDE.md rule 7: same-topic instance sets in one file).  Decision
recorded in HANDOFF.md: keep semantic chain (each predictor depends
on the prior one) — not a pure instance set.

## Where to add new files

  - New modulus N        → `Predictor<N>.lean`  (semantic chain
                            from prior step — see existing
                            `Predictor<N-1>` import)
  - Generic refinement   → `Predictor.lean`

## Companion clusters

  - `DyadicFSM/Fib/`     — Fibonacci sequence (consolidated to 1)
  - `DyadicFSM/Pell/`    — Pell sequence + dyadic FSM
