# `DyadicFSM/Pisano/` — Pisano-period predictors

Predictor for the Pisano period (Fibonacci sequence mod N) at
selected moduli.

## Files (2)

  - `Predictor.lean`      — `pisano_predict : Nat → Nat`
                             (Legendre-driven), the
                             `pisano_period_lift` utility, and
                             the 4-prime correctness theorem.
  - `PredictorChain.lean` — per-prime verifications for 23 primes
                             (3, 5, 7, 11, 13, 17, 19, 23, 29,
                             31, 37, 41, 43, 47, 53, 59, 61,
                             67, 71, 73, 79, 89, 101).  Each
                             prime gets a `pisano_at_<p>` lemma;
                             two headline conjunctions
                             `pisano_predict_realises_pell_7`
                             (downstream-consumed) and
                             `pisano_predict_realises_pell_23`
                             (full headline).

## Where to add new evidence

  - New prime `p` with verified period `X`:
      add `pisano_at_p` lemma in `PredictorChain.lean`
      (3-line proof via `pisano_period_lift` + the
      `pellFSMmod<p>_bits_period_<X>` lemma)
  - Refinement of `pisano_predict` itself:
      edit `Predictor.lean`

## Companion clusters

  - `DyadicFSM/Fib/`     — Fibonacci sequence
  - `DyadicFSM/Pell/`    — Pell sequence + dyadic FSM
