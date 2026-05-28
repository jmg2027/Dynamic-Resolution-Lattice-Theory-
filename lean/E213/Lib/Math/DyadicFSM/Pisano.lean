import E213.Lib.Math.DyadicFSM.Pisano.Predictor
import E213.Lib.Math.DyadicFSM.Pisano.PredictorChain

/-! Spec-as-code entry point for `E213.Lib.Math.DyadicFSM.Pisano`.

  Pisano-period predictor library — given a base b, computes the
  Pisano period π(b) via the dyadic-FSM encoding.

  ## Files

    * `Predictor`      — predictor scaffold: `pisano_predict :
                         Nat → Nat` (Legendre-driven), the
                         `pisano_period_lift` utility, and the
                         4-prime correctness theorem.
    * `PredictorChain` — per-prime verifications for 23 primes
                         (3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
                         37, 41, 43, 47, 53, 59, 61, 67, 71,
                         73, 79, 89, 101).  Headline conjunctions
                         `pisano_predict_realises_pell_7` and
                         `pisano_predict_realises_pell_23`.
-/
