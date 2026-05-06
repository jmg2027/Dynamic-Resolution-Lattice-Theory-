import E213.Math.DyadicFSM.Pisano.Predictor
import E213.Math.DyadicFSM.Pisano.Predictor11
import E213.Math.DyadicFSM.Pisano.Predictor14
import E213.Math.DyadicFSM.Pisano.Predictor17
import E213.Math.DyadicFSM.Pisano.Predictor20
import E213.Math.DyadicFSM.Pisano.Predictor22
import E213.Math.DyadicFSM.Pisano.Predictor6
import E213.Math.DyadicFSM.Pisano.Predictor7
import E213.Math.DyadicFSM.Pisano.Predictor8

/-! Spec-as-code entry point for `E213.Math.DyadicFSM.Pisano`.

  Pisano-period predictor library — given a base b, computes the
  Pisano period π(b) via the dyadic-FSM encoding.

  ## Files

    * `Predictor`    — generic predictor scaffold
    * `Predictor6`,
      `Predictor7`,
      `Predictor8`,
      `Predictor11`,
      `Predictor14`,
      `Predictor17`,
      `Predictor20`,
      `Predictor22`  — per-base specialised predictors
                       (small bases verified by `decide`).
-/
