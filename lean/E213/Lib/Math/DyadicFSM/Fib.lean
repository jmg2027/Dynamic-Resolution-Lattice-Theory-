import E213.Lib.Math.DyadicFSM.Fib.FSMmod
import E213.Lib.Math.DyadicFSM.Fib.PellRelation
import E213.Lib.Math.DyadicFSM.Fib.Pisano8
import E213.Lib.Math.DyadicFSM.Fib.PisanoCapstone

/-! Spec-as-code entry point for `E213.Lib.Math.DyadicFSM.Fib`.

  Fibonacci-FSM family + Pell + Pisano.

  ## Per-mod FSMs

    * `FSMmod3`, `FSMmod5`, `FSMmod7`,
      `FSMmod11`, `FSMmod13`, `FSMmod17`,
      `FSMmod19`, `FSMmod23` — Fib mod-p FSMs at the small primes.

  ## Pisano

    * `Pisano8`         — Pisano-8 (period of Fib mod 8)
    * `PisanoCapstone`  — capstone tying the per-prime Pisano
                          periods together
    * `PellRelation`    — Fibonacci-Pell algebraic relation
                          x_n² - 5 y_n² = ±4
-/
