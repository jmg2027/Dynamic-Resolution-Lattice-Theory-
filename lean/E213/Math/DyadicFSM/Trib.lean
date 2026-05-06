import E213.Math.DyadicFSM.Trib.CRT4Capstone
import E213.Math.DyadicFSM.Trib.CRTCapstone
import E213.Math.DyadicFSM.Trib.Capstone
import E213.Math.DyadicFSM.Trib.FSMmod3
import E213.Math.DyadicFSM.Trib.FSMmod5
import E213.Math.DyadicFSM.Trib.FSMmod7

/-! Spec-as-code entry point for `E213.Math.DyadicFSM.Trib`.

  Tribonacci-FSM family.

  ## Files

    * `FSMmod3`,
      `FSMmod5`,
      `FSMmod7`     — Tribonacci mod-p FSMs at small primes
    * `Capstone`    — top-level Tribonacci capstone tying the
                      per-mod results
    * `CRTCapstone` — Chinese-remainder integration over multiple
                      primes
    * `CRT4Capstone` — 4-prime CRT integration
-/
