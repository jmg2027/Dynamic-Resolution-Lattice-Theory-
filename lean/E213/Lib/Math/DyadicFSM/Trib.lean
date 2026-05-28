import E213.Lib.Math.DyadicFSM.Trib.CRTCapstone
import E213.Lib.Math.DyadicFSM.Trib.FSMmod
import E213.Lib.Math.DyadicFSM.Trib.Capstone

/-! Spec-as-code entry point for `E213.Lib.Math.DyadicFSM.Trib`.

  Tribonacci-FSM family.

  ## Files

    * `FSMmod3`,
      `FSMmod5`,
      `FSMmod7`     — Tribonacci mod-p FSMs at small primes
    * `Capstone`    — top-level Tribonacci capstone tying the
                      per-mod results
    * `CRTCapstone` — Chinese-remainder integration: 3-modulus
                      closure (`trib_crt_capstone` for `m ∈ {2,
                      3, 5}`) + 4-modulus closure
                      (`trib_crt_4_capstone` adding `m = 7`)
-/
