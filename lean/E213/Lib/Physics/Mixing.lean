import E213.Lib.Physics.Mixing.Bridge
import E213.Lib.Physics.Mixing.CKMHierarchy
import E213.Lib.Physics.Mixing.CPViolation
import E213.Lib.Physics.Mixing.JarlskogApex
import E213.Lib.Physics.Mixing.CabibboAngle
import E213.Lib.Physics.Mixing.NeutrinoMixing

/-! Spec-as-code entry point for `E213.Lib.Physics.Mixing`.

  Quark + lepton mixing-matrix cluster.

  ## Files

    * `CabibboAngle`    — sin θ_C / sin²θ_13 atomic prediction
    * `CKMHierarchy`    — quark-mixing CKM matrix structure
    * `NeutrinoMixing`  — PMNS matrix (lepton sector)
    * `CPViolation`     — CP-phase + Jarlskog invariant
    * `Bridge`          — cross-reference layer to Foundations
                          (atomic angle inputs)
-/
