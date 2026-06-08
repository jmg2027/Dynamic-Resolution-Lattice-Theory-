import E213.Lib.Physics.Mixing.Bridge
import E213.Lib.Physics.Mixing.CKMHierarchy
import E213.Lib.Physics.Mixing.CPViolation
import E213.Lib.Physics.Mixing.CPPhaseCount
import E213.Lib.Physics.Mixing.JarlskogApex
import E213.Lib.Physics.Mixing.ApexCPMechanism
import E213.Lib.Physics.Mixing.ApexPiInternal
import E213.Lib.Physics.Mixing.ApexRightTriangle
import E213.Lib.Physics.Mixing.CPPhaseC4Forcing
import E213.Lib.Physics.Mixing.CPHodgeStructure
import E213.Lib.Physics.Mixing.CPGenerationWiring
import E213.Lib.Physics.Mixing.CPMaximalPhase
import E213.Lib.Physics.Mixing.BigradedYukawa
import E213.Lib.Physics.Mixing.CohomologicalYukawa
import E213.Lib.Physics.Mixing.CohomologicalYukawaEval
import E213.Lib.Physics.Mixing.ApexFitConsistency
import E213.Lib.Physics.Mixing.A5QuarkApex
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
