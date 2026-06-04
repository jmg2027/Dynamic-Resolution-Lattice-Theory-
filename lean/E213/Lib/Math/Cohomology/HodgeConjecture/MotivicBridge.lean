import E213.Lib.Math.Cohomology.HodgeConjecture.MotivicBridge.BeilinsonLichtenbaum
import E213.Lib.Math.Cohomology.HodgeConjecture.MotivicBridge.BlochBeilinson
import E213.Lib.Math.Cohomology.HodgeConjecture.MotivicBridge.ChernCharacter
import E213.Lib.Math.Cohomology.HodgeConjecture.MotivicBridge.HodgeTate
import E213.Lib.Math.Cohomology.HodgeConjecture.MotivicBridge.MumfordTate
import E213.Lib.Math.Cohomology.HodgeConjecture.MotivicBridge.Tate

/-! Spec-as-code entry point for
    `E213.Lib.Math.Cohomology.HodgeConjecture.MotivicBridge`.

  Motivic-cohomology bridges — classical-side counterparts of the
  213-native Hodge-conjecture programme, expressed as cross-
  references to the standard algebraic-geometry literature.

  Sister cluster of `Bridge/` (which holds physics / CS bridges
  like Ising, Potts, MLDecoder).  Where `Bridge/` connects the
  HC²¹³ programme outward to lattice-physics models, `MotivicBridge/`
  connects it inward to the standard motivic-cohomology programme.

  These files were hosted under `OS/HodgeConjecture/Bridges/`
  before Phase A3 of the M14 refactor moved them home.

  ## Files

    * `BeilinsonLichtenbaum`  — Beilinson–Lichtenbaum motivic
                                conjecture
    * `BlochBeilinson`        — Bloch–Beilinson filtration
    * `ChernCharacter`        — Chern character bridge
    * `HodgeTate`             — Hodge–Tate decomposition
    * `MumfordTate`           — Mumford–Tate group
    * `Tate`                  — Tate conjecture

  Note: `BeilinsonRegulator` lives in the sister `Bridge/` cluster
  (substantive ζ_X/ρ_X content there); the OS-side stub was
  removed in Phase A1.
-/
