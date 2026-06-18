import E213.Lib.Physics.YangMills.Bridge
import E213.Lib.Physics.YangMills.ColoredGap
import E213.Lib.Physics.YangMills.Gap
import E213.Lib.Physics.YangMills.SU5Roots
import E213.Lib.Physics.YangMills.WZBosons
import E213.Lib.Physics.YangMills.WeinbergAngle

/-! Spec-as-code entry point for `E213.Lib.Physics.YangMills`.

  Yang–Mills gauge-theory cluster — SU(5) GUT structure plus the
  electroweak Weinberg-angle prediction.

  ## Files

    * `SU5Roots`        — SU(5) root system, atomic root counts
    * `WZBosons`        — W / Z gauge-boson masses
    * `WeinbergAngle`   — sin²θ_W from atomic ratios
    * `Gap`             — Yang–Mills mass-gap structural witness
    * `ColoredGap`      — colored-mode spectral positivity (the spectral face of
                          confinement): the SOS certificate `Δ₀²−massGap·Δ₀ ⪰ 0` and
                          the eigenvalue gap `λ ≥ massGap` for every colored mode
    * `Bridge`          — α₃-channel atomic facts (b_1 = 8 = NS²−1,
                          d²−1 = 24); cross-reference to Gap / PhotonKernel
-/
