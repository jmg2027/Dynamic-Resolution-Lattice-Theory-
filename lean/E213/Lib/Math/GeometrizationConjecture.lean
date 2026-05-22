import E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz

/-! Spec-as-code entry point for `E213.Lib.Math.GeometrizationConjecture`.

  213-Lens reading of the Thurston/Perelman Geometrization
  conjecture and the dimension-4 exotic-smoothness anomaly.

  ## Top-level

    * `ChartAxisAnsatz.lean` — G121 §4.1 ansatz
      `d_M = chartBase - selfPointingAxes` in parametric form.
      Open conjecture; structural derivation deferred to R1
      (close M2).

  ## Cross-references

    * `research-notes/G121_dim4_self_pointing_axis.md` — full
      narrative + open knots M1-M4 + validation routes R1-R4
    * `lean/E213/Lib/Math/BipartiteDecomp/G44Capstone.lean` —
      substrate_sum (chartBase 3 2 = 5 numerical agreement)
-/
