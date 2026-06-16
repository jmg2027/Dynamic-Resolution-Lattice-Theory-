import E213.Lib.Math.Cohomology.Bipartite.Parametric.Betti.KernelConstancyUniversal
import E213.Lib.Math.Cohomology.Bipartite.Parametric.EulerAndCapstone
import E213.Lib.Math.Cohomology.Bipartite.Filled3CellCohomology
import E213.Lib.Math.Cohomology.Bipartite.Filled3CellExtension
import E213.Lib.Math.Cohomology.Bipartite.Filled4CellExtension
import E213.Lib.Math.Cohomology.Bipartite.SteenrodSquaresAtOmega
import E213.Lib.Math.Cohomology.Bipartite.MultParityOrthogonal

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Bipartite`.

  K_{NS,NT}^{(c)} bipartite-graph cohomology.

  ## Files

    * `Parametric/`            — the structural, graph-carrier-free family.
      `CochSpaces` defines `CochV`/`CochE`/`δ⁰` parametrically in
      `(NS, NT, c)`; `Betti/KernelConstancyUniversal.universal_kernel_close`
      proves `ker δ⁰ = constants` (`b₀ = 1`, `dim ker = 1`) for every
      connected `K_{NS,NT}^{(c)}`; `EulerAndCapstone` gives the Euler
      characteristic and `b₁ = c·NS·NT − (NS + NT) + 1` (= 8 at (3,2,2)).
    * `Filled3Cell{,Cohomology,Extension}` / `Filled4CellExtension` —
      F₂ face algebra on the 3 simple 4-cycles: face dependence
      (`rank δ¹ = 2`), the `b₂ = 1` ω class, its Sym(3)-invariance, and
      the cup-1 = δ² / Steenrod-square ladder at ω.
    * `FaceCupHigher` / `FaceCup1At3Cell` / `SelfPairingTrace`
      / `SteenrodSquaresAtOmega` — Steenrod cup-i machinery at ω.
    * `MultParityOrthogonal` — the multiplicity parity ℤ/2 is orthogonal
      to the cup-orientation ℤ/2 (refutes the "chirality forces c=2"
      frontier P3′), stated over the parametric `srcOf`/`tgtOf` encoding.
-/
