import E213.Lib.Math.Cohomology.HodgeConjecture.Toolkit.Primitives
import E213.Lib.Math.Cohomology.HodgeConjecture.Toolkit.RoundTrip
import E213.Lib.Math.Cohomology.HodgeConjecture.Toolkit.RoundTripMid
import E213.Lib.Math.Cohomology.HodgeConjecture.Structure.Ring
import E213.Lib.Math.Cohomology.HodgeConjecture.Structure.Map
import E213.Lib.Math.Cohomology.HodgeConjecture.Structure.PoincareDuality
import E213.Lib.Math.Cohomology.HodgeConjecture.Refinement.CupAtomicGeneration
import E213.Lib.Math.Cohomology.HodgeConjecture.Pairing.HodgeRiemann

/-!
# Cohomology bridge API — cup-chain cohomology + surface intersection forms

`import E213.Lib.Math.Cohomology.HodgeConjecture.API` exposes the
operational + structural layers of the 213-native cup-chain
cohomology programme:

  · **Toolkit/**   — operational primitives (support, fromList,
                     round-trip, primitives)
  · **Structure/** — multiplicative + duality structure
                     (Ring, Map = ⋆ as ℤ/2-bijection, Poincaré duality)
  · **Refinement/**— cup-atomic generation at Δ⁴ (k=2 case-work)
  · **Pairing/**   — signed-ℤ Hodge–Riemann polarization

The genuine ⋆⋆ = id involution lives in
`E213.Lib.Math.Cohomology.Hodge.InvolutionCapstone`; the surface
intersection-form / signature results live in
`E213.Lib.Math.Cohomology.HodgeConjecture.Pairing` and
`E213.Lib.Math.Cohomology.Surfaces`.

See `INDEX.md` for navigation.
-/
