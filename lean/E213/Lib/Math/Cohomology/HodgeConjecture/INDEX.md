# `Math/Cohomology/HodgeConjecture/` — cup-chain cohomology + surface forms

Cup-chain cohomology toolkit and **surface intersection-form /
signature** results, all strict ∅-axiom.  (Directory name retained
pending a later rename pass.)

The genuine ⋆⋆ = id Hodge involution lives in
`Cohomology/Hodge/InvolutionCapstone.lean` (outside this directory).

**Single import**: `E213.Lib.Math.Cohomology.HodgeConjecture.API`

---

## Layers

### `Toolkit/`  — compute layer

Operational primitives on `Cochain n k = Fin (binom n k) → Bool`.

  · `Primitives.lean`        support, fromList, isCocycle, weight
  · `RoundTrip.lean`         fromList ∘ support = id (4 strata)
  · `RoundTripMid.lean`      Round-trip on (5,2)/(5,3)

### `Structure/`  — algebraic structure layer

  · `Ring.lean`              ⋆ × cup compatibility
  · `Map.lean`               ⋆ as ℤ/2-bijection + XOR-linearity
  · `PoincareDuality.lean`   H^k ↔ H^{n−k}

### `Refinement/`  — cup-atomic generation

  · `CupAtomicGeneration.lean`  vertex⌣vertex realises the 10 edge
                                 indicators of C²(Δ⁴) (k=2 case-work)

### `Pairing/`  — surface intersection forms

Genuine signature / Hodge–Riemann results on real CW surfaces.

  · `HodgeIndexT2` / `HodgeIndexT2Squared` / `HodgeIndexP2` /
    `HodgeIndexP1Squared`   — signatures on T², T²×T², ℙ², ℙ¹×ℙ¹
  · `HodgeRiemann*`         — signed-ℤ Hodge–Riemann polarization
                              (Q, J), positive-definite `h = Q·J = I`
  · `T2nPattern` / `T2nInductive` / `GenusGSurface` /
    `TensorSignature`       — parametric signature patterns
  · `SurfaceComparisonTheorem`, `*GradeStructure`,
    `*ProductSurface*`      — comparison + product signatures

### `Bridge/`  — statistical-mechanics + CS bridges

K_5 / K_{3,2}^{(c=2)} stat-mech + algorithmic interpretations.

  · `Ising.lean` / `Potts.lean`       energy spectra + routing
  · `SpinGlass.lean` / `SpinGlassGroundState.lean`
  · `MLDecoder.lean`, `DiscreteGeometry.lean`,
    `ClassAExactWitnesses.lean`

---

## Companion narrative

`theory/math/cohomology/hodge.md` (⋆⋆ involution) +
`theory/math/cohomology/surfaces.md` (intersection forms).
