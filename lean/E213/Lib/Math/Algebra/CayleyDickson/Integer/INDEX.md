# `Lib/Math/Algebra/CayleyDickson/Integer/` — integer-coefficient CD codomains

Concrete integer-coefficient codomains used as
`ConjugationCodomain` typeclass witnesses.  Together they show that
the (CommBinary + NonVanishing + Conjugation) triple does NOT force
ℂ — many ZSqrt / ZOmega instances satisfy all three.

These are the **first non-trivial witnesses** for the
`Meta.SelfRecognising` axiom-game.  Each cluster has shape
(carrier · arithmetic · domain · instance · hom).

## Files (131)

### ZI = ℤ[i] (Gaussian integers)
  - `ZI.lean`           — type + arithmetic
  - `ZIArith.lean`      — `add / sub / mul / conj` lemmas
  - `ZIDomain.lean`     — integral-domain instance
  - `ZIAlgebra213.lean` — `Algebra213` instance
  - `ZIHom.lean`        — homomorphism witnesses
  - `ZIInstance.lean`   — `ConjugationCodomain` instance
  - `GaussianOrthogonality.lean` — additive-character orthogonality `Σ iᵏ = 0` at order 4
    (`i_orthogonality`: `1+i+i²+i³=0`) via the geometric telescope, plus the order-agnostic
    generic conditional over any `CommRing213` (`geomSum_telescope`,
    `orthogonality_of_pow_one`).  The order-4 leg of fourier.md's character-orthogonality
    target — sibling of `RootOfUnityOrthogonality` (orders 3, 6 in ℤ[ω])
  - `ShiftRule_ZI_L3.lean` — Level-3 shift-rule

### Z₂ = ℤ[√-2]
  - `Z2Instance.lean` — instance witness

### ZOmega = ℤ[ω] (cyclotomic / Eisenstein)
  - `ZOmega.lean`              — base type
  - `ZOmegaDomain.lean`        — domain
  - `RootOfUnityOrthogonality.lean` — additive-character orthogonality `Σ ζᵏ = 0` for the
    cyclotomic roots `ω` (order 3) and `ζ₆` (order 6) in `ℤ[ω]`, via the geometric telescope
    `(ζ−1)·Σ_{k<n} ζᵏ = ζⁿ−1`.  The order-`>2` leg of fourier.md's character-orthogonality target
  - `ZOmegaInstance.lean`      — Conjugation instance
  - `ZOmegaDouble.lean`,
    `ZOmegaDoubleOrderDist.lean` — Cayley-Dickson double-stage
  - `ZOmegaQuad.lean`,
    `ZOmegaQuadOrderDist.lean`  — quadruple stage
  - `ZOmegaOct.lean`,
    `ZOmegaOctOrderDist.lean`   — octuple stage
  - `EisensteinSignature.lean` / `ParabolicSignature.lean` — the disc `−3` / `0` / `+5`
    signature trichotomy (positive-definite / degenerate / indefinite → curve / cusp / line)
  - `EisensteinCrossDet.lean` / `EisensteinCompletion.lean` / `GaussianCrossDet.lean` —
    the ℤ[ω]- and ℤ[i]-convergent cross-determinant, its 6- and 4-unit floor rotation
  - `EisensteinSplitting.lean` — the local splitting of the Eisenstein period's L-function:
    Brahmagupta multiplicativity (`eisForm_composition`), ramification at 3, split/inert
    witnesses, the χ₋₃ Euler-factor trichotomy
  - `EisensteinClassNumber.lean` — class number one for disc `−3` (`reduced_disc_neg3_unique`):
    the principal form `x²+xy+y²` is the only reduced form, the form-class shadow of `ℤ[ω]`
    being a PID (why the period's L-function carries a single form)
  - `EisensteinEuclidean.lean` — the covering-radius bound (`covering_bound`): the Eisenstein
    lattice's covering radius² is `≤ 3/4 < 1`, the geometric reason `ℤ[ω]` is norm-Euclidean
    (the split-prime descent's load-bearing inequality)

  **Cubic / Eisenstein reciprocity — the cubic character `(·/d)₃ = α^m`** (`d` a norm-`p` prime,
  `p ≡ 1 mod 3`, `m = (p−1)/3`).  Complete cubic-character theory + Jacobi-sum substrate.  The
  reciprocity *law* is **complete** (both cases, ∅-axiom): the **inert law** `(π/q)₃ = χ(q)` for
  rational `q ≡ 2 mod 3` (`EisensteinCubicReciprocity.cubic_reciprocity_law`) and the **split law**
  `(π/π')₃ = (π'/π)₃` for two complex primes (`EisensteinCubicReciprocitySplit.split_cubic_reciprocity`).
  Narrative: `theory/math/numbertheory/cubic_reciprocity.md`.
  - `CubeRootsOfUnity.lean` — value group `μ₃ = {1,ω,ω²}` (`x³=1 ⟺ x∈μ₃`)
  - `EisensteinCongruence.lean` / `EisensteinResidue.lean` / `EisensteinResiduePrime.lean` —
    `α≡β (mod π)`, the reduction `ℤ[ω]/(d)=ℤ`-image, the residue prime for `p≡1 mod 3`
  - `EisensteinPrime.lean` — a norm-`p` element is prime (`norm_prime_euclid`); `ℤ[ω]/(d)` integral domain
  - `EisensteinCubicChar.lean` — cubes-to-one, multiplicativity, cube-detection, rational weld
  - `EisensteinCubicCharValue.lean` — `cubic_factor` + the value is exactly `1, ω,` or `ω²`
  - `EisensteinCubicCharWelldef.lean` — the three roots distinct mod `d`: `(·/d)₃` a well-defined function
  - `EisensteinCubicWeld.lean` / `EisensteinCubicEuler.lean` — `(α/d)₃=1 ⟺ r` cubic residue; `⟹ α` a cube
  - `EisensteinPrimary.lean` — the unique primary associate `≡ 2 (mod 3)`
  - `EisensteinCubicCharOmega.lean` / `EisensteinCubicCharConj.lean` — supplementary laws `(ω/d)₃`, `(ᾱ/d)₃`
  - `EisensteinFiniteSum.lean` / `EisensteinCharOrthogonality.lean` / `EisensteinCubicCharFunction.lean` —
    Jacobi-sum substrate: `Σ_{k<n} f k`, `Σ_{j<3k} ωʲ = 0`, the character homomorphism `χ̂(i)=ωⁱ`

  **The reciprocity law (Phase B, ∅-axiom PURE)** — Gauss-sum Frobenius → residue-symbol assembly.
  - `EisensteinConvGaussFrobenius.lean` / `EisensteinConvGaussReindex.lean` — the Gauss-sum Frobenius
    `g(χ)^{⋆q}(k) ≡ χ(q)·χ̄(k) (mod q)` (inert) and `≡ χ̄(pr)·χ(k) (mod pr)` (split), via the `t↦tq%p` reindex
  - `EisensteinIntFermat.lean` / `EisensteinFrobeniusConj.lean` — ℤ-Fermat; `conj z ≡ z^q (mod q)` =
    `q`-power Frobenius on `ℤ[ω]/(q) ≅ 𝔽_{q²}` (inert), and `z^{q²} ≡ z`
  - `EisensteinMu3Lift.lean` — `X ≡ Y (mod q), X,Y ∈ μ₃ ⟹ X = Y` (distinct cube roots stay distinct)
  - `EisensteinInertForm.lean` / `EisensteinInertPrime.lean` / `EisensteinInertCube.lean` — a rational
    prime `q ≡ 2 mod 3` is prime in `ℤ[ω]` (`𝔽_{q²}` field); cube roots of unity there are `{1,ω,ω²}`
  - `EisensteinCubicReciprocity.lean` — ★ **the inert law** `(π/q)₃ = χ(q)`, the residue symbol as a
    unique μ₃ value (`cubic_reciprocity_law`, `cubic_residue_symbol_well_defined`)
  - `EisensteinSplitFermat.lean` / `EisensteinCharSumRange.lean` / `EisensteinYfunGauss.lean` — split-prime
    `𝔽_{p'}` Fermat `z^{pr} ≡ z (mod π')`; `Σχ = 0`; `Yfun ⋆ g = p·g`
  - `EisensteinSplitCube.lean` / `EisensteinSplitReciprocity.lean` — `g^{⋆pr} = J^{s+1}·p^{s+1}·g`;
    `J^{2(s+1)}·J̄^{s+1} ≡ χ̄(pr)` (all-Eisenstein) and its descent to `mod π'`
  - `EisensteinSplitResidueSymbol.lean` — ★ `(π/π')₃ = J^{s+1}` μ₃-valued; **`J̄^{s+1} ≡ χ̄(pr)·J^{s+1}
    (mod π')`** (the mod-`π'` half)
  - `EisensteinCharNormSplit.lean` — ★ **`χ_ω(N(π')) ≡ (π'/π)₃·(π̄'/π)₃ (mod d)`** (the mod-`d` half)

### ZSqrt = ℤ[√D] (parametric family)
  - `ZSqrt.lean`              — generic carrier
  - `ZSqrt2.lean`             — D = 2 special case
  - `ZSqrtDomain.lean`        — generic domain
  - `ZSqrt2Domain.lean`       — D = 2 domain
  - `ZSqrtInstance.lean`      — Conjugation instance
  - `ZSqrtProduct.lean`       — product / tower properties
  - `ZSqrtMinus2L6Search.lean`,
    `ZSqrtMinus2L6Witnesses.lean`,
    `ZSqrtMinus2Tower.lean`   — ZSqrt(-2) Level-6 search +
                                witnesses + tower

### Hurwitz integers (ℤ[ω] quaternionic extension)
  - `Hurwitz213.lean`         — Hurwitz quaternion integers
  - `HurwitzTower.lean` — Type D Hurwitz CD-doubling tower — L1 and L2
  - `UnitsToModular.lean` — modular generators `S, U` as regular-representation images of the units
  - `ZOmegaQuadAlgebra213.lean` — `ZOmegaQuad` as a `MoufangIntegerNormed213` instance
  - `ZSqrtMinus2Algebra213.lean` — `L3T` (= CDDouble ZSqrt[-2]) Algebra213 bridge
  - `ZSqrtMinus2TowerDeep.lean` — ZSqrt[-2] tower — deeper layers L7, L8, L9

## Sibling buckets (in `CayleyDickson/`)

  - `Tower/`     — generic Cayley-Dickson tower machinery
  - `Levels/`    — level-2 (Quaternion), level-4 (Cayley), level-5
                   (Sedenion) instances
  - `Lipschitz/` — Lipschitz integers + heavy work
  - `Misc/`      — small auxiliary lemmas (R5Vacuity etc.)

## Where to add new integer-coefficient codomains

  - Cyclotomic-like ZOmega variant → ZOmega family
  - Quadratic ring ℤ[√D] → ZSqrt family
  - Gaussian-like → ZI family

Each new bucket follows the {carrier, arithmetic, domain, instance,
hom} 5-tuple pattern.
