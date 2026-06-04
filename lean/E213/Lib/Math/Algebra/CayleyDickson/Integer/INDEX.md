# `Lib/Math/Algebra/CayleyDickson/Integer/` — integer-coefficient CD codomains

Concrete integer-coefficient codomains used as
`ConjugationCodomain` typeclass witnesses.  Together they show that
the (CommBinary + NonVanishing + Conjugation) triple does NOT force
ℂ — many ZSqrt / ZOmega instances satisfy all three.

These are the **first non-trivial witnesses** for the
`Meta.SelfRecognising` axiom-game.  Each cluster has shape
(carrier · arithmetic · domain · instance · hom).

## Files (26)

### ZI = ℤ[i] (Gaussian integers)
  - `ZI.lean`           — type + arithmetic
  - `ZIArith.lean`      — `add / sub / mul / conj` lemmas
  - `ZIDomain.lean`     — integral-domain instance
  - `ZIAlgebra213.lean` — `Algebra213` instance
  - `ZIHom.lean`        — homomorphism witnesses
  - `ZIInstance.lean`   — `ConjugationCodomain` instance
  - `ShiftRule_ZI_L3.lean` — Level-3 shift-rule

### Z₂ = ℤ[√-2]
  - `Z2Instance.lean` — instance witness

### ZOmega = ℤ[ω] (cyclotomic / Eisenstein)
  - `ZOmega.lean`              — base type
  - `ZOmegaDomain.lean`        — domain
  - `ZOmegaInstance.lean`      — Conjugation instance
  - `ZOmegaDouble.lean`,
    `ZOmegaDoubleOrderDist.lean` — Cayley-Dickson double-stage
  - `ZOmegaQuad.lean`,
    `ZOmegaQuadOrderDist.lean`  — quadruple stage
  - `ZOmegaOct.lean`,
    `ZOmegaOctOrderDist.lean`   — octuple stage

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
