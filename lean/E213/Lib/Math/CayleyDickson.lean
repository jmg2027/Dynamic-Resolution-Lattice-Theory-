import E213.Lib.Math.CayleyDickson.Tower.CDDouble
import E213.Lib.Math.CayleyDickson.Tower.CDTower
import E213.Lib.Math.CayleyDickson.Levels.Cayley
import E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy
import E213.Lib.Math.CayleyDickson.Tower.F2CDTower
import E213.Lib.Math.CayleyDickson.Tower.MetaTowerLoopSpine
import E213.Lib.Math.CayleyDickson.Tower.SeedUnitGovernance
import E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian
import E213.Lib.Math.CayleyDickson.Tower.TypeOOctahedral
import E213.Lib.Math.CayleyDickson.Tower.MobiusPIcosian
import E213.Lib.Math.CayleyDickson.Tower.MckayADECensus
import E213.Lib.Math.CayleyDickson.Tower.CDTowerParametric
import E213.Lib.Math.CayleyDickson.Tower.McKayADClosure
import E213.Lib.Math.CayleyDickson.Tower.FullOctahedral
import E213.Lib.Math.CayleyDickson.Tower.FullIcosian
import E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzHeavy
import E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzLens
import E213.Lib.Math.CayleyDickson.Levels.Pathion
import E213.Lib.Math.CayleyDickson.Levels.PathionHeavy
import E213.Lib.Math.CayleyDickson.Misc.R5Vacuity
import E213.Lib.Math.CayleyDickson.Levels.Sedenion
import E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy
import E213.Lib.Math.CayleyDickson.Levels.Trigintaduonion
import E213.Lib.Math.CayleyDickson.Levels.TrigintaduoionionHeavy
import E213.Lib.Math.CayleyDickson.Integer.ZI
import E213.Lib.Math.CayleyDickson.Integer.ZIArith
import E213.Lib.Math.CayleyDickson.Integer.ZIDomain
import E213.Lib.Math.CayleyDickson.Integer.ZIHom
import E213.Lib.Math.CayleyDickson.Integer.ZOmega
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaDomain
import E213.Lib.Math.CayleyDickson.Integer.ZSqrt
import E213.Lib.Math.CayleyDickson.Integer.ZSqrt2
import E213.Lib.Math.CayleyDickson.Integer.ZSqrt2Domain
import E213.Lib.Math.CayleyDickson.Integer.ZSqrtDomain
import E213.Lib.Math.CayleyDickson.Integer.ConjugationInstances
import E213.Lib.Math.CayleyDickson.Integer.ZSqrtProduct

/-! Spec-as-code entry point for `E213.Lib.Math.CayleyDickson`.

  Cayley–Dickson layered construction over 213.  Each layer is a
  CD doubling of the previous, producing the classical algebra
  tower at integer coefficients (no Mathlib, no `ring`, no
  Classical).

  ## Codomain witnesses (counterexamples to "R1–R4 force ℂ")

    * `ZI`        — Gaussian integers `ℤ[i]`           (D = 1)
    * `ZSqrt2`    — `ℤ[√-2]` and the parametric        (D = 2)
    * `ZOmega`    — Eisenstein integers `ℤ[ω]`         (cross-term norm)
    * `ZSqrt D`   — parametric family for any D > 0    (any positive D)

    Each is a `ConjugationCodomain` instance witnessing that the
    three-tier codomain spec (`CommBinaryCodomain` + `NonVanishing`
    + `Conjugation`) does NOT pin the codomain to ℂ.

  ## CD tower (structural drop ladder)

    * `CDDouble`     — CD doubling of ZI → Lipschitz quaternions.
                       R2 (commutativity) drops here.
    * `Cayley`       — CD doubling of Lipschitz → integer octonions.
                       Associativity drops here.
    * `Sedenion`     — CD doubling of Cayley → integer sedenions.
                       R3 (no zero divisors) drops here.  Moreno's
                       (e_3 + e_10)·(e_6 - e_15) = 0 witness.
    * `Trigintaduonion` — Sedenion × Sedenion (32-dim).
    * `Pathion`      — Trigintaduonion × Trigintaduonion (64-dim).

  ## Domain proofs

    * `ZIDomain`,
      `ZOmegaDomain`,
      `ZSqrtDomain`,
      `ZSqrt2Domain`  — `normSq u · v = normSq u · normSq v` etc.
    * `ZIArith`,
      `ZIHom`         — extra ZI lemmas + ring-hom witness for `conj`.

  ## Tactic-derived instances

    * `ConjugationInstances` — `derive_conjugation_codomain` /
      `quad_extension D` macro outputs for ZI / Z2 / ZOmega /
      ZSqrt {3, 5, 7}. from four
      singleton files.

  ## Status

  All ~49 files build clean.

  Recent compression:

    - 4 singleton `*Instance.lean` files → `ConjugationInstances.lean`
    - 3 `ZOmega{Double,Quad,Oct}` + `OrderDist` pairs merged
    - 3 ZSqrtMinus2-discovery files → `ZSqrtMinus2Findings.lean`

  Net: -8 files.
-/
