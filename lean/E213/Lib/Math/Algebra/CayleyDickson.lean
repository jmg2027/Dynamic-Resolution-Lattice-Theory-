import E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble
import E213.Lib.Math.Algebra.CayleyDickson.Tower.CDTower
import E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley
import E213.Lib.Math.Algebra.CayleyDickson.Levels.CayleyHeavy
import E213.Lib.Math.Algebra.CayleyDickson.Tower.F2CDTower
import E213.Lib.Math.Algebra.CayleyDickson.Tower.MetaTowerLoopSpine
import E213.Lib.Math.Algebra.CayleyDickson.Tower.SeedUnitGovernance
import E213.Lib.Math.Algebra.CayleyDickson.Tower.TypeEIcosian
import E213.Lib.Math.Algebra.CayleyDickson.Tower.TypeOOctahedral
import E213.Lib.Math.Algebra.CayleyDickson.Tower.MobiusPIcosian
import E213.Lib.Math.Algebra.CayleyDickson.Tower.MckayADECensus
import E213.Lib.Math.Algebra.CayleyDickson.Tower.CDTowerParametric
import E213.Lib.Math.Algebra.CayleyDickson.Tower.McKayADClosure
import E213.Lib.Math.Algebra.CayleyDickson.Tower.FullOctahedral
import E213.Lib.Math.Algebra.CayleyDickson.Tower.FullIcosian
import E213.Lib.Math.Algebra.CayleyDickson.Tower.IcosianClassStructure
import E213.Lib.Math.Algebra.CayleyDickson.Tower.BinaryPolyhedralTower
import E213.Lib.Math.Algebra.CayleyDickson.Tower.ExceptionalAtomicIndex
import E213.Lib.Math.Algebra.CayleyDickson.Tower.DiscForcingObstruction
import E213.Lib.Math.Algebra.CayleyDickson.Tower.ExceptionalTraceSeed
import E213.Lib.Math.Algebra.CayleyDickson.Tower.CyclotomicTraceDegree
import E213.Lib.Math.Algebra.CayleyDickson.Tower.PlatonicSchlafliFilter
import E213.Lib.Math.Algebra.CayleyDickson.Tower.QuadraticFieldDiscriminant
import E213.Lib.Math.Algebra.CayleyDickson.Tower.UnitResidueRootTwo
import E213.Lib.Math.Algebra.CayleyDickson.Tower.TraceDoublingMap
import E213.Lib.Math.Algebra.CayleyDickson.Tower.TwoEnginesDichotomy
import E213.Lib.Math.Algebra.CayleyDickson.Tower.AxisSeedTrichotomy
import E213.Lib.Math.Algebra.CayleyDickson.Tower.AxisComposition
import E213.Lib.Math.Algebra.CayleyDickson.Tower.PMatrixArithmeticBridge
import E213.Lib.Math.Algebra.CayleyDickson.Tower.NaturalTowerForm
import E213.Lib.Math.Algebra.CayleyDickson.Tower.ThreeAxisRecurrence
import E213.Lib.Math.Algebra.CayleyDickson.Tower.SpiralAxisCrystallographic
import E213.Lib.Math.Algebra.CayleyDickson.Lipschitz.LipschitzHeavy
import E213.Lib.Math.Algebra.CayleyDickson.Lipschitz.LipschitzLens
import E213.Lib.Math.Algebra.CayleyDickson.Levels.Pathion
import E213.Lib.Math.Algebra.CayleyDickson.Levels.PathionHeavy
import E213.Lib.Math.Algebra.CayleyDickson.Misc.R5Vacuity
import E213.Lib.Math.Algebra.CayleyDickson.Levels.Sedenion
import E213.Lib.Math.Algebra.CayleyDickson.Levels.SedenionHeavy
import E213.Lib.Math.Algebra.CayleyDickson.Levels.Trigintaduonion
import E213.Lib.Math.Algebra.CayleyDickson.Levels.TrigintaduoionionHeavy
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIArith
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIDomain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIUnits
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIHom
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSignature
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCrossDet
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCompletion
import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianCrossDet
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ImaginaryQuadraticUnitTrichotomy
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ParabolicSignature
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitting
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinClassNumber
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinEuclidean
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd
import E213.Lib.Math.Algebra.CayleyDickson.Integer.CubeRootsOfUnity
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResiduePrime
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharValue
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicWeld
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicEuler
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharOmega
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharConj
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharOrthogonality
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharWelldef
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFunction
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidueFieldCubeRoots
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumZero
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrimary
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConverse
import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianOrthogonality
import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDivStep
import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDvd
import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianGcd
import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianSplit
import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianTwoSquare
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegDivStep
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegSplit
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegTwoSquare
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegSharp
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt2
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt2Domain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtDomain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ConjugationInstances
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtProduct
import E213.Lib.Math.Algebra.CayleyDickson.Integer.HurwitzTower
import E213.Lib.Math.Algebra.CayleyDickson.Integer.UnitsToModular
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaQuadAlgebra213
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtMinus2Algebra213
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtMinus2TowerDeep
import E213.Lib.Math.Algebra.CayleyDickson.Levels.SedenionZeroDivisor
import E213.Lib.Math.Algebra.CayleyDickson.Lipschitz.LipschitzMoufang
import E213.Lib.Math.Algebra.CayleyDickson.Tower.AlgebraTowerCapstone
import E213.Lib.Math.Algebra.CayleyDickson.Tower.FirstSlashGrounding

/-! Spec-as-code entry point for `E213.Lib.Math.Algebra.CayleyDickson`.

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
