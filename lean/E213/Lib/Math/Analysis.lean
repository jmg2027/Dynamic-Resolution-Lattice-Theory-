import E213.Lib.Math.NumberSystems.Real213
import E213.Lib.Math.Analysis.ClassicCalc
import E213.Lib.Math.Analysis.Differentiation
import E213.Lib.Math.Analysis.DyadicSearch
import E213.Lib.Math.Analysis.ExtremeValue
import E213.Lib.Math.Analysis.UniformLimitContinuous
import E213.Lib.Math.Analysis.BanachFixedPoint
import E213.Lib.Math.Analysis.RiemannContinuous
import E213.Lib.Math.Analysis.ModulusConvergence
import E213.Lib.Math.Analysis.CesaroMean
import E213.Lib.Math.Analysis.LimitArithmetic
import E213.Lib.Math.Analysis.AlternatingSeries
import E213.Lib.Math.Analysis.ComparisonTest
import E213.Lib.Math.Analysis.CauchySchwarz
import E213.Lib.Math.Analysis.ChebyshevSumInequality
import E213.Lib.Math.Analysis.SqueezeProduct
import E213.Lib.Math.Analysis.FluxMVT
import E213.Lib.Math.Analysis.Integration
import E213.Lib.Math.Analysis.ODE
import E213.Lib.Math.Analysis.Series
import E213.Lib.Math.Analysis.BracketCauchyModulus
import E213.Lib.Math.Analysis.CauchyProj
import E213.Lib.Math.Analysis.ChainCauchy
import E213.Lib.Math.Analysis.CauchyComplete
import E213.Lib.Math.Analysis.CauchyCompleteValid
import E213.Lib.Math.Analysis.StagedLimitCauchy
import E213.Lib.Math.Analysis.CompletionTower
import E213.Lib.Math.Analysis.ModulusMonoid
import E213.Lib.Math.Analysis.ResolutionQuantitative
import E213.Lib.Math.Analysis.ModulusForm
import E213.Lib.Math.Analysis.PhysicsBridgeNT2
import E213.Lib.Math.Analysis.ResolutionShift
import E213.Lib.Math.Analysis.Optimization.GradientFlow
import E213.Lib.Math.Analysis.Optimization.CompletenessLoop
import E213.Lib.Math.Analysis.Optimization.RealCauchyWitness

/-! Spec-as-code entry point for `E213.Lib.Math.Analysis`.

  213-native analysis — calculus on top of `Math/Real213`.

  Importing this module pulls in the Real213 base type AND all of
  Analysis on top.

  ## Chapters (sub-directory umbrellas)

    * `Analysis/ClassicCalc`     — applied calculus structure (3 files)
    * `Analysis/Differentiation` — differential calculus, polynomial chain (14)
    * `Analysis/DyadicSearch`    — dyadic-search IVT (9 files,
                                   includes trajectory-as-witness
                                   `MinimalRootLens` + Layer 3c
                                   morphism-collapse closure)
    * `Analysis/FluxMVT`         — flux-form Mean Value Theorem (22)
    * `Analysis/Integration`     — integration on cuts (10)
    * `Analysis/ODE`             — ordinary differential equations (3)
    * `Analysis/Series`          — series + sequences (3)

  ## Top-level Analysis files

    * `BracketCauchyModulus`     — Cauchy modulus per dyadic bracket
    * `CauchyComplete`           — Cauchy completeness via direct construction
    * `PhysicsBridgeNT2`         — physics-track NT=2 atomic block ↔ dyadic geometry
    * `ResolutionShift`          — concrete (Nat,+)-graded structure
                                   on cut transformers; falsifiability
                                   tests for the CollapseCondition
                                   composition closure

  ## Status

  ∅-axiom standard on the production critical path.  Trajectory-as-
  witness IVT design: `theory/math/analysis/minimal_root.md`.
-/
