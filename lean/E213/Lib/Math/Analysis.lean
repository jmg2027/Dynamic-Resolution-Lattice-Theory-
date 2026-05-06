import E213.Lib.Math.Real213
import E213.Lib.Math.Analysis.ClassicCalc
import E213.Lib.Math.Analysis.Differentiation
import E213.Lib.Math.Analysis.DyadicSearch
import E213.Lib.Math.Analysis.FluxMVT
import E213.Lib.Math.Analysis.Integration
import E213.Lib.Math.Analysis.ODE
import E213.Lib.Math.Analysis.Series
import E213.Lib.Math.Analysis.BracketCauchyModulus
import E213.Lib.Math.Analysis.CauchyComplete
import E213.Lib.Math.Analysis.PhysicsBridgeNT2
import E213.Lib.Math.Analysis.ResolutionShift

/-! Spec-as-code entry point for `E213.Lib.Math.Analysis`.

  213-native analysis — calculus on top of `Math/Real213`.

  Importing this module pulls in the Real213 base type AND all of
  Analysis on top.

  ## Chapters (sub-directory umbrellas)

    * `Analysis/ClassicCalc`     — applied calculus structure (3 files)
    * `Analysis/Differentiation` — differential calculus, polynomial chain (14)
    * `Analysis/DyadicSearch`    — dyadic-search IVT (9 files,
                                   includes G31 trajectory-as-witness
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

  ## Status

  ∅-axiom standard on the production critical path.  Trajectory-as-
  witness IVT design recorded in `research-notes/G31_minimal_root_lens.md`.
-/
