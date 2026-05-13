import E213.Lib.Math.Analysis.FluxMVT.FluxPassthroughClass

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Lib.Math.Analysis.FluxMVT.FluxCochain
import E213.Lib.Math.Analysis.FluxMVT.FluxCut
import E213.Lib.Math.Analysis.FluxMVT.FluxDivergence
import E213.Lib.Math.Analysis.FluxMVT.FluxMVT
/-!
# FluxPassthroughCatalog
catalog of Passthrough instances built via combinators.

Demonstrates compositionality: any function buildable from id,
cutPow, ∘, cutMul yields automatic MVT + FTC at unit bracket
through one-liner combinator chains.
-/

namespace E213.Lib.Math.Analysis.FluxMVT.FluxPassthroughCatalog

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong)
open E213.Lib.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Lib.Math.Analysis.FluxMVT.FluxPassthroughClass.FluxCut (Passthrough_at)

namespace FluxCut.Passthrough_at

open E213.Lib.Math.Analysis.FluxMVT.FluxPassthroughClass.FluxCut.Passthrough_at
  (id_pass cutPow_pass mul_pass mvt_pure)
open E213.Lib.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq)

/-- x ↦ x via id (pointwise). -/
def x_pass : Passthrough_at id := id_pass

/-- x ↦ x · x via mul (PURE pointwise). -/
def square_pass : Passthrough_at (fun x => cutMul x x) :=
  mul_pass id_pass id_pass

/-- x ↦ x · (x · x) via mul + mul (PURE pointwise). -/
def cube_pass : Passthrough_at (fun x => cutMul x (cutMul x x)) :=
  mul_pass id_pass square_pass

/-- x ↦ (x · x) · (x · x) via mul + mul (PURE pointwise). -/
def quartic_pass :
    Passthrough_at (fun x => cutMul (cutMul x x) (cutMul x x)) :=
  mul_pass square_pass square_pass

/-- x ↦ (x · x) · (x · x · x) — quintic (PURE pointwise). -/
def quintic_pass :
    Passthrough_at (fun x => cutMul (cutMul x x) (cutMul x (cutMul x x))) :=
  mul_pass square_pass cube_pass

/-- x ↦ id · x² = x · x² via mul (PURE pointwise). -/
def id_mul_square_pass :
    Passthrough_at (fun x => cutMul x (cutMul x x)) :=
  mul_pass id_pass square_pass

/-- ★ Catalog _at showcase: 5 Passthrough_at instances yield fluxCutEq
    MVT.  PURE — strict ∅-axiom. -/
theorem catalog_mvt_capstone_at :
    fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
                (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x))
                                 unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutMul (cutMul x x)
                                  (cutMul x x)) unitBracket)
                (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutMul (cutMul x x)
                                  (cutMul x (cutMul x x))) unitBracket)
                (ofCut (constCut 1 1)) :=
  ⟨mvt_pure x_pass, mvt_pure square_pass,
   mvt_pure cube_pass, mvt_pure quartic_pass,
   mvt_pure quintic_pass⟩

end FluxCut.Passthrough_at

end E213.Lib.Math.Analysis.FluxMVT.FluxPassthroughCatalog
