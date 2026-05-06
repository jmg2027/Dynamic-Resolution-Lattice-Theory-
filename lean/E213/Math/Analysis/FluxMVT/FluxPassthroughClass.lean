import E213.Math.Analysis.FluxMVT.FluxMVTPassthrough

import E213.Math.Real213.Core
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutMulDetermined
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutPow
import E213.Math.Real213.CutPowConst
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.CutSumZero
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.FluxMVT.FluxCochain
import E213.Math.Analysis.FluxMVT.FluxCut
import E213.Math.Analysis.FluxMVT.FluxDivergence
import E213.Math.Analysis.FluxMVT.FluxMVT
/-!
# FluxPassthroughClass
Passthrough class** — bundle a function with its
endpoint witnesses + combinators making MVT/FTC instant.

  Passthrough f := { left : f(0) = 0, right : f(1) = 1 }

  combinators:
    Passthrough.id       : identity
    Passthrough.cutPow   : x → x^(n+1)
    Passthrough.compose  : g ∘ f
    Passthrough.mul      : cutMul f g

  one-liner MVT/FTC:
    Passthrough.mvt      : LD f unitBracket = ofCut 1
    Passthrough.ftc      : LD = fluxAlong (FTC bridge)
-/

namespace E213.Math.Analysis.FluxMVT.FluxPassthroughClass

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMul (cutMulOuter)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)
open E213.Math.Real213.CutPowConst (cutPow_one_n_at cutPow_zero_succ_at)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Analysis.FluxMVT.FluxMVTPassthrough.FluxCut
  (mvt_passthrough_unit_pure)

namespace FluxCut

/-- Pointwise passthrough — strict ∅-axiom variant (no funext required
    in `left/right` fields).  Sole Passthrough class — function-eq
    Passthrough was deleted 2026-05-XX session 27 ('박멸'). -/
structure Passthrough_at (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k
  right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k

namespace Passthrough_at

/-- Identity is passthrough_at. -/
def id_pass : Passthrough_at id := { left := fun _ _ => rfl, right := fun _ _ => rfl }

/-- cutPow x^(n+1) is passthrough_at. -/
def cutPow_pass (n : Nat) : Passthrough_at (fun x => cutPow x (n+1)) :=
  { left := fun m k => cutPow_zero_succ_at n m k
    right := fun m k => cutPow_one_n_at (n+1) m k }

/-- Composition of passthrough_at's — requires that f's endpoints
    reduce DEFINITIONALLY (rfl-clean) since Passthrough_at gives
    pointwise eq, not function eq.  For id ∘ id, both endpoints
    rfl-equal so this works. -/
def compose_id_id : Passthrough_at (id ∘ id) :=
  { left := fun _ _ => rfl, right := fun _ _ => rfl }

/-- Product of passthrough_at's is passthrough_at — fully pointwise
    via `cutMulOuter_congr`.  No funext, no propext, no Quot.sound. -/
def mul_pass {f g} (pf : Passthrough_at f) (pg : Passthrough_at g) :
    Passthrough_at (fun x => cutMul (f x) (g x)) :=
  { left := fun m k => by
      show cutMul (f (constCut 0 1)) (g (constCut 0 1)) m k = constCut 0 1 m k
      show cutMulOuter (f (constCut 0 1)) (g (constCut 0 1))
                       k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
      have step :
          cutMulOuter (f (constCut 0 1)) (g (constCut 0 1))
                      k m ((m+1)*(k+1)) ((m+1)*(k+1))
          = cutMulOuter (constCut 0 1) (constCut 0 1)
                      k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
        cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
          (f (constCut 0 1)) (constCut 0 1)
          (g (constCut 0 1)) (constCut 0 1)
          (fun m' _ => pf.left m' k)
          (fun m' _ => pg.left m' k)
          ((m+1)*(k+1)) (Nat.le_refl _)
      rw [step]; exact cutMul_zero_zero_at m k
    right := fun m k => by
      show cutMul (f (constCut 1 1)) (g (constCut 1 1)) m k = constCut 1 1 m k
      show cutMulOuter (f (constCut 1 1)) (g (constCut 1 1))
                       k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
      have step :
          cutMulOuter (f (constCut 1 1)) (g (constCut 1 1))
                      k m ((m+1)*(k+1)) ((m+1)*(k+1))
          = cutMulOuter (constCut 1 1) (constCut 1 1)
                      k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
        cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
          (f (constCut 1 1)) (constCut 1 1)
          (g (constCut 1 1)) (constCut 1 1)
          (fun m' _ => pf.right m' k)
          (fun m' _ => pg.right m' k)
          ((m+1)*(k+1)) (Nat.le_refl _)
      rw [step]; exact cutMul_one_one_at m k }

end Passthrough_at

namespace Passthrough_at

open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Analysis.FluxMVT.FluxMVTPassthrough.FluxCut
  (mvt_passthrough_unit_pure fluxAlong_passthrough_unit_pure
   ftc_bridge_passthrough_unit_pure)

/-- One-liner MVT (fluxCutEq, PURE) for any Passthrough_at. -/
theorem mvt_pure {f} (pf : Passthrough_at f) :
    fluxCutEq (localDivergence f unitBracket) (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure f pf.left pf.right

/-- One-liner FTC bridge (fluxCutEq, PURE) for any Passthrough_at. -/
theorem ftc_pure {f} (pf : Passthrough_at f) :
    fluxCutEq (localDivergence f unitBracket) (fluxAlong f unitBracket) :=
  ftc_bridge_passthrough_unit_pure f pf.left pf.right

end Passthrough_at

end FluxCut

end E213.Math.Analysis.FluxMVT.FluxPassthroughClass
