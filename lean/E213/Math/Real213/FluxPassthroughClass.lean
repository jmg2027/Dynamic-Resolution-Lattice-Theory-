import E213.Math.Real213.FluxMVTClosure

/-!
# Research.Real213FluxPassthroughClass

Phase BJ: **Passthrough class** — bundle a function with its
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

namespace E213.Math.Real213.FluxPassthroughClass

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMul (cutMulOuter)
open E213.Math.Real213.CutMulOne (cutMul_one_one cutMul_one_one_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero cutMul_zero_zero_at)
open E213.Math.Real213.CutPowConst
  (cutPow_one_n cutPow_one_n_at cutPow_zero_succ cutPow_zero_succ_at)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Real213.FluxMVTPassthrough.FluxCut
  (mvt_passthrough_unit ftc_bridge_passthrough_unit)

namespace FluxCut

/-- A function passing through (0, 0) and (1, 1) on dyadic cuts. -/
structure Passthrough (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  left : f (constCut 0 1) = constCut 0 1
  right : f (constCut 1 1) = constCut 1 1

/-- Pointwise passthrough — strict ∅-axiom variant (no funext required
    in `left/right` fields). -/
structure Passthrough_at (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k
  right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k

namespace Passthrough

/-- Identity is passthrough. -/
def id_pass : Passthrough id := { left := rfl, right := rfl }

/-- cutPow x^(n+1) is passthrough. -/
def cutPow_pass (n : Nat) : Passthrough (fun x => cutPow x (n+1)) :=
  { left := cutPow_zero_succ n, right := cutPow_one_n (n+1) }

/-- Composition of passthroughs is passthrough. -/
def compose_pass {f g} (pf : Passthrough f) (pg : Passthrough g) :
    Passthrough (g ∘ f) :=
  { left := by show g (f (constCut 0 1)) = constCut 0 1
               rw [pf.left, pg.left]
    right := by show g (f (constCut 1 1)) = constCut 1 1
                rw [pf.right, pg.right] }

/-- Product of passthroughs is passthrough. -/
def mul_pass {f g} (pf : Passthrough f) (pg : Passthrough g) :
    Passthrough (fun x => cutMul (f x) (g x)) :=
  { left := by show cutMul (f (constCut 0 1)) (g (constCut 0 1)) = constCut 0 1
               rw [pf.left, pg.left, cutMul_zero_zero]
    right := by show cutMul (f (constCut 1 1)) (g (constCut 1 1)) = constCut 1 1
                rw [pf.right, pg.right, cutMul_one_one] }

end Passthrough

namespace Passthrough_at

/-- Identity is passthrough_at. -/
def id_pass : Passthrough_at id := { left := fun _ _ => rfl, right := fun _ _ => rfl }

/-- cutPow x^(n+1) is passthrough_at. -/
def cutPow_pass (n : Nat) : Passthrough_at (fun x => cutPow x (n+1)) :=
  { left := fun m k => cutPow_zero_succ_at n m k
    right := fun m k => cutPow_one_n_at (n+1) m k }

/-- Composition of passthrough_at's is passthrough_at — only needs
    that g preserves pointwise eq, captured via `congrArg` chain.  But
    in general we need the function-eq form of pf to substitute under
    g.  This combinator therefore wraps the `Passthrough` form (DIRTY
    Quot.sound).  Pure-pointwise composition would need either f to
    be locally-determined or a stronger hypothesis. -/
def compose_pass {f g} (pf : Passthrough f) (pg : Passthrough_at g) :
    Passthrough_at (g ∘ f) :=
  { left := fun m k => by
      show g (f (constCut 0 1)) m k = constCut 0 1 m k
      rw [pf.left]; exact pg.left m k
    right := fun m k => by
      show g (f (constCut 1 1)) m k = constCut 1 1 m k
      rw [pf.right]; exact pg.right m k }

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

namespace Passthrough

/-- One-liner MVT for any Passthrough. -/
theorem mvt {f} (pf : Passthrough f) :
    localDivergence f unitBracket = ofCut (constCut 1 1) :=
  mvt_passthrough_unit f pf.left pf.right

/-- One-liner FTC bridge for any Passthrough. -/
theorem ftc {f} (pf : Passthrough f) :
    localDivergence f unitBracket = fluxAlong f unitBracket :=
  ftc_bridge_passthrough_unit f pf.left pf.right

end Passthrough

end FluxCut

end E213.Math.Real213.FluxPassthroughClass
