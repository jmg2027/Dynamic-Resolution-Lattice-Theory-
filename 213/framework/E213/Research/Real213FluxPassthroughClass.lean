import E213.Research.Real213FluxMVTClosure

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

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

namespace FluxCut

/-- A function passing through (0, 0) and (1, 1) on dyadic cuts. -/
structure Passthrough (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  left : f (constCut 0 1) = constCut 0 1
  right : f (constCut 1 1) = constCut 1 1

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

end E213.Research.Real213CutSum
