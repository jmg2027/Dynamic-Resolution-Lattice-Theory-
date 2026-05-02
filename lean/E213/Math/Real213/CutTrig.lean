import E213.Math.Real213.CutPow
import E213.Math.Real213.CutExp
import E213.Math.Real213.SignedSum

/-!
# Research.Real213CutTrig: sin / cos / π series at cut level

sin(x) = Σ (-1)^i x^(2i+1)/(2i+1)!
cos(x) = Σ (-1)^i x^(2i)/(2i)!
π/4 = Σ (-1)^i / (2i+1) (Leibniz)
-/

namespace E213.Math.Real213.CutTrig

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutPow (cutPow cutScale)
open E213.Math.Real213.CutSumTest (constCut)

/-- Sign of (-1)^i. -/
def altSign (i : Nat) : Bool := i % 2 = 0

/-- sin series term: (-1)^i x^(2i+1)/(2i+1)!. -/
def sinTerm (x : Nat → Nat → Bool) (i : Nat) : SignedCut where
  sign := altSign i
  cut := cutScale 1 (factorial (2*i+1)) (cutPow x (2*i+1))

/-- cos series term: (-1)^i x^(2i)/(2i)!. -/
def cosTerm (x : Nat → Nat → Bool) (i : Nat) : SignedCut where
  sign := altSign i
  cut := cutScale 1 (factorial (2*i)) (cutPow x (2*i))

/-- Leibniz π/4 term: (-1)^i / (2i+1). -/
def leibnizPiTerm (i : Nat) : SignedCut where
  sign := altSign i
  cut := constCut 1 (2*i+1)

/-- sin partial sum (degree n). -/
def sinPartial (x : Nat → Nat → Bool) : Nat → SignedCut
  | 0 => { sign := true, cut := constCut 0 1 }
  | n+1 => cutSignedSum (sinPartial x n) (sinTerm x n)

/-- cos partial sum (degree n). -/
def cosPartial (x : Nat → Nat → Bool) : Nat → SignedCut
  | 0 => { sign := true, cut := constCut 0 1 }
  | n+1 => cutSignedSum (cosPartial x n) (cosTerm x n)

/-- π/4 partial sum via Leibniz. -/
def leibnizPiPartial : Nat → SignedCut
  | 0 => { sign := true, cut := constCut 0 1 }
  | n+1 => cutSignedSum (leibnizPiPartial n) (leibnizPiTerm n)

end E213.Math.Real213.CutTrig
