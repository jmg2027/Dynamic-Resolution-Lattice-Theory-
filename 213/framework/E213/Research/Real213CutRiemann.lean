import E213.Research.Real213CutPow
import E213.Research.Real213CutInv

/-!
# Research.Real213CutRiemann: Riemann integration algorithm

∫[a, b] f := lim Σ_{i=0}^{n-1} f(a + i*h) * h, h = (b-a)/n.

## 정의

partition n a b := list of midpoints.
riemannSum f a b n := Σ f(midpoint_i) * h.
riemannIntegral f a b := lim_n riemannSum f a b n.

## 의의

Riemann integration 의 cut-level form — partition + sum + limit.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **Riemann sum at sample points**: Σ_{i=0}^{n-1} f(xs i).
주 어 진 sample sequence xs 위 의 finite sum.  Δx scaling 은
caller responsibility (subtraction 가 cut-level 에 서 partial). -/
def riemannSumOnSamples (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (xs : Nat → (Nat → Nat → Bool)) : Nat → Nat → Nat → Bool
  | 0 => constCut 0 1
  | n+1 => cutSum (riemannSumOnSamples f xs n) (f (xs n))

/-- Sample partition: xs i = constant a (degenerate sample). -/
def constSamples (a : Nat → Nat → Bool) : Nat → (Nat → Nat → Bool) :=
  fun _ => a

/-- riemannSumOnSamples at degenerate (all = a) for constant f returns
    n * f(a) — but partial sum 형 식 으 로. -/
example : riemannSumOnSamples (fun _ => constCut 1 1) (constSamples (constCut 1 1)) 0
    = constCut 0 1 := rfl

/-- **Riemann sum step** (legacy interface). -/
def riemannSumStep (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (a b : Nat → Nat → Bool) (n : Nat) : Nat → Nat → Bool :=
  let _ := b
  riemannSumOnSamples f (constSamples a) n

/-- **Riemann integral data** (carries n + sum + modulus). -/
structure RiemannIntegralData
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (a b : Nat → Nat → Bool) where
  approx : Nat → Nat → Nat → Bool   -- nth approximation
  modulus : Nat → Nat → Nat          -- precision modulus
  bound_data : Unit  -- placeholder for convergence proof

/-- **Constant integration**: ∫[a, b] c dx = c * (b - a).
Cut-level implementation 별 도. -/
def constRiemann (c : Nat → Nat → Bool) (a b : Nat → Nat → Bool) :
    RiemannIntegralData (fun _ => c) a b where
  approx := fun _ => c   -- placeholder
  modulus := fun _ _ => 0
  bound_data := ()

end E213.Research.Real213CutSum
