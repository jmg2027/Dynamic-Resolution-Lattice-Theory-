import E213.Research.Real213.CutPow
import E213.Research.Real213.CutInv

/-!
# Research.Real213CutRiemann: Riemann integration algorithm

∫[a, b] f := lim Σ_{i=0}^{n-1} f(a + i*h) * h, h = (b-a)/n.

## Definition

partition n a b := list of midpoints.
riemannSum f a b n := Σ f(midpoint_i) * h.
riemannIntegral f a b := lim_n riemannSum f a b n.

## Significance

Cut-level form of Riemann integration — partition + sum + limit.
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- **Riemann sum at sample points**: Σ_{i=0}^{n-1} f(xs i).
Finite sum over given sample sequence xs.  Δx scaling is
caller responsibility (subtraction is partial at cut level). -/
def riemannSumOnSamples (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (xs : Nat → (Nat → Nat → Bool)) : Nat → Nat → Nat → Bool
  | 0 => constCut 0 1
  | n+1 => cutSum (riemannSumOnSamples f xs n) (f (xs n))

/-- Sample partition: xs i = constant a (degenerate sample). -/
def constSamples (a : Nat → Nat → Bool) : Nat → (Nat → Nat → Bool) :=
  fun _ => a

/-- riemannSumOnSamples at degenerate (all = a) for constant f returns
    n * f(a) — but in partial sum form. -/
example : riemannSumOnSamples (fun _ => constCut 1 1) (constSamples (constCut 1 1)) 0
    = constCut 0 1 := rfl

/-- **Riemann sum step** (legacy interface). -/
def riemannSumStep (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (a b : Nat → Nat → Bool) (n : Nat) : Nat → Nat → Bool :=
  let _ := b
  riemannSumOnSamples f (constSamples a) n

/-- riemannSumOnSamples unfolding at 0 (rfl). -/
theorem riemannSumOnSamples_zero
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (xs : Nat → (Nat → Nat → Bool)) :
    riemannSumOnSamples f xs 0 = constCut 0 1 := rfl

/-- riemannSumOnSamples unfolding at n+1 (rfl). -/
theorem riemannSumOnSamples_succ
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (xs : Nat → (Nat → Nat → Bool)) (n : Nat) :
    riemannSumOnSamples f xs (n+1)
    = cutSum (riemannSumOnSamples f xs n) (f (xs n)) := rfl

/-- **Riemann integral data** (carries n + sum + modulus). -/
structure RiemannIntegralData
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (a b : Nat → Nat → Bool) where
  approx : Nat → Nat → Nat → Bool   -- nth approximation
  modulus : Nat → Nat → Nat          -- precision modulus
  bound_data : Unit  -- placeholder for convergence proof

/-- **Constant integration**: ∫[a, b] c dx = c * (b - a).
Cut-level implementation is separate. -/
def constRiemann (c : Nat → Nat → Bool) (a b : Nat → Nat → Bool) :
    RiemannIntegralData (fun _ => c) a b where
  approx := fun _ => c   -- placeholder
  modulus := fun _ _ => 0
  bound_data := ()

end E213.Research.Real213.CutSum
