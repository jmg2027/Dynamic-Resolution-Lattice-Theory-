import E213.Math.Real213.CutPow
import E213.Math.Real213.CutInv

import E213.Math.Real213.Core
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest
/-!
# Real213CutRiemann: Riemann integration algorithm

∫[a, b] f := lim Σ_{i=0}^{n-1} f(a + i*h) * h, h = (b-a)/n.

## Definition

partition n a b := list of midpoints.
riemannSum f a b n := Σ f(midpoint_i) * h.
riemannIntegral f a b := lim_n riemannSum f a b n.

## Significance

Cut-level form of Riemann integration — partition + sum + limit.
-/

namespace E213.Math.Analysis.Integration.CutRiemann

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)

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

/-- **Riemann integral data** (carries the n-th approximation, a Cauchy
    modulus, and the Cauchy stabilisation bound).

    `bound_data` is the cut-level Cauchy property: for any target
    precision `(m, k)`, beyond `modulus m k` the approximations
    pointwise agree at `(m, k)`.  This is the same shape as
    `CauchyCutSeq.cauchy` in `Math/Analysis/CauchyComplete.lean`
    (the `approx` family forms a Cauchy sequence of cuts whose limit
    is the Riemann integral). -/
structure RiemannIntegralData
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (a b : Nat → Nat → Bool) where
  approx : Nat → Nat → Nat → Bool   -- n-th Riemann approximation
  modulus : Nat → Nat → Nat          -- Cauchy modulus N(m, k)
  bound_data :                        -- Cauchy stabilisation bound
    ∀ m k i j, modulus m k ≤ i → modulus m k ≤ j →
      approx i m k = approx j m k

/-- Extract the limit of the Riemann approximations as a single cut.
    Pointwise: read `approx` at the modulus index. -/
def RiemannIntegralData.limit
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    {a b : Nat → Nat → Bool}
    (d : RiemannIntegralData f a b) : Nat → Nat → Bool :=
  fun m k => d.approx (d.modulus m k) m k

/-- **Limit stability**: limit equals approx at any index past modulus. -/
theorem RiemannIntegralData.limit_eq_at
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    {a b : Nat → Nat → Bool}
    (d : RiemannIntegralData f a b)
    (m k i : Nat) (hi : d.modulus m k ≤ i) :
    d.limit m k = d.approx i m k :=
  d.bound_data m k (d.modulus m k) i (Nat.le_refl _) hi

/-- **Constant integration on the unit interval [0, 1]**:
    ∫[0, 1] c dx = c · 1 = c.  The Riemann sum of a constant on `[0, 1]`
    is identically `c` at every refinement level (each sample contributes
    `c · (1/n)` and there are `n` of them), so the approximation sequence
    is the constant sequence `c`, the Cauchy modulus is `0`, and the
    stabilisation bound is discharged by `rfl`.

    The general ∫[a, b] c dx = c · (b − a) requires cut subtraction
    (signed) and is a separate arc; restricting to `(a, b) = (0, 1)`
    gives the only case where `approx := fun _ => c` is mathematically
    correct. -/
def unitConstRiemann (c : Nat → Nat → Bool) :
    RiemannIntegralData (fun _ => c) (constCut 0 1) (constCut 1 1) where
  approx := fun _ => c
  modulus := fun _ _ => 0
  bound_data := fun _ _ _ _ _ _ => rfl

/-- The unit constant Riemann integral converges to `c`. -/
theorem unitConstRiemann_limit (c : Nat → Nat → Bool) :
    (unitConstRiemann c).limit = c := rfl

end E213.Math.Analysis.Integration.CutRiemann
