import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries
import E213.Lib.Math.Probability.Inequality.Concentration

/-!
# Probability — Hoeffding-style exponential bound (atomic)

Atomic exponential-tail concentration using the `cutExp` Taylor
series from `Real213.CutExpSeries`.

For a fair-coin balanced sample of length `2n`, the centered
deviation is `0`, so the Hoeffding bound `2 · exp(−2 n ε²)`
trivialises to `2 · exp(0) = 2`.

For non-trivial sequences, the bound is stated in *finite-N*
form: `2 · expPartialSum (negTwoNEpsSqr) N`.  The Cauchy
modulus passage `N → ∞` gives the closed Hoeffding inequality;
the modulus argument is left as a follow-up
(`Real213.CutExpSeries` Cauchy-modulus is the gating piece).
-/

namespace E213.Lib.Math.Probability.Inequality.Hoeffding

open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpSeries (expPartialSum cutExp)
open E213.Lib.Math.Probability.Inequality.Concentration
  (centeredAbsDev2 centeredAbsDev2_balanced)
open E213.Lib.Math.Probability.Limit.LLN (balancedHeadsTails)

/-- Atomic Hoeffding bound at finite Taylor depth `N`:
    `2 · expPartialSum x N`, where `x` encodes `−2 n ε²`.  Returns a
    cut function — caller specifies the negative-`x` argument. -/
def hoeffdingBoundAtDepth (negArg : Nat → Nat → Bool) (N : Nat)
    : Nat → Nat → Bool :=
  expPartialSum negArg N

/-- At depth 0 the bound is `expPartialSum negArg 0 = 0` (rfl).  This
    is the "before any Taylor terms" baseline; the actual bound
    grows as `N` increases. -/
theorem hoeffdingBound_depth_zero (negArg : Nat → Nat → Bool) :
    hoeffdingBoundAtDepth negArg 0
    = E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest.constCut 0 1 := rfl

/-- ★ **Balanced collapse** ★ — for fair-coin balanced sample of
    length `2n`, the deviation is identically zero.  This is the
    finite-sample version of "Hoeffding bound trivialises at zero
    deviation". -/
theorem hoeffding_balanced_zero_dev (n : Nat) :
    centeredAbsDev2 (balancedHeadsTails n) = 0 :=
  centeredAbsDev2_balanced n

/-- Universal `cutExp(0) = 0` at finite depth 0 — the partial-sum
    baseline, before any Taylor terms.  Atomic placeholder for the
    full Hoeffding bound which kicks in at `N ≥ 1`. -/
theorem cutExp_zero_baseline (negArg : Nat → Nat → Bool) :
    cutExp negArg 0
    = E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest.constCut 0 1 := rfl

/-- Hoeffding bound at depth `N` is the cut-function partial Taylor
    sum (rfl, by definition).  Convergence to `2 · exp(...)` as
    `N → ∞` follows from `CutExpSeries` Cauchy-modulus (deferred). -/
theorem hoeffdingBound_eq_partialSum
    (negArg : Nat → Nat → Bool) (N : Nat) :
    hoeffdingBoundAtDepth negArg N = expPartialSum negArg N := rfl

end E213.Lib.Math.Probability.Inequality.Hoeffding
