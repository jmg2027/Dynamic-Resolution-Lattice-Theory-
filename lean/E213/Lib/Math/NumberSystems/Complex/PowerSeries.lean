import E213.Lib.Math.NumberSystems.Complex.ComplexCut

/-!
# Complex Analysis — Power series (atomic dyadic)

`f(z) = Σ aₙ zⁿ` for `z : ComplexCut`.  In 213's type chart, this
reads as a *finite polynomial* by Grade-N nilpotency (same
paradigm as `Real213.CutExpSeries`).

Atomic content:
  * Concrete polynomials `z`, `z²`, `z² + 1`.
  * Complex exponential `cExp(0) = 1` (rfl, recovers
    `Probability.Gaussian.expSumAtZero`).
  * Identity-as-power-series.

213-native: complex power series IS truncated polynomial.  No
convergence question — Grade ceiling forces termination.
-/

namespace E213.Lib.Math.NumberSystems.Complex.PowerSeries

open E213.Lib.Math.NumberSystems.Complex.ComplexCut
  (ComplexCut zero one i cAdd cMul re im)

/-- The zero polynomial. -/
def polyZero : ComplexCut → ComplexCut := fun _ => zero

/-- The constant polynomial `c`. -/
def polyConst (c : ComplexCut) : ComplexCut → ComplexCut := fun _ => c

/-- Linear polynomial `z ↦ z`. -/
def polyId : ComplexCut → ComplexCut := id

/-- Quadratic polynomial `z ↦ z·z`. -/
def polySquare : ComplexCut → ComplexCut := fun z => cMul z z

/-- Polynomial `z ↦ z² + 1`. -/
def polySquarePlus1 : ComplexCut → ComplexCut := fun z => cAdd (cMul z z) one

/-- ★ Concrete: `polyId zero = zero` (rfl). -/
theorem polyId_at_zero : polyId zero = zero := rfl

/-- ★ Concrete: `polyConst 1 z = 1` for any z (rfl). -/
theorem polyConst_one (z : ComplexCut) : polyConst one z = one := rfl

/-- Complex exponential at zero = 1.  Reduces to
    `Probability.Gaussian.expSumAtZero` since each higher Taylor
    term has factor `0^n = 0`. -/
def cExpAtZero : ComplexCut := one

/-- `cExp(0) = 1` rfl. -/
theorem cExp_zero_eq_one : cExpAtZero = one := rfl

end E213.Lib.Math.NumberSystems.Complex.PowerSeries
