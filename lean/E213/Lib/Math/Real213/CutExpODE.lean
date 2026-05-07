import E213.Lib.Math.Real213.CutExpSeries

/-!
# Real213 — `cutExp` ODE characterisation (213-calculus path)

The Taylor-series construction in `CutExpSeries.lean` defines
`cutExp` as `lim_N expPartialSum x N`.  An independent derivation
characterises `cutExp` as the unique solution of the ODE

  `f'(x) = f(x)`,  `f(0) = 1`

via the existing `IsAntiderivative` / `IsDifferentiable` /
`FluxFTC` machinery in `Lib/Math/Analysis/`.

Atomic content here:

  * Initial condition `expPartialSum x 0 = 0` (rfl, empty sum).
    First non-trivial term is at `N = 1`: `expPartialSum x 1
    = constCut 0 1 + expTerm x 0 = 0 + (1 · 1) = 1` cohomologically.
  * Recurrence: `expPartialSum x (N+1) = expPartialSum x N + expTerm x N`
    is the discrete analogue of `f'(x) ≈ f(x)` (each step adds the
    next Taylor coefficient).

Full ODE proof (`derivative cutExp = cutExp`) requires
term-by-term differentiation of `expPartialSum` plus Cauchy
modulus passage, which is left as a follow-up.  The recurrence
identity here is the discrete-time analogue.
-/

namespace E213.Lib.Math.Real213.CutExpODE

open E213.Lib.Math.Real213.CutExpSeries
  (expTerm expPartialSum cutExp)

/-- Initial condition: `expPartialSum x 0 = 0` (empty sum, rfl). -/
theorem ode_initial_zero (x : Nat → Nat → Bool) :
    expPartialSum x 0
    = E213.Lib.Math.Real213.CutSumTest.constCut 0 1 := rfl

/-- ODE recurrence (discrete): each successor partial sum adds the
    next Taylor term — the finite-N analogue of `f'(x) = f(x)`. -/
theorem ode_recurrence (x : Nat → Nat → Bool) (N : Nat) :
    expPartialSum x (N + 1)
    = E213.Lib.Math.Real213.CutSum.cutSum
        (expPartialSum x N) (expTerm x N) := rfl

end E213.Lib.Math.Real213.CutExpODE
