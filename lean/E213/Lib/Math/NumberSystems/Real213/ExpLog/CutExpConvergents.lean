import E213.Lib.Math.Analysis.Cauchy.Euler
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpModulus
import E213.Meta.Nat.PolyNatMTactic

/-!
# Real213 — exp(m) rational convergents + cross-determinant (∅-axiom)

**Marathon T1**, algebraic route.

`EulerModulus` gave e = exp(1) a *total* constructive cut modulus by feeding its convergents'
**cross-determinant** into `RateModulus`.  This file generalizes the convergent arithmetic to
**exp(m) for every integer argument `m`**, so the same machine can lift exp at any integer to a
constructive `Real213` point.

The `n`-th partial sum of `Σ mᵏ/k!` over the common denominator `n!` is `expNum m n / eulerDen n`,
with `eulerDen n = n!` (reused from `EulerSeq`) and

  `expNum m 0 = 1`,   `expNum m (n+1) = (n+1)·expNum m n + m^{n+1}`

(the new term `m^{n+1}/(n+1)!` contributes `m^{n+1}` to the numerator over `(n+1)!`).  At `m = 1`
this is exactly Euler's `eulerNum` (`expNum_one`).

The key object is the **cross-determinant**

  `expNum m (n+1)·eulerDen n − expNum m n·eulerDen (n+1) = m^{n+1}·eulerDen n`

(`exp_cross_det`) — the generalization of `euler_cross_det` (where `m = 1` collapses the right side
to `eulerDen n = n!`).  Being positive (for `m ≥ 1`) it gives strict monotonicity of the convergents
(`exp_convergents_mono`).

## Honest boundary — why e's clean modulus is `m = 1`-special

Feeding this cross-determinant `W_i = m^{i+1}·eulerDen i` into `RateModulus.Htel_of_crossdet` reduces the
rate certificate to `i(i+1)·m^{i+1} + i ≤ (i+1)²` (after factoring out `eulerDen i`).  At `m = 1` this is
`i(i+1)+i ≤ (i+1)²` — true for all `i ≥ 1`, which is exactly why **e** gets the clean total modulus
`N(m,k) = k+2` (`EulerModulus`).  For `m ≥ 2` the term `m^{i+1}` blows the bound — it **fails** already at
`i = 1` (`exp_two_rate_fails_at_one`: `1·2·2² + 1 = 9 > 4 = 2²`).  So the simple margin `e_i + 1/(i·d_i)`
is *not* non-increasing from `i = 1` for `m ≥ 2`; the convergence only kicks in past the threshold `i ≈ 2m`.
General exp(m)'s modulus therefore comes from the **analytic** route — the geometric majorant
`CutExpModulus` with its `2M` threshold — not from the `RateModulus` rate certificate.  The two routes are
genuinely complementary: algebraic (this file, clean for e) and analytic (`CutExpModulus`, general `m`).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpConvergents

open E213.Lib.Math.Analysis.Cauchy.EulerSeq (eulerNum eulerDen eulerDen_pos)

/-- Numerator of the `n`-th partial sum of `Σ mᵏ/k!` over common denominator `n!`:
    `Aₙ = Σ_{k≤n} mᵏ·n!/k!`, recursion `A_{n+1} = (n+1)·Aₙ + m^{n+1}`. -/
def expNum (m : Nat) : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * expNum m n + m ^ (n + 1)

/-- `expNum m (n+1) = (n+1)·expNum m n + m^{n+1}` (rfl). -/
theorem expNum_succ (m n : Nat) :
    expNum m (n + 1) = (n + 1) * expNum m n + m ^ (n + 1) := rfl

/-- The denominators are the factorials — shared with Euler's e. -/
theorem expDen_succ (n : Nat) : eulerDen (n + 1) = (n + 1) * eulerDen n := rfl

/-- ★ **At `m = 1` the convergents are Euler's e.**  `expNum 1 n = eulerNum n` — exp(1) = e. -/
theorem expNum_one (n : Nat) : expNum 1 n = eulerNum n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (k + 1) * expNum 1 k + 1 ^ (k + 1) = (k + 1) * eulerNum k + 1
    rw [ih, Nat.one_pow]

/-- ★★★ **The exp(m) cross-determinant** — generalizes `euler_cross_det`.

      `expNum m (n+1)·eulerDen n = expNum m n·eulerDen (n+1) + m^{n+1}·eulerDen n`.

    The cross-determinant of consecutive convergents is exactly `m^{n+1}·n!` (`= n!` when `m = 1`,
    recovering Euler).  This is the rate certificate `RateModulus` consumes to build exp(m)'s
    total modulus. -/
theorem exp_cross_det (m n : Nat) :
    expNum m (n + 1) * eulerDen n
      = expNum m n * eulerDen (n + 1) + m ^ (n + 1) * eulerDen n := by
  rw [expNum_succ, expDen_succ]
  -- ((n+1)·Aₙ + m^{n+1})·Dₙ = Aₙ·((n+1)·Dₙ) + m^{n+1}·Dₙ
  ring_nat

/-- ★★ **The convergents strictly increase** (for `m ≥ 1`): `Aₙ·D_{n+1} < A_{n+1}·Dₙ`
    (cross-multiplied `eₙ < e_{n+1}`).  Immediate from `exp_cross_det`: the gap is exactly
    `m^{n+1}·eulerDen n ≥ 1`.  The monotonicity `RateModulus` pairs with the cross-determinant to
    pin the limit. -/
theorem exp_convergents_mono (m n : Nat) (hm : 1 ≤ m) :
    expNum m n * eulerDen (n + 1) < expNum m (n + 1) * eulerDen n := by
  rw [exp_cross_det]
  refine Nat.lt_add_of_pos_right ?_
  exact Nat.mul_pos (Nat.pos_pow_of_pos (n + 1) hm) (eulerDen_pos n)

/-- ★★ **The `RateModulus` rate certificate fails for exp(2) at `i = 1`** — the concrete
    boundary witness.  `Htel_of_crossdet`'s condition `i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}` with
    `W_i = m^{i+1}·eulerDen i` at `m = 2, i = 1` reads `1·2·(2²·1) + 1·1 = 9 > 4 = 2·eulerDen 2`.
    So the clean `N = k+2` modulus is genuinely e-special; exp(m≥2) needs the analytic
    `CutExpModulus` threshold `2m`.  (Contrast: at `m = 1, i = 1` the condition is `3 ≤ 4`, true.) -/
theorem exp_two_rate_fails_at_one :
    ¬ (1 * (1 + 1) * (2 ^ (1 + 1) * eulerDen 1) + 1 * eulerDen 1
        ≤ (1 + 1) * eulerDen (1 + 1)) := by decide

/-- The same condition **holds** at `m = 1, i = 1` (`3 ≤ 4`) — the e case `RateModulus` consumes. -/
theorem exp_one_rate_holds_at_one :
    1 * (1 + 1) * (1 ^ (1 + 1) * eulerDen 1) + 1 * eulerDen 1
      ≤ (1 + 1) * eulerDen (1 + 1) := by decide

/-! ## The two routes unified — convergent increment = Taylor term

The algebraic convergents (this file) and the analytic Taylor series (`CutExpModulus`)
are the *same* object: the partial-sum increment `e_{i+1} − e_i` is exactly the next
Taylor term `m^{i+1}/(i+1)!`.  Hence the convergent gaps inherit the analytic geometric
majorant — the convergents are Cauchy with the `2m`-threshold modulus, the route that
actually delivers exp(m)'s total modulus (the `RateModulus` margin being e-special, above). -/

/-- The convergent denominators are the Taylor denominators: `eulerDen n = n!`
    (`CutFactorial.factorial`).  Bridges the algebraic and analytic factorials. -/
theorem eulerDen_eq_factorial (n : Nat) :
    eulerDen n = E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial.factorial n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (k + 1) * eulerDen k
      = (k + 1) * E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial.factorial k
    rw [ih]

/-- ★★ **Convergent increment = Taylor term.**  `e_{i+1} − e_i = m^{i+1}/(i+1)!`: over the
    common denominator `eulerDen (i+1) = (i+1)!`, the increment numerator is exactly
    `m^{i+1}` — the numerator of the `(i+1)`-th Taylor term.  `expNum m (i+1) − (i+1)·expNum m i
    = m^{i+1}`, i.e. the partial-sum step adds precisely the next Taylor term.  The identity
    welding the algebraic convergents to the analytic series. -/
theorem exp_increment_eq_taylor (m i : Nat) :
    expNum m (i + 1) = (i + 1) * expNum m i + m ^ (i + 1) := expNum_succ m i

/-- ★★★ **Convergent gaps decay geometrically past `2m`** (the Cauchy rate, analytically
    sourced).  The Taylor terms `m^l/l!` — which ARE the convergent increments — satisfy
    `2ʲ·m^{2m+j}·(2m)! ≤ m^{2m}·(2m+j)!` (`CutExpModulus.expTail_geom_decay`, here over the
    convergent denominators `eulerDen`).  So the convergent increments are squeezed below any
    dyadic past `2m`: the convergents `expNum m i / eulerDen i` form a Cauchy sequence with the
    explicit `2m`-threshold modulus — exp(m) is a constructive real via the analytic rate,
    *not* the e-special `RateModulus` margin. -/
theorem exp_increment_geom_decay (m j : Nat) :
    2 ^ j * m ^ (2 * m + j) * eulerDen (2 * m)
      ≤ m ^ (2 * m) * eulerDen (2 * m + j) := by
  rw [eulerDen_eq_factorial, eulerDen_eq_factorial]
  exact E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpModulus.expTail_geom_decay m j

end E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpConvergents
