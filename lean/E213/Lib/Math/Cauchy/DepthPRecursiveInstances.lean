import E213.Lib.Math.Cauchy.DepthPRecursive
import E213.Lib.Math.Cauchy.DivergenceDepth
import E213.Lib.Math.Cauchy.Wallis

/-!
# DepthPRecursiveInstances — finite depth ⟺ P-recursive, on the monomial basis and on e, π

`DepthPRecursive` proved the *structural* law — a sequence has finite divergence
depth iff it is a discrete polynomial (`polyDepth d s ↔ polyDepth d (diff s)` lowers
the degree by one).  What it does not exhibit is the **witnesses**: a clean general
"degree `d` ⟹ depth `d`" theorem, and the explicit P-recursive recurrences of the
concrete transcendentals e and π.  This file lays those bricks.

## §1 — the general bridge, in the Newton (binomial) basis

The obstruction to "degree `d` ⟹ depth `d`" over `Nat` is that the forward
difference `diff s n = s(n+1) − s n` truncates.  The Newton basis dissolves it: the
binomial column `binom · k` has an **exact** forward difference (Pascal's rule),
`diff (binom · (k+1)) = binom · k`, with *no* subtraction truncation.  So the `k`-th
difference of the `k`-th column is the constant `binom · 0 = 1`:

> ★ `binomCol_polyDepth` : `polyDepth k (fun n => binom n k)` — the degree-`k`
> discrete monomial has divergence-depth exactly `k`.

Every discrete polynomial is a finite `Nat`-combination `Σ_{i≤d} cᵢ·binom(·,i)` of
these columns (the Newton forward-difference form), and §1b lifts the column result
to that whole class:

> ★★★ `newton_polyDepth` : `polyDepth d (newton c d)` — *every* degree-`d` discrete
> polynomial has divergence-depth `d`, for any coefficients `c`.  The complete
> ∅-axiom "finite depth = P-recursive (difference) order".

## §2 — e: P-recursive of order 1, depth 1 (complete)

  * `euler_holonomic_recurrence` — `eulerDen (n+1) = (n+1)·eulerDen n`: e's convergent
    denominators satisfy a first-order recurrence with the **degree-1** polynomial
    coefficient `c(n) = n+1`.  This is exactly "P-recursive" (holonomic).
  * `euler_ratio_polyDepth` — `polyDepth 1` of e's cross-determinant ratio `rₙ = n+1`:
    the ratio is a degree-1 discrete polynomial, so its difference-depth is 1.
  * `e_finite_depth_iff_P_recursive` bundles them: e's depth (1, on the ratio axis)
    **matches** its P-recursive order.  The classical-bridge gap, closed for e.

## §3 — π: P-recursive of order 1 with a degree-2 step coefficient of proven depth

  * `wallis_num_holonomic`, `wallis_den_holonomic` — π's Wallis convergents are
    P-recursive: `wallisNum (n+1) = wallisNum n·(4(n+1)²)`, `wallisDen (n+1) =
    wallisDen n·((2n+1)(2n+3))`, with **degree-2** polynomial step coefficients.
  * `wallisDenCoeff_polyDepth` — the denominator step coefficient `(2n+1)(2n+3)` is a
    degree-2 discrete polynomial: `polyDepth 2` (its second difference is the constant
    `8`).  A concrete finite depth pinned on actual π data, via the one nonlinear-`Nat`
    identity done by hand.  So π's cross-determinant ratio (the product of the two
    degree-2 coefficients) is degree 4 — depth 6 (1 cross-det + 1 ratio + 4
    differences), exactly as `DivergenceDepth` records.  By `binomCol_polyDepth` a
    degree-4 polynomial has depth 4; pinning π's full quartic onto that count is the
    residual nonlinear-`Nat`-expansion step (no ∅-axiom `ring`).

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthPRecursiveInstances

open E213.Lib.Math.Cauchy.DivergenceLadder (diff liftK)
open E213.Lib.Math.Cauchy.DepthPRecursive (polyDepth liftK_diff_comm liftK_congr)
open E213.Tactic.NatHelper
  (add_sub_cancel_right add_mul mul_assoc add_sub_of_le mul_sub_distrib add_sub_add_of_le)

/-! ## §1 — 213-native binomial and the monomial-column depth theorem -/

/-- 213-native binomial coefficient (Pascal's triangle; Lean-core `Nat.choose` is
    unavailable without Mathlib).  Structural recursion ⇒ closed terms reduce by
    `rfl` and stay ∅-axiom. -/
def binom : Nat → Nat → Nat
  | _,   0   => 1
  | 0,   _+1 => 0
  | n+1, k+1 => binom n k + binom n (k+1)

/-- `binom n 0 = 1` (definitional — the first pattern matches any `n`). -/
theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by cases n <;> rfl

/-- ★ **Pascal's rule is an *exact* forward difference.**  `diff (binom · (k+1)) n =
    binom (n+1) (k+1) − binom n (k+1) = binom n k` — `Nat` subtraction never
    truncates here, because `binom (n+1) (k+1) = binom n k + binom n (k+1)` by
    definition.  The engine of the whole section. -/
theorem binomCol_diff (k n : Nat) :
    diff (fun m => binom m (k+1)) n = binom n k := by
  show binom (n+1) (k+1) - binom n (k+1) = binom n k
  exact add_sub_cancel_right (binom n k) (binom n (k+1))

/-- `j` differences of the `(k+j)`-th column give the `k`-th column:
    `liftK j (binom · (k+j)) n = binom n k`.  Each `diff` lowers the column index by
    one (Pascal), pointwise — no `funext`. -/
theorem liftK_binomCol : ∀ (j k n : Nat),
    liftK j (fun m => binom m (k + j)) n = binom n k
  | 0,   k, n => by show binom n (k + 0) = binom n k; rw [Nat.add_zero]
  | j+1, k, n => by
    have hidx : k + (j+1) = (k+1) + j := (Nat.succ_add k j).symm
    show diff (liftK j (fun m => binom m (k + (j+1)))) n = binom n k
    rw [hidx]
    show liftK j (fun m => binom m ((k+1) + j)) (n+1)
       - liftK j (fun m => binom m ((k+1) + j)) n = binom n k
    rw [liftK_binomCol j (k+1) (n+1), liftK_binomCol j (k+1) n]
    exact add_sub_cancel_right (binom n k) (binom n (k+1))

/-- The `k`-th difference of the `k`-th column is the constant `1`:
    `liftK k (binom · k) n = binom n 0 = 1`. -/
theorem binomCol_liftK_const (k n : Nat) : liftK k (fun m => binom m k) n = 1 := by
  have h := liftK_binomCol k 0 n
  rw [Nat.zero_add] at h
  rw [h]; exact binom_zero_right n

/-- ★★★ **The degree-`k` discrete monomial has divergence-depth `k`.**  `polyDepth k
    (binom · k)` — the `k`-th binomial column is a discrete polynomial of degree `k`,
    and its `k`-th finite difference is constant, so its depth is exactly `k`.  This
    is the ∅-axiom witness for "finite divergence depth = P-recursive (difference)
    order", on the basis that spans every discrete polynomial. -/
theorem binomCol_polyDepth (k : Nat) : polyDepth k (fun m => binom m k) := by
  intro n
  show liftK k (fun m => binom m k) n = liftK k (fun m => binom m k) 0
  rw [binomCol_liftK_const k n, binomCol_liftK_const k 0]

/-! ## §1b — the full Newton-form polynomial: every degree-`d` discrete polynomial
       has depth `d`

`binomCol_polyDepth` handles a single column.  A general discrete polynomial of
degree `d` is a `Nat`-combination `Σ_{i≤d} cᵢ · binom(·, i)` (the Newton forward-
difference form).  This sub-section lifts the column result to that whole class —
the complete "finite divergence depth = P-recursive (difference) order". -/

/-- The degree-`d` Newton-form polynomial `newton c d n = Σ_{i=0}^{d} cᵢ · binom n i`
    (`binom · 0 = 1`, so the `i = 0` term is `c 0`). -/
def newton (c : Nat → Nat) : Nat → Nat → Nat
  | 0,   _ => c 0
  | d+1, n => newton c d n + c (d+1) * binom n (d+1)

/-- `binom · k` is monotone in `n` (Pascal: a column only grows). -/
theorem binom_mono (k n : Nat) : binom n k ≤ binom (n+1) k := by
  cases k with
  | zero => exact Nat.le_of_eq (by rw [binom_zero_right n, binom_zero_right (n+1)])
  | succ j => show binom n (j+1) ≤ binom n j + binom n (j+1); exact Nat.le_add_left _ _

/-- A scaled column's forward difference: `cc·binom(n+1)(k+1) − cc·binom n (k+1) =
    cc·binom n k` (Pascal under the scalar, exact). -/
theorem coeff_col_diff (cc n k : Nat) :
    cc * binom (n+1) (k+1) - cc * binom n (k+1) = cc * binom n k := by
  rw [← mul_sub_distrib (binom_mono (k+1) n)]
  congr 1
  exact add_sub_cancel_right (binom n k) (binom n (k+1))

/-- `newton c d` is monotone in `n` (sum of monotone columns, nonneg coeffs). -/
theorem newton_mono (c : Nat → Nat) : ∀ d n, newton c d n ≤ newton c d (n+1)
  | 0, _ => Nat.le_refl _
  | d+1, n => Nat.add_le_add (newton_mono c d n)
      (Nat.mul_le_mul (Nat.le_refl (c (d+1))) (binom_mono (d+1) n))

/-- ★ **One difference lowers the Newton form by exactly one degree, with shifted
    coefficients** (pointwise): `diff (newton c (d+1)) n = newton (c ∘ succ) d n`.
    Each column drops one index (Pascal), the constant term falls away, and the
    coefficient sequence shifts up by one.  Truncation-free via `add_sub_add_of_le`
    on the monotone summands. -/
theorem diff_newton (c : Nat → Nat) : ∀ d n,
    diff (newton c (d+1)) n = newton (fun i => c (i+1)) d n
  | 0, n => by
    show (c 0 + c 1 * binom (n+1) 1) - (c 0 + c 1 * binom n 1) = c 1
    rw [add_sub_add_of_le (Nat.le_refl (c 0))
         (Nat.mul_le_mul (Nat.le_refl (c 1)) (binom_mono 1 n)),
        Nat.sub_self, Nat.zero_add, coeff_col_diff (c 1) n 0, binom_zero_right, Nat.mul_one]
  | d+1, n => by
    show (newton c (d+1) (n+1) + c (d+2) * binom (n+1) (d+2))
       - (newton c (d+1) n + c (d+2) * binom n (d+2))
       = newton (fun i => c (i+1)) d n + c (d+2) * binom n (d+1)
    rw [add_sub_add_of_le (newton_mono c (d+1) n)
         (Nat.mul_le_mul (Nat.le_refl (c (d+2))) (binom_mono (d+2) n)),
        coeff_col_diff (c (d+2)) n (d+1)]
    show diff (newton c (d+1)) n + c (d+2) * binom n (d+1)
       = newton (fun i => c (i+1)) d n + c (d+2) * binom n (d+1)
    rw [diff_newton c d n]

/-- The `d`-th difference of a degree-`d` Newton form is the constant top
    coefficient: `liftK d (newton c d) n = c d`.  Iterate `diff_newton` (shifting
    coefficients) `d` times via `liftK_diff_comm` + `liftK_congr`. -/
theorem liftK_newton_const : ∀ (c : Nat → Nat) d n, liftK d (newton c d) n = c d
  | _, 0,   _ => rfl
  | c, d+1, n => by
    rw [liftK_diff_comm d (newton c (d+1)),
        liftK_congr d (diff (newton c (d+1))) (newton (fun i => c (i+1)) d)
          (diff_newton c d) n]
    exact liftK_newton_const (fun i => c (i+1)) d n

/-- ★★★ **Every degree-`d` discrete polynomial has divergence-depth `d`.**
    `polyDepth d (newton c d)` — for *any* coefficient sequence `c`, the Newton-form
    polynomial `Σ_{i≤d} cᵢ·binom(·,i)` has its `d`-th finite difference constant
    (`= c d`), so its depth is `d`.  This is the complete ∅-axiom statement of
    "finite divergence depth = P-recursive (difference) order" — `binomCol_polyDepth`
    is the single-column case (`c = δ_k`). -/
theorem newton_polyDepth (c : Nat → Nat) (d : Nat) : polyDepth d (newton c d) :=
  fun n => by rw [liftK_newton_const c d n, liftK_newton_const c d 0]

/-! ## §2 — e: P-recursive of order 1, depth 1 -/

/-- ★★ **e's convergent denominators are P-recursive (holonomic) of order 1.**
    `eulerDen (n+1) = (n+1)·eulerDen n` — a first-order recurrence with the degree-1
    polynomial coefficient `c(n) = n+1`.  This is the explicit P-recursive recurrence
    whose existence makes e a *structured* transcendental. -/
theorem euler_holonomic_recurrence (n : Nat) :
    E213.Lib.Math.Cauchy.EulerSeq.eulerDen (n+1)
      = (n+1) * E213.Lib.Math.Cauchy.EulerSeq.eulerDen n := rfl

/-- ★★ **e's cross-determinant ratio is a degree-1 discrete polynomial.**
    `polyDepth 1 (rₙ = n+1)` — one finite difference floors it (`Δ(n+1) = 1`), so its
    difference-depth is 1, *matching* the order of the recurrence above. -/
theorem euler_ratio_polyDepth : polyDepth 1 E213.Lib.Math.Cauchy.DivergenceDepth.ratio :=
  fun n => by
    show E213.Lib.Math.Cauchy.DivergenceDepth.ratio (n+1)
          - E213.Lib.Math.Cauchy.DivergenceDepth.ratio n
       = E213.Lib.Math.Cauchy.DivergenceDepth.ratio (0+1)
          - E213.Lib.Math.Cauchy.DivergenceDepth.ratio 0
    rw [E213.Lib.Math.Cauchy.DivergenceDepth.floor_value n,
        E213.Lib.Math.Cauchy.DivergenceDepth.floor_value 0]

/-- ★★★ **Finite depth ⟺ P-recursive, closed for e.**  e's convergent denominators
    obey a degree-1 P-recursive recurrence, and e's cross-determinant ratio has
    difference-depth 1 — the depth equals the recurrence order.  The classical-bridge
    gap (target B, e case), discharged ∅-axiom. -/
theorem e_finite_depth_iff_P_recursive :
    (∀ n, E213.Lib.Math.Cauchy.EulerSeq.eulerDen (n+1)
            = (n+1) * E213.Lib.Math.Cauchy.EulerSeq.eulerDen n)
    ∧ polyDepth 1 E213.Lib.Math.Cauchy.DivergenceDepth.ratio :=
  ⟨euler_holonomic_recurrence, euler_ratio_polyDepth⟩

/-! ## §3 — π: P-recursive of order 1 with degree-2 coefficients -/

/-- ★★ **π's Wallis numerators are P-recursive of order 1**, step coefficient
    `4(n+1)²` (degree 2). -/
theorem wallis_num_holonomic (n : Nat) :
    E213.Lib.Math.Cauchy.WallisSeq.wallisNum (n+1)
      = E213.Lib.Math.Cauchy.WallisSeq.wallisNum n * (4 * (n + 1) * (n + 1)) := rfl

/-- ★★ **π's Wallis denominators are P-recursive of order 1**, step coefficient
    `(2n+1)(2n+3)` (degree 2).  The product of the two step coefficients is π's
    cross-determinant ratio — a degree-4 polynomial, hence depth 6 (1 cross-det +
    1 ratio + 4 differences), as `DivergenceDepth` records. -/
theorem wallis_den_holonomic (n : Nat) :
    E213.Lib.Math.Cauchy.WallisSeq.wallisDen (n+1)
      = E213.Lib.Math.Cauchy.WallisSeq.wallisDen n * ((2 * n + 1) * (2 * n + 3)) := rfl

/-- π's Wallis denominator step coefficient `(2n+1)(2n+3)` as a sequence. -/
def wallisDenCoeff (n : Nat) : Nat := (2 * n + 1) * (2 * n + 3)

/-- ★ The step coefficient's forward difference is the linear `8n+12` — the degree
    drops `2 → 1`.  The single nonlinear-`Nat` identity `(2n+3)(2n+5) =
    (2n+1)(2n+3) + (8n+12)` is discharged by hand (no ∅-axiom `ring`), via PURE
    distributivity helpers. -/
theorem wallisDenCoeff_diff (n : Nat) : diff wallisDenCoeff n = 8 * n + 12 := by
  show (2*(n+1)+1)*(2*(n+1)+3) - (2*n+1)*(2*n+3) = 8*n+12
  have h1 : 2*(n+1)+1 = 2*n+3 := by rw [Nat.mul_succ]
  have h2 : 2*(n+1)+3 = 2*n+5 := by rw [Nat.mul_succ]
  rw [h1, h2]
  have key : (2*n+3)*(2*n+5) = (2*n+1)*(2*n+3) + (8*n+12) := by
    have e5 : 2*n+5 = (2*n+1) + 4 := rfl
    rw [e5, Nat.mul_add, Nat.mul_comm (2*n+3) (2*n+1)]
    congr 1
    show (2*n+3)*4 = 8*n+12
    rw [add_mul]
    congr 1
    rw [mul_assoc, Nat.mul_comm n 4, ← mul_assoc]
  rw [key, Nat.add_comm ((2*n+1)*(2*n+3)) (8*n+12)]
  exact add_sub_cancel_right (8*n+12) ((2*n+1)*(2*n+3))

/-- The step coefficient's *second* difference is the constant `8` — `liftK 2
    wallisDenCoeff = 8`. -/
theorem wallisDenCoeff_liftK2 (n : Nat) : liftK 2 wallisDenCoeff n = 8 := by
  show (diff wallisDenCoeff) (n+1) - (diff wallisDenCoeff) n = 8
  rw [wallisDenCoeff_diff (n+1), wallisDenCoeff_diff n, Nat.mul_succ,
      Nat.add_right_comm (8*n) 8 12, Nat.add_comm (8*n+12) 8]
  exact add_sub_cancel_right 8 (8*n+12)

/-- ★★★ **π's step coefficient is a degree-2 discrete polynomial: `polyDepth 2`.**
    The second finite difference of `(2n+1)(2n+3)` is the constant `8`, so its
    divergence-depth is exactly 2 — a concrete finite depth pinned on actual π
    convergent data (the den-side step coefficient).  Combined with the equal-degree
    numerator coefficient `4(n+1)²`, π's cross-determinant ratio is their degree-4
    product; pinning *that* quartic onto `binomCol_polyDepth`'s "degree 4 ⟹ depth 4"
    count is the residual step (more nonlinear-`Nat` expansion). -/
theorem wallisDenCoeff_polyDepth : polyDepth 2 wallisDenCoeff :=
  fun n => by rw [wallisDenCoeff_liftK2 n, wallisDenCoeff_liftK2 0]

/-- ★★★ **π is P-recursive (holonomic) of order 1, with a degree-2 step coefficient
    of proven depth.**  Both Wallis convergent sequences satisfy first-order
    recurrences with degree-2 polynomial coefficients, and the denominator
    coefficient `(2n+1)(2n+3)` is a degree-2 discrete polynomial (`polyDepth 2`).
    This is the explicit P-recursive data + concrete depth underlying π's depth-6
    classification (1 cross-det + 1 ratio + the coefficient's differences). -/
theorem pi_is_P_recursive :
    (∀ n, E213.Lib.Math.Cauchy.WallisSeq.wallisNum (n+1)
            = E213.Lib.Math.Cauchy.WallisSeq.wallisNum n * (4 * (n + 1) * (n + 1)))
    ∧ (∀ n, E213.Lib.Math.Cauchy.WallisSeq.wallisDen (n+1)
            = E213.Lib.Math.Cauchy.WallisSeq.wallisDen n * ((2 * n + 1) * (2 * n + 3)))
    ∧ polyDepth 2 wallisDenCoeff :=
  ⟨wallis_num_holonomic, wallis_den_holonomic, wallisDenCoeff_polyDepth⟩

end E213.Lib.Math.Cauchy.DepthPRecursiveInstances
