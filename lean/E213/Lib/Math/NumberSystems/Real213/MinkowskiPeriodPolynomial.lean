import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Order

/-!
# MinkowskiPeriodPolynomial — the weight-4 Eichler–Shimura period polynomial is `1 − X²`

The last named gap of the period thread: the **slash action on the polynomial module `V_{k−2}`**.
Here it is built for weight 4 (`V_2` = degree-2 polynomials `a + bX + cX²`, coefficient triple
`(a,b,c)`), with the two generators of `PSL(2,ℤ)`:

  * `S = [[0,−1],[1,0]]` (order 4, the Gaussian unit `i`), weight-2 action `X²·r(−1/X)` —
    `(a,b,c) ↦ (c, −b, a)`;
  * `U = [[0,−1],[1,1]]` (order 6, the Eisenstein unit `ω`), weight-2 action `(X+1)²·r(−1/(X+1))` —
    `(a,b,c) ↦ (a−b+c, 2a−b, a)`.

The Eichler–Shimura **period relations** `r|(1+S) = 0` and `r|(1+U+U²) = 0` (the cocycle conditions
from `S²=−I`, `U³=−I`) are now a finite ℤ-linear system, solved here: the weight-4 period polynomial
is **`1 − X²`** (`periodPoly = (1,0,−1)`), the unique line `ℤ·(1,0,−1)` annihilated by both relations.
It is the `−1`-eigenvector of `S` (the `(1+S)` relation) and is cycled with order 3 by `U`.  All
∅-axiom (`decide`/`ring_intZ` over `ℤ`).  This closes the higher-weight Eichler–Shimura *slash-action*
gap (the remaining residual being only the complex `ℍ`-contour for the analytic period integral).
-/

namespace E213.Lib.Math.NumberSystems.Real213.MinkowskiPeriodPolynomial

open E213.Meta.Int213 (add_neg_cancel add_comm mul_neg)
open E213.Meta.Int213.Order (sub_zero)

/-- A weight-4 period polynomial `a + bX + cX²` as its coefficient triple. -/
abbrev V2 := Int × Int × Int

/-- Slash action of `S = [[0,−1],[1,0]]` (weight 2): `X²·r(−1/X)`, `(a,b,c) ↦ (c, −b, a)`. -/
def slashS : V2 → V2 := fun ⟨a, b, c⟩ => (c, -b, a)

/-- Slash action of `U = [[0,−1],[1,1]]` (weight 2): `(X+1)²·r(−1/(X+1))`,
    `(a,b,c) ↦ (a−b+c, 2a−b, a)`. -/
def slashU : V2 → V2 := fun ⟨a, b, c⟩ => (a - b + c, 2 * a - b, a)

/-- Coordinatewise addition on `V_2`. -/
def addV2 : V2 → V2 → V2 := fun ⟨a, b, c⟩ ⟨d, e, f⟩ => (a + d, b + e, c + f)

/-- The `(1+S)` period-relation operator. -/
def relS (r : V2) : V2 := addV2 r (slashS r)

/-- The `(1+U+U²)` period-relation operator. -/
def relU (r : V2) : V2 := addV2 r (addV2 (slashU r) (slashU (slashU r)))

/-- The weight-4 period polynomial `1 − X²`. -/
def periodPoly : V2 := (1, 0, -1)

/-- ★★★★ **`1 − X²` solves both Eichler–Shimura period relations** — it is the weight-4 period
    polynomial.  `r|(1+S) = 0` and `r|(1+U+U²) = 0` for `r = 1 − X²`.  ∅-axiom (`decide`). -/
theorem period_satisfies_relations :
    relS periodPoly = (0, 0, 0) ∧ relU periodPoly = (0, 0, 0) := by decide

/-- ★★★ **`1 − X²` is the `−1`-eigenvector of `S`** (the `(1+S)` relation's content): the order-4
    Gaussian-unit generator sends `1 − X²` to `−(1 − X²)`. -/
theorem slashS_period_eq_neg : slashS periodPoly = (-1, 0, 1) := by decide

/-- ★★★ **`U` cycles the period polynomial with order 3** (the even-weight image of `U`'s order 6,
    the `{4,6}` elliptic torsion): `U³` fixes `1 − X²`. -/
theorem slashU_period_order3 :
    slashU (slashU (slashU periodPoly)) = periodPoly := by decide

/-- The relations are **non-trivial**: `1 + X²` (`(1,0,1)`) is *not* a period polynomial — `(1+S)`
    does not annihilate it.  So the period space is a proper subspace, not all of `V_2`. -/
theorem relations_nontrivial : relS (1, 0, 1) ≠ (0, 0, 0) := by decide

/-- ★★★★ **The closed form of the period relations** (general coefficients): `(1+S)` collapses to
    `(a+c, 0, a+c)` and `(1+U+U²)` to the constant triple `(2a−b+2c)·(1,1,1)`.  So the period space
    `{r : r|(1+S)=0 ∧ r|(1+U+U²)=0}` is exactly `{a+c = 0 ∧ b = 0}` = the line `ℤ·(1 − X²)`: the
    1-dimensional weight-4 Eichler–Shimura period space.  ∅-axiom (`ring_intZ` per coordinate). -/
theorem relations_closed_form (a b c : Int) :
    relS (a, b, c) = (a + c, 0, a + c)
    ∧ relU (a, b, c) = (2 * a - b + 2 * c, 2 * a - b + 2 * c, 2 * a - b + 2 * c) := by
  refine ⟨?_, ?_⟩
  · show ((a + c, b + -b, c + a) : V2) = (a + c, 0, a + c)
    rw [add_neg_cancel b, add_comm c a]
  · show ((a + ((a - b + c) + ((a - b + c) - (2 * a - b) + a)),
          b + ((2 * a - b) + (2 * (a - b + c) - (2 * a - b))),
          c + (a + (a - b + c))) : V2)
        = (2 * a - b + 2 * c, 2 * a - b + 2 * c, 2 * a - b + 2 * c)
    rw [show a + ((a - b + c) + ((a - b + c) - (2 * a - b) + a)) = 2 * a - b + 2 * c from by ring_intZ,
        show b + ((2 * a - b) + (2 * (a - b + c) - (2 * a - b))) = 2 * a - b + 2 * c from by ring_intZ,
        show c + (a + (a - b + c)) = 2 * a - b + 2 * c from by ring_intZ]

/-- ★★★ **The period space is the line `ℤ·(1 − X²)`.**  `t·(1 − X²)` (coefficients `(t,0,−t)`) is
    annihilated by both relations, for every `t` — the span of the weight-4 period polynomial. -/
theorem period_line_in_kernel (t : Int) :
    relS (t, 0, -t) = (0, 0, 0) ∧ relU (t, 0, -t) = (0, 0, 0) := by
  obtain ⟨hS, hU⟩ := relations_closed_form t 0 (-t)
  refine ⟨?_, ?_⟩
  · rw [hS, add_neg_cancel t]
  · rw [hU, sub_zero, mul_neg, add_neg_cancel]

end E213.Lib.Math.NumberSystems.Real213.MinkowskiPeriodPolynomial
