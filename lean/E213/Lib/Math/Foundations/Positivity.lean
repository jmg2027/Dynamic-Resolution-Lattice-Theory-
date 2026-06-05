import E213.Meta.Int213.Core
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order
import E213.Meta.Int213.PolyIntMTactic

/-!
# A7 POSITIVITY — a nonnegative fold forces a bound (∅-axiom)

The seventh proof-ISA lift archetype, the **structural twin of A5 COUNT**.

A5 COUNT is the *cardinality* face of `GAP`: a deficit (`Σ|badᵢ| < |codomain|`)
forces existence.  POSITIVITY is its **norm/square face**: a quantity is forced
`≥ 0` (or a bound is forced) because it is the `READ` of an intrinsically
**nonnegative** structure — a *square*, a dimension, a norm.  The bound is not
counted; it is read off the *sign* of a fold.

Classical conquests this is the shadow of:
  · **Weil RH** — Frobenius weights bounded by cohomology positivity (hard Lefschetz);
  · **Kazhdan–Lusztig positivity** — a coefficient `≥ 0` because it is an IH stalk *dimension*;
  · **Mordell / Faltings** — finiteness from a nonnegative *height* (Northcott).

## The archetype, and the conquest it drives

`positivity_of_sq`: when a bound's **gap equals a square**, the bound holds —
`gap = s² ⟹ 0 ≤ gap`.  The conquest it drives: **Cauchy–Schwarz**.  Cauchy–Schwarz
*is* positivity: its gap is exactly a square (the Lagrange identity), so
`⟨u,v⟩² ≤ ⟨u,u⟩⟨v,v⟩` is forced with no analysis — `cauchy_schwarz_2d`, the gap
`(u₀v₁ − u₁v₀)²`.

Over `ℤ` scalars (the clean ring for the square; `ring_intZ` discharges the
Lagrange identity and `int_sq_nonneg` its sign).  The `n`-dimensional Lagrange
identity (gap `= Σᵢ<ⱼ (uᵢvⱼ − uⱼvᵢ)²`) extends this; the 2-D case is the atom.

**Lift cost: an algebraic identity exhibiting the gap as a sum of squares.**
-/

namespace E213.Lib.Math.Foundations.Positivity

open E213.Meta.Int213

/-- ★★★★★ **A7 POSITIVITY archetype.**  If a bound's gap equals a square (a
    nonnegative fold), the bound is forced.  `gap = s² ⟹ 0 ≤ gap`. -/
theorem positivity_of_sq (gap s : Int) (h : gap = s * s) : 0 ≤ gap := by
  rw [h]; exact int_sq_nonneg s

/-- **Lagrange identity (2-D)**: the Cauchy–Schwarz gap is a single square. -/
theorem lagrange_2d (a0 a1 b0 b1 : Int) :
    (a0 * a0 + a1 * a1) * (b0 * b0 + b1 * b1)
      - (a0 * b0 + a1 * b1) * (a0 * b0 + a1 * b1)
    = (a0 * b1 - a1 * b0) * (a0 * b1 - a1 * b0) := by
  ring_intZ

/-- ★★★★★★ **Cauchy–Schwarz (2-D, ℤ) via POSITIVITY.**
    `⟨u,v⟩² ≤ ⟨u,u⟩·⟨v,v⟩` — forced because the gap is the square
    `(u₀v₁ − u₁v₀)² ≥ 0`.  The POSITIVITY archetype driving an actual
    inner-product conquest, no analysis used. -/
theorem cauchy_schwarz_2d (a0 a1 b0 b1 : Int) :
    (a0 * b0 + a1 * b1) * (a0 * b0 + a1 * b1)
    ≤ (a0 * a0 + a1 * a1) * (b0 * b0 + b1 * b1) := by
  have hgap : (a0 * a0 + a1 * a1) * (b0 * b0 + b1 * b1)
                - (a0 * b0 + a1 * b1) * (a0 * b0 + a1 * b1)
              = (a0 * b1 - a1 * b0) * (a0 * b1 - a1 * b0) := lagrange_2d a0 a1 b0 b1
  have hpos : 0 ≤ (a0 * a0 + a1 * a1) * (b0 * b0 + b1 * b1)
                    - (a0 * b0 + a1 * b1) * (a0 * b0 + a1 * b1) :=
    positivity_of_sq _ _ hgap
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hpos)

/-- **A7 POSITIVITY (sum-of-three-squares form)**: a bound forced because its gap
    is a sum of three squares. -/
theorem positivity_of_sq3 (gap s t u : Int) (h : gap = s * s + t * t + u * u) :
    0 ≤ gap := by
  rw [h]
  exact add_nonneg (add_nonneg (int_sq_nonneg s) (int_sq_nonneg t)) (int_sq_nonneg u)

/-- ★★★★★ **AM–GM (2-variable, ℤ) via POSITIVITY**: `4ab ≤ (a+b)²`, forced
    because the gap is the square `(a−b)²`. -/
theorem amgm_2 (a b : Int) : 4 * (a * b) ≤ (a + b) * (a + b) := by
  have hgap : (a + b) * (a + b) - 4 * (a * b) = (a - b) * (a - b) := by ring_intZ
  have hpos : 0 ≤ (a + b) * (a + b) - 4 * (a * b) := positivity_of_sq _ _ hgap
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hpos)

/-- **Lagrange identity (3-D)**: the Cauchy–Schwarz gap is a sum of three
    squares. -/
theorem lagrange_3d (a0 a1 a2 b0 b1 b2 : Int) :
    (a0 * a0 + a1 * a1 + a2 * a2) * (b0 * b0 + b1 * b1 + b2 * b2)
      - (a0 * b0 + a1 * b1 + a2 * b2) * (a0 * b0 + a1 * b1 + a2 * b2)
    = (a0 * b1 - a1 * b0) * (a0 * b1 - a1 * b0)
      + (a0 * b2 - a2 * b0) * (a0 * b2 - a2 * b0)
      + (a1 * b2 - a2 * b1) * (a1 * b2 - a2 * b1) := by
  ring_intZ

/-- ★★★★★★ **Cauchy–Schwarz (3-D, ℤ) via POSITIVITY**: `⟨u,v⟩² ≤ ⟨u,u⟩⟨v,v⟩`,
    forced because the gap is the sum of three squares (the 3-D Lagrange
    identity). -/
theorem cauchy_schwarz_3d (a0 a1 a2 b0 b1 b2 : Int) :
    (a0 * b0 + a1 * b1 + a2 * b2) * (a0 * b0 + a1 * b1 + a2 * b2)
    ≤ (a0 * a0 + a1 * a1 + a2 * a2) * (b0 * b0 + b1 * b1 + b2 * b2) := by
  have hpos : 0 ≤ (a0 * a0 + a1 * a1 + a2 * a2) * (b0 * b0 + b1 * b1 + b2 * b2)
                    - (a0 * b0 + a1 * b1 + a2 * b2) * (a0 * b0 + a1 * b1 + a2 * b2) :=
    positivity_of_sq3 _ _ _ _ (lagrange_3d a0 a1 a2 b0 b1 b2)
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hpos)

/-! ## POSITIVITY's rigidity face — a vanishing nonnegative fold forces vanishing

The same nonnegativity that forces a *bound* (above) forces, at the extreme
`= 0`, **rigidity**: a sum of squares is `0` only when every term is.  This is
positive-*definiteness* of the coordinate form `⟨v,v⟩ = Σ vᵢ²` (the condition
`⟨v,v⟩ = 0 ⟹ v = 0`), proven for the concrete form. -/

/-- `a² = 0 ⟹ a = 0`. -/
theorem sq_eq_zero {a : Int} (h : a * a = 0) : a = 0 :=
  (mul_eq_zero h).elim id id

/-- ★★★★★ **POSITIVITY rigidity (2-D)** = positive-definiteness: `a²+b² = 0`
    forces `a = b = 0`. -/
theorem positive_definite_2 (a b : Int) (h : a * a + b * b = 0) :
    a = 0 ∧ b = 0 :=
  let hpair := add_eq_zero_of_nonneg (int_sq_nonneg a) (int_sq_nonneg b) h
  ⟨sq_eq_zero hpair.1, sq_eq_zero hpair.2⟩

/-- ★★★★★ **POSITIVITY rigidity (3-D)**: `a²+b²+c² = 0` forces `a = b = c = 0`. -/
theorem positive_definite_3 (a b c : Int) (h : a * a + b * b + c * c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 :=
  let hpair := add_eq_zero_of_nonneg
    (add_nonneg (int_sq_nonneg a) (int_sq_nonneg b)) (int_sq_nonneg c) h
  let hab := positive_definite_2 a b hpair.1
  ⟨hab.1, hab.2, sq_eq_zero hpair.2⟩

end E213.Lib.Math.Foundations.Positivity
