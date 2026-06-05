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

end E213.Lib.Math.Foundations.Positivity
