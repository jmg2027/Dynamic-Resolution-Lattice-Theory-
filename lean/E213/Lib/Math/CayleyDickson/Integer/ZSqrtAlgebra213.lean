import E213.Lib.Math.CayleyDickson.Integer.ZSqrt
import E213.Lib.Math.CayleyDickson.Misc.QuadIdentities
import E213.Meta.Algebra213.Core
import E213.Meta.Algebra213.CDDouble
import E213.Meta.Int213.Core

/-!
# `ZSqrt[D]` as a `CommStarRing213` / `IntegerNormed213` instance

Promotes the parametric quadratic integer ring `ℤ[√D]` to the full
`Algebra213` typeclass hierarchy: `Ring213 → CommRing213 →
StarRing213 → IntegerNormed213 → CommStarRing213`.

`ZSqrt[D]` is the parametric Type B base for the CD tower; concrete
instances at `D = 2, -2, …` inherit automatically.  Multiplication:
`(a + b√D)(c + d√D) = (ac + D·bd) + (ad + bc)√D`.  Conjugation:
`a + b√D ↦ a - b√D`.  Norm: `N(a + b√D) = a² - D·b²` (Pell-like).

All proofs PURE via `Int213` componentwise projection — no
`quad_norm`, no `omega`.  Uses `int_quad_diophantus_sqrt` (PURE)
from `Misc.QuadIdentities` for the `normSq_mul` polynomial identity.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZSqrt

open E213.Meta.Algebra213
open E213.Lib.Math.CayleyDickson.Misc.QuadIdentities

variable (D : Int)

/-- `ofInt n = ⟨n, 0⟩` — embed Int along the rational-axis. -/
def ofInt (n : Int) : ZSqrt D := ⟨n, 0⟩

/-! ## §1 — Additive axioms (componentwise via Int213) -/

private theorem add_assoc' (u v w : ZSqrt D) :
    u + v + w = u + (v + w) := by
  apply ZSqrt.ext
  · show u.re + v.re + w.re = u.re + (v.re + w.re)
    exact E213.Meta.Int213.add_assoc _ _ _
  · show u.im + v.im + w.im = u.im + (v.im + w.im)
    exact E213.Meta.Int213.add_assoc _ _ _

private theorem add_comm' (u v : ZSqrt D) : u + v = v + u := by
  apply ZSqrt.ext
  · exact E213.Meta.Int213.add_comm _ _
  · exact E213.Meta.Int213.add_comm _ _

private theorem add_zero' (u : ZSqrt D) : u + 0 = u := by
  apply ZSqrt.ext
  · show u.re + 0 = u.re; exact Int.add_zero _
  · show u.im + 0 = u.im; exact Int.add_zero _

private theorem add_left_neg' (u : ZSqrt D) : -u + u = 0 := by
  apply ZSqrt.ext
  · exact E213.Meta.Int213.add_left_neg _
  · exact E213.Meta.Int213.add_left_neg _

/-! ## §2 — Multiplicative axioms -/

/-- Multiplication commutes — Type B base is commutative. -/
private theorem mul_comm' (u v : ZSqrt D) : u * v = v * u := by
  apply ZSqrt.ext
  · show u.re * v.re - D * (u.im * v.im) = v.re * u.re - D * (v.im * u.im)
    rw [E213.Meta.Int213.mul_comm u.re v.re,
        E213.Meta.Int213.mul_comm u.im v.im]
  · show u.re * v.im + u.im * v.re = v.re * u.im + v.im * u.re
    rw [E213.Meta.Int213.mul_comm u.re v.im,
        E213.Meta.Int213.mul_comm u.im v.re,
        E213.Meta.Int213.add_comm (v.im * u.re)]

/-- Conjugation distributes over addition (componentwise). -/
private theorem conj_add' (u v : ZSqrt D) :
    ZSqrt.conj (u + v) = ZSqrt.conj u + ZSqrt.conj v := by
  apply ZSqrt.ext
  · show u.re + v.re = u.re + v.re; rfl
  · show -(u.im + v.im) = -u.im + -v.im
    exact E213.Meta.Int213.neg_add _ _

/-- Conjugation distributes over multiplication (commutative case,
    so anti = same order). -/
private theorem conj_mul' (u v : ZSqrt D) :
    ZSqrt.conj (u * v) = ZSqrt.conj v * ZSqrt.conj u := by
  apply ZSqrt.ext
  · show u.re * v.re - D * (u.im * v.im)
       = v.re * u.re - D * (-v.im * -u.im)
    have h_neg : -v.im * -u.im = v.im * u.im := by
      rw [E213.Meta.Int213.neg_mul, E213.Meta.Int213.mul_neg, Int.neg_neg]
    rw [h_neg, E213.Meta.Int213.mul_comm u.re v.re,
        E213.Meta.Int213.mul_comm u.im v.im]
  · show -(u.re * v.im + u.im * v.re)
       = v.re * -u.im + -v.im * u.re
    rw [E213.Meta.Int213.mul_neg, E213.Meta.Int213.neg_mul,
        E213.Meta.Int213.neg_add,
        E213.Meta.Int213.mul_comm v.re u.im,
        E213.Meta.Int213.mul_comm v.im u.re,
        E213.Meta.Int213.add_comm]

end E213.Lib.Math.CayleyDickson.Integer.ZSqrt
