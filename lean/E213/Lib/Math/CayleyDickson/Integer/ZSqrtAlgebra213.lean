import E213.Lib.Math.CayleyDickson.Integer.ZSqrt
import E213.Lib.Math.CayleyDickson.Misc.QuadIdentities
import E213.Meta.Algebra213.Core
import E213.Meta.Algebra213.CDDouble
import E213.Meta.Algebra213.AlternativeNormed
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

/-! ## §3 — Ring axioms via Int213 polynomial AC normalization -/

/-- mul_assoc.re polynomial identity for ZSqrt[D].  AC `simp only`
    over PURE Int213 ring set. -/
private theorem int_zsqrt_mul_assoc_re (D a b c d e f : Int) :
    (a*c - D*(b*d))*e - D*((a*d + b*c)*f)
  = a*(c*e - D*(d*f)) - D*(b*(c*f + d*e)) := by
  simp only [Int.sub_eq_add_neg, E213.Meta.Int213.neg_mul,
             E213.Meta.Int213.mul_neg, Int.neg_neg,
             E213.Meta.Int213.neg_add,
             E213.Meta.Int213.add_mul, E213.Meta.Int213.mul_add,
             E213.Meta.Int213.mul_assoc, E213.Meta.Int213.mul_comm,
             E213.Meta.Int213.mul_left_comm,
             E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_comm,
             E213.Meta.Int213.add_left_comm,
             Int.add_zero, Int.zero_add]

/-- mul_assoc.im polynomial identity for ZSqrt[D]. -/
private theorem int_zsqrt_mul_assoc_im (D a b c d e f : Int) :
    (a*c - D*(b*d))*f + (a*d + b*c)*e
  = a*(c*f + d*e) + b*(c*e - D*(d*f)) := by
  simp only [Int.sub_eq_add_neg, E213.Meta.Int213.neg_mul,
             E213.Meta.Int213.mul_neg, Int.neg_neg,
             E213.Meta.Int213.neg_add,
             E213.Meta.Int213.add_mul, E213.Meta.Int213.mul_add,
             E213.Meta.Int213.mul_assoc, E213.Meta.Int213.mul_comm,
             E213.Meta.Int213.mul_left_comm,
             E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_comm,
             E213.Meta.Int213.add_left_comm,
             Int.add_zero, Int.zero_add]

private theorem mul_assoc' (u v w : ZSqrt D) :
    (u * v) * w = u * (v * w) := by
  apply ZSqrt.ext
  · show (u.re*v.re - D*(u.im*v.im))*w.re
         - D*((u.re*v.im + u.im*v.re)*w.im)
       = u.re*(v.re*w.re - D*(v.im*w.im))
         - D*(u.im*(v.re*w.im + v.im*w.re))
    exact int_zsqrt_mul_assoc_re D u.re u.im v.re v.im w.re w.im
  · show (u.re*v.re - D*(u.im*v.im))*w.im
         + (u.re*v.im + u.im*v.re)*w.re
       = u.re*(v.re*w.im + v.im*w.re)
         + u.im*(v.re*w.re - D*(v.im*w.im))
    exact int_zsqrt_mul_assoc_im D u.re u.im v.re v.im w.re w.im

/-- Right distributivity. -/
private theorem add_mul' (u v w : ZSqrt D) :
    (u + v) * w = u * w + v * w := by
  apply ZSqrt.ext
  · show (u.re + v.re)*w.re - D*((u.im + v.im)*w.im)
       = (u.re*w.re - D*(u.im*w.im)) + (v.re*w.re - D*(v.im*w.im))
    simp only [Int.sub_eq_add_neg, E213.Meta.Int213.neg_mul,
               E213.Meta.Int213.mul_neg, E213.Meta.Int213.neg_add,
               E213.Meta.Int213.add_mul, E213.Meta.Int213.mul_add,
               E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_comm,
               E213.Meta.Int213.add_left_comm]
  · show (u.re + v.re)*w.im + (u.im + v.im)*w.re
       = (u.re*w.im + u.im*w.re) + (v.re*w.im + v.im*w.re)
    simp only [E213.Meta.Int213.add_mul,
               E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_comm,
               E213.Meta.Int213.add_left_comm]

/-- Left distributivity (= add_mul via mul_comm, but proven directly). -/
private theorem mul_add' (u v w : ZSqrt D) :
    u * (v + w) = u * v + u * w := by
  apply ZSqrt.ext
  · show u.re*(v.re + w.re) - D*(u.im*(v.im + w.im))
       = (u.re*v.re - D*(u.im*v.im)) + (u.re*w.re - D*(u.im*w.im))
    simp only [Int.sub_eq_add_neg, E213.Meta.Int213.neg_mul,
               E213.Meta.Int213.mul_neg, E213.Meta.Int213.neg_add,
               E213.Meta.Int213.add_mul, E213.Meta.Int213.mul_add,
               E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_comm,
               E213.Meta.Int213.add_left_comm]
  · show u.re*(v.im + w.im) + u.im*(v.re + w.re)
       = (u.re*v.im + u.im*v.re) + (u.re*w.im + u.im*w.re)
    simp only [E213.Meta.Int213.mul_add,
               E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_comm,
               E213.Meta.Int213.add_left_comm]

/-! ## §4 — ofInt + self_mul_conj -/

private theorem ofInt_add' (a b : Int) :
    ofInt D a + ofInt D b = ofInt D (a + b) := by
  apply ZSqrt.ext
  · show a + b = a + b; rfl
  · show (0 : Int) + 0 = 0; rfl

private theorem ofInt_mul' (a b : Int) :
    ofInt D a * ofInt D b = ofInt D (a * b) := by
  apply ZSqrt.ext
  · show a * b - D * (0 * 0) = a * b
    rw [Int.zero_mul, Int.mul_zero]
    exact Int.sub_zero _
  · show a * 0 + 0 * b = 0
    rw [Int.mul_zero, Int.zero_mul]
    rfl

private theorem ofInt_central' (z : Int) (a : ZSqrt D) :
    ofInt D z * a = a * ofInt D z := by
  apply ZSqrt.ext
  · show z*a.re - D*(0*a.im) = a.re*z - D*(a.im*0)
    rw [Int.zero_mul a.im, Int.mul_zero a.im, Int.mul_zero D,
        E213.Meta.Int213.mul_comm z a.re]
  · show z*a.im + 0*a.re = a.re*0 + a.im*z
    rw [Int.zero_mul, Int.mul_zero,
        Int.add_zero, Int.zero_add]
    exact E213.Meta.Int213.mul_comm z a.im

private theorem ofInt_inj' {a b : Int} (h : ofInt D a = ofInt D b) : a = b := by
  have h_re : (ofInt D a).re = (ofInt D b).re := congrArg ZSqrt.re h
  exact h_re

/-- `u * conj u = ofInt (normSq u)` for ZSqrt[D].  Direct via expansion. -/
private theorem self_mul_conj' (u : ZSqrt D) :
    u * ZSqrt.conj u = ofInt D u.normSq := by
  apply ZSqrt.ext
  · show u.re * u.re - D * (u.im * -u.im)
       = u.re * u.re + D * (u.im * u.im)
    rw [E213.Meta.Int213.mul_neg u.im u.im,
        E213.Meta.Int213.mul_neg D (u.im * u.im),
        show ∀ x y : Int, x - -y = x + y from fun x y => by
          show x + -(-y) = x + y; rw [Int.neg_neg]]
  · show u.re * -u.im + u.im * u.re = 0
    rw [E213.Meta.Int213.mul_neg u.re u.im,
        E213.Meta.Int213.mul_comm u.im u.re,
        E213.Meta.Int213.add_comm (-(u.re * u.im)) (u.re * u.im)]
    exact E213.Meta.Int213.add_neg_cancel _

/-! ## §5 — Typeclass instance registration -/

/-- ZSqrt[D] `Ring213` instance — all axioms PURE via Int213
    projection (plus the int_zsqrt_mul_assoc helpers). -/
instance : Ring213 (ZSqrt D) where
  add_assoc    := add_assoc' D
  add_comm     := add_comm' D
  add_zero     := add_zero' D
  add_left_neg := add_left_neg' D
  mul_assoc    := mul_assoc' D
  add_mul      := add_mul' D
  mul_add      := mul_add' D

/-- ZSqrt[D] `CommRing213` — multiplication commutes. -/
instance : CommRing213 (ZSqrt D) where
  mul_comm := mul_comm' D

/-- ZSqrt[D] `StarRing213`.  Conjugation `a + b√D ↦ a − b√D` —
    anti-distributive (= same-order via mul_comm in this commutative
    case). -/
instance : StarRing213 (ZSqrt D) where
  conj      := ZSqrt.conj
  conj_conj := ZSqrt.conj_conj
  conj_add  := conj_add' D
  conj_mul  := conj_mul' D

/-- ZSqrt[D] `IntegerNormed213`.  norm `N(a + b√D) = a² + D·b²`
    (sign convention follows the ZSqrt struct's `normSq`). -/
instance : IntegerNormed213 (ZSqrt D) where
  ofInt         := ofInt D
  normSq        := ZSqrt.normSq
  self_mul_conj := self_mul_conj' D
  ofInt_mul     := ofInt_mul' D
  ofInt_add     := ofInt_add' D
  ofInt_central := ofInt_central' D
  ofInt_inj     := ofInt_inj' D

/-- ZSqrt[D] `CommStarRing213` bundle. -/
instance : CommStarRing213 (ZSqrt D) where
  conj      := ZSqrt.conj
  conj_conj := ZSqrt.conj_conj
  conj_add  := conj_add' D
  conj_mul  := conj_mul' D

/-! ## §6 — MoufangIntegerNormed213 (trivial at commutative base) -/

private theorem zsqrt_moufang_norm (u v : ZSqrt D) :
    (u * v) * (ZSqrt.conj v * ZSqrt.conj u)
      = u * (v * ZSqrt.conj v) * ZSqrt.conj u := by
  rw [← Ring213.mul_assoc (u * v) (ZSqrt.conj v) (ZSqrt.conj u),
      Ring213.mul_assoc u v (ZSqrt.conj v)]

private theorem zsqrt_ofInt_paren_central (z : Int) (u : ZSqrt D) :
    u * ofInt D z * ZSqrt.conj u
      = ofInt D z * (u * ZSqrt.conj u) := by
  rw [show u * ofInt D z = ofInt D z * u from
        (@IntegerNormed213.ofInt_central (ZSqrt D) _ z u).symm,
      Ring213.mul_assoc (ofInt D z) u (ZSqrt.conj u)]

/-- ★ ZSqrt[D] MoufangIntegerNormed213.  Trivial Moufang via
    mul_assoc (commutative base is associative). -/
instance : MoufangIntegerNormed213 (ZSqrt D) where
  ofInt               := ofInt D
  normSq              := ZSqrt.normSq
  self_mul_conj       := self_mul_conj' D
  ofInt_mul           := ofInt_mul' D
  ofInt_central       := ofInt_central' D
  ofInt_inj           := ofInt_inj' D
  moufang_norm        := zsqrt_moufang_norm D
  ofInt_paren_central := zsqrt_ofInt_paren_central D

/-- ★ ZSqrt[D] normSq_mul via MoufangIntegerNormed213 generic. -/
theorem moufang_normSq_mul (u v : ZSqrt D) :
    (u * v).normSq = u.normSq * v.normSq :=
  MoufangIntegerNormed213.normSq_mul u v

end E213.Lib.Math.CayleyDickson.Integer.ZSqrt
