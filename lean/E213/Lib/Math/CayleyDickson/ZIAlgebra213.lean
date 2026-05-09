import E213.Lib.Math.CayleyDickson.ZI
import E213.Lib.Math.CayleyDickson.ZIArith
import E213.Lib.Math.CayleyDickson.ZIDomain
import E213.Lib.Math.CayleyDickson.ZIHom
import E213.Theory.Internal.Algebra213
import E213.Theory.Internal.Int213

/-!
# `ZI` as an `IntegerNormed213` instance

Provides ZI's instance of the `Ring213 → CommRing213 → StarRing213 →
IntegerNormed213` hierarchy.  The generic `normSq_mul` theorem at
`IntegerNormed213` level then derives `ZI`'s norm-multiplicativity
automatically without polynomial expansion.

Each ring axiom reduces componentwise to `Int213.*`.
-/

namespace E213.Lib.Math.CayleyDickson.ZI.ZI

open E213.Theory.Internal.Algebra213

/-- `ofInt n = ⟨n, 0⟩` — embed Int into ZI as the real axis. -/
def ofInt (n : Int) : ZI := ⟨n, 0⟩

/-- ∅-axiom componentwise add_assoc. -/
private theorem add_assoc' (u v w : ZI) : u + v + w = u + (v + w) := by
  apply ext
  · show u.re + v.re + w.re = u.re + (v.re + w.re)
    exact E213.Theory.Internal.Int213.add_assoc _ _ _
  · show u.im + v.im + w.im = u.im + (v.im + w.im)
    exact E213.Theory.Internal.Int213.add_assoc _ _ _

private theorem add_left_neg' (u : ZI) : -u + u = 0 := by
  apply ext
  · show -u.re + u.re = 0
    exact E213.Theory.Internal.Int213.add_left_neg _
  · show -u.im + u.im = 0
    exact E213.Theory.Internal.Int213.add_left_neg _

/-- ∅-axiom Int helper: `A + X + (Y + Z) = A + Y + (X + Z)` —
    swap middle two terms in a 4-term sum. -/
private theorem add_4_swap_mid (A X Y Z : Int) :
    A + X + (Y + Z) = A + Y + (X + Z) := by
  rw [E213.Theory.Internal.Int213.add_assoc A X (Y + Z),
      E213.Theory.Internal.Int213.add_left_comm X Y Z,
      ← E213.Theory.Internal.Int213.add_assoc A Y (X + Z)]

/-- ∅-axiom Int helper: `(A+C) - (B+D) = A - B + (C - D)`, used
    for the re-component of ZI add_mul. -/
private theorem int_helper_re (A B C D : Int) :
    (A + C) - (B + D) = A - B + (C - D) := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg,
      E213.Theory.Internal.Int213.neg_add]
  exact add_4_swap_mid A C (-B) (-D)

/-- ∅-axiom Int helper: `A + C + (B + D) = A + B + (C + D)`. -/
private theorem int_helper_im (A B C D : Int) :
    A + C + (B + D) = A + B + (C + D) :=
  add_4_swap_mid A C B D

private theorem add_mul' (u v w : ZI) : (u + v) * w = u * w + v * w := by
  apply ext
  · show (u.re + v.re) * w.re - (u.im + v.im) * w.im
       = u.re * w.re - u.im * w.im + (v.re * w.re - v.im * w.im)
    rw [E213.Theory.Internal.Int213.add_mul, E213.Theory.Internal.Int213.add_mul]
    exact int_helper_re _ _ _ _
  · show (u.re + v.re) * w.im + (u.im + v.im) * w.re
       = u.re * w.im + u.im * w.re + (v.re * w.im + v.im * w.re)
    rw [E213.Theory.Internal.Int213.add_mul, E213.Theory.Internal.Int213.add_mul]
    exact int_helper_im _ _ _ _

private theorem mul_add' (u v w : ZI) : u * (v + w) = u * v + u * w := by
  rw [mul_comm, add_mul', mul_comm v u, mul_comm w u]

/-- Anti-distributive form needed by StarRing213: `conj(uv) = conj v · conj u`.
    Since ZI is commutative, derive from same-order `conj_mul` + `mul_comm`. -/
private theorem conj_mul_anti (u v : ZI) :
    conj (u * v) = conj v * conj u := by
  rw [conj_mul, mul_comm]

private theorem self_mul_conj' (u : ZI) : u * conj u = ofInt u.normSq := by
  apply ext
  · show u.re * u.re - u.im * (-u.im) = u.re * u.re + u.im * u.im
    rw [E213.Theory.Internal.Int213.mul_neg, Int.sub_eq_add_neg, Int.neg_neg]
  · show u.re * (-u.im) + u.im * u.re = 0
    rw [E213.Theory.Internal.Int213.mul_neg, E213.Theory.Internal.Int213.mul_comm u.im u.re]
    exact E213.Theory.Internal.Int213.add_left_neg _

private theorem ofInt_mul' (a b : Int) : ofInt a * ofInt b = ofInt (a * b) := by
  apply ext
  · show a * b - 0 * 0 = a * b
    rw [Int.mul_zero, Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero]
  · show a * 0 + 0 * b = 0
    rw [Int.mul_zero, E213.Theory.Internal.Int213.zero_mul, Int.add_zero]

private theorem ofInt_central' (z : Int) (a : ZI) :
    ofInt z * a = a * ofInt z := by
  apply ext
  · show z * a.re - 0 * a.im = a.re * z - a.im * 0
    rw [Int.mul_zero, E213.Theory.Internal.Int213.zero_mul, E213.Theory.Internal.Int213.mul_comm z a.re]
  · show z * a.im + 0 * a.re = a.re * 0 + a.im * z
    rw [Int.mul_zero, E213.Theory.Internal.Int213.zero_mul, E213.Theory.Internal.Int213.mul_comm z a.im, E213.Theory.Internal.Int213.add_comm]

private theorem ofInt_inj' {a b : Int} (h : ofInt a = ofInt b) : a = b := by
  have h_re : a = b := congrArg ZI.re h
  exact h_re

instance : Ring213 ZI where
  add_assoc    := add_assoc'
  add_comm     := add_comm
  add_zero     := add_zero
  add_left_neg := add_left_neg'
  mul_assoc    := mul_assoc
  add_mul      := add_mul'
  mul_add      := mul_add'

instance : CommRing213 ZI where
  mul_comm := mul_comm

instance : StarRing213 ZI where
  conj      := conj
  conj_conj := conj_conj
  conj_add  := conj_add
  conj_mul  := conj_mul_anti

instance : IntegerNormed213 ZI where
  ofInt         := ofInt
  normSq        := normSq
  self_mul_conj := self_mul_conj'
  ofInt_mul     := ofInt_mul'
  ofInt_central := ofInt_central'
  ofInt_inj     := ofInt_inj'

end E213.Lib.Math.CayleyDickson.ZI.ZI
