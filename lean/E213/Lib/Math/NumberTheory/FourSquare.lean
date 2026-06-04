import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.OrderMul

/-!
# FourSquare — Lagrange's four-square theorem via Euler descent (Pillar II)

The descent route to `∀ n, n = a²+b²+c²+d²`, staying entirely over `ℤ` with ring identities and
`centered_div_int` — sidestepping the non-commutative Hurwitz-quaternion gcd.

  * ★★★ `four_sq_id` — **Euler's four-square identity** (multiplicativity, a ring identity).
  * `isSum4` / `isSum4_mul` — "is a sum of four squares" is closed under multiplication.

(The descent step `m·p = Σ4², 1 < m < p ⟹ ∃ r < m, r·p = Σ4²` and the assembly to all `n`
build on these — see `research-notes/frontiers/four_square_marathon.md`.)

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FourSquare

open E213.Meta.Int213.OrderMul (int_sign mul_pos int_lt_irrefl)
open E213.Meta.Int213.Order
  (le_antisymm le_of_sub_nonneg nonneg_of_le_zero sub_pos_of_lt lt_of_sub_pos zero_sub sub_self_zero)
open E213.Meta.Int213 (mul_neg zero_add)

/-! ## §0 — pure `ℤ` positive-multiplication cancellation -/

/-- `¬ a < b ⟹ b ≤ a` (pure, via `int_sign`). -/
theorem le_of_not_lt {a b : Int} (h : ¬ a < b) : b ≤ a := by
  rcases int_sign (a - b) with hge | hlt
  · exact le_of_sub_nonneg (nonneg_of_le_zero hge)
  · have hba : (0 : Int) < b - a := by
      have hx := sub_pos_of_lt hlt
      rw [zero_sub, show -(a - b) = b - a from by ring_intZ] at hx; exact hx
    exact absurd (lt_of_sub_pos hba) h

/-- `0 < c`, `c·d = 0 ⟹ d = 0` (no zero divisors, pure). -/
theorem eq_zero_of_mul_pos {c d : Int} (hc : 0 < c) (h : c * d = 0) : d = 0 := by
  rcases int_sign d with hd | hd
  · exact le_antisymm (le_of_not_lt (fun hp => int_lt_irrefl 0 (h ▸ mul_pos hc hp))) hd
  · exfalso
    have h2 : 0 < c * (-d) := mul_pos hc (by have hx := sub_pos_of_lt hd; rwa [zero_sub] at hx)
    rw [mul_neg, h] at h2; exact int_lt_irrefl 0 h2

/-- `0 < c`, `c·a = c·b ⟹ a = b` (pure positive-mul left-cancellation). -/
theorem mul_left_cancel_pos {c a b : Int} (hc : 0 < c) (h : c * a = c * b) : a = b := by
  have h0 : c * (a - b) = 0 := by
    rw [show c * (a - b) = c * a - c * b from by ring_intZ, h]; exact sub_self_zero _
  have hab : a - b = 0 := eq_zero_of_mul_pos hc h0
  have key : (a - b) + b = 0 + b := by rw [hab]
  rw [show (a - b) + b = a from by ring_intZ, zero_add] at key; exact key

/-- ★★★ **Euler's four-square identity.**  The product of two sums of four squares is a sum of
    four squares — the bilinear combination is the quaternion-norm multiplicativity, here a bare
    `ℤ` polynomial identity. -/
theorem four_sq_id (a1 a2 a3 a4 b1 b2 b3 b4 : Int) :
    (a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4) * (b1 * b1 + b2 * b2 + b3 * b3 + b4 * b4)
    = (a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4) * (a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4)
    + (a1 * b2 - a2 * b1 + a3 * b4 - a4 * b3) * (a1 * b2 - a2 * b1 + a3 * b4 - a4 * b3)
    + (a1 * b3 - a2 * b4 - a3 * b1 + a4 * b2) * (a1 * b3 - a2 * b4 - a3 * b1 + a4 * b2)
    + (a1 * b4 + a2 * b3 - a3 * b2 - a4 * b1) * (a1 * b4 + a2 * b3 - a3 * b2 - a4 * b1) := by
  ring_intZ

/-- `n` is a sum of four integer squares. -/
def isSum4 (n : Int) : Prop := ∃ a b c d : Int, n = a * a + b * b + c * c + d * d

/-- **Sum-of-four-squares is multiplicative** (Euler): `isSum4 m`, `isSum4 n` ⟹ `isSum4 (m·n)`. -/
theorem isSum4_mul {m n : Int} (hm : isSum4 m) (hn : isSum4 n) : isSum4 (m * n) := by
  obtain ⟨a1, a2, a3, a4, hm⟩ := hm
  obtain ⟨b1, b2, b3, b4, hn⟩ := hn
  refine ⟨a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4, a1 * b2 - a2 * b1 + a3 * b4 - a4 * b3,
    a1 * b3 - a2 * b4 - a3 * b1 + a4 * b2, a1 * b4 + a2 * b3 - a3 * b2 - a4 * b1, ?_⟩
  rw [hm, hn]; exact four_sq_id a1 a2 a3 a4 b1 b2 b3 b4

/-! ## §2 — the descent step (algebraic heart) -/

/-- ★★★★ **The Lagrange descent core.**  Given `m·p = Σaᵢ²`, centred residues `aᵢ = qᵢ·m + Aᵢ`,
    and `m·r = ΣAᵢ²`, the product `(m·p)(m·r) = Σcⱼ²` (Euler) has each `cⱼ` divisible by `m`, so
    dividing by `m²` gives `p·r = Σdⱼ²` — the smaller multiple `r·p` of `p` is again a sum of
    four squares. -/
theorem descent_core (m p r a1 a2 a3 a4 q1 q2 q3 q4 A1 A2 A3 A4 : Int) (hm : 0 < m)
    (hqa1 : a1 = q1 * m + A1) (hqa2 : a2 = q2 * m + A2) (hqa3 : a3 = q3 * m + A3)
    (hqa4 : a4 = q4 * m + A4)
    (hmp : a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4 = m * p)
    (hmr : A1 * A1 + A2 * A2 + A3 * A3 + A4 * A4 = m * r) :
    ∃ d1 d2 d3 d4 : Int, p * r = d1 * d1 + d2 * d2 + d3 * d3 + d4 * d4 := by
  refine ⟨q1 * A1 + q2 * A2 + q3 * A3 + q4 * A4 + r, q1 * A2 - q2 * A1 + q3 * A4 - q4 * A3,
    q1 * A3 - q2 * A4 - q3 * A1 + q4 * A2, q1 * A4 + q2 * A3 - q3 * A2 - q4 * A1, ?_⟩
  have hc1 : a1 * A1 + a2 * A2 + a3 * A3 + a4 * A4
      = m * (q1 * A1 + q2 * A2 + q3 * A3 + q4 * A4 + r) := by
    rw [hqa1, hqa2, hqa3, hqa4]
    have e : (q1 * m + A1) * A1 + (q2 * m + A2) * A2 + (q3 * m + A3) * A3 + (q4 * m + A4) * A4
        = m * (q1 * A1 + q2 * A2 + q3 * A3 + q4 * A4) + (A1 * A1 + A2 * A2 + A3 * A3 + A4 * A4) := by
      ring_intZ
    rw [e, hmr]; ring_intZ
  have hc2 : a1 * A2 - a2 * A1 + a3 * A4 - a4 * A3 = m * (q1 * A2 - q2 * A1 + q3 * A4 - q4 * A3) := by
    rw [hqa1, hqa2, hqa3, hqa4]; ring_intZ
  have hc3 : a1 * A3 - a2 * A4 - a3 * A1 + a4 * A2 = m * (q1 * A3 - q2 * A4 - q3 * A1 + q4 * A2) := by
    rw [hqa1, hqa2, hqa3, hqa4]; ring_intZ
  have hc4 : a1 * A4 + a2 * A3 - a3 * A2 - a4 * A1 = m * (q1 * A4 + q2 * A3 - q3 * A2 - q4 * A1) := by
    rw [hqa1, hqa2, hqa3, hqa4]; ring_intZ
  have hid := four_sq_id a1 a2 a3 a4 A1 A2 A3 A4
  rw [hmp, hmr, hc1, hc2, hc3, hc4] at hid
  apply mul_left_cancel_pos (mul_pos hm hm)
  rw [show m * m * (p * r) = (m * p) * (m * r) from by ring_intZ, hid]; ring_intZ

end E213.Lib.Math.NumberTheory.FourSquare
