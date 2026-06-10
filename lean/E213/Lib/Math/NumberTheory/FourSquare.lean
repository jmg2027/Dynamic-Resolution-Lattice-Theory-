import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.OrderMul
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.NatRing213
import E213.Meta.Nat.PureNat

/-!
# FourSquare — Lagrange's four-square theorem via Euler descent (Pillar II)

The descent route to `∀ n, n = a²+b²+c²+d²`, staying entirely over `ℤ` with ring identities and
`centered_div_int` — sidestepping the non-commutative Hurwitz-quaternion gcd.

  * ★★★ `four_sq_id` — **Euler's four-square identity** (multiplicativity, a ring identity).
  * `isSum4` / `isSum4_mul` — "is a sum of four squares" is closed under multiplication.
  * `descent_rec` — the parity-split descent (`m·p = Σ4², 1 ≤ m < p ⟹ isSum4 p`).
  * ★★★★★ `nat_isSum4` — **Lagrange's four-square theorem** (`∀ n, isSum4 ↑n`), assembled from
    the seed multiple, constructive prime factorization, and `isSum4_mul`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FourSquare

open E213.Meta.Int213.OrderMul (int_sign mul_pos int_lt_irrefl mul_le_mul_left_nonneg ofNat_le_of_le)
open E213.Meta.Int213.Order
  (le_antisymm le_of_sub_nonneg nonneg_of_le_zero sub_pos_of_lt lt_of_sub_pos zero_sub sub_self_zero
   lt_of_lt_of_le lt_of_le_of_lt le_of_lt le_trans add_le_add_right add_le_add_left)
open E213.Meta.Int213 (mul_neg zero_add)

/-- `a ≤ b`, `c ≤ d ⟹ a+c ≤ b+d` (pure). -/
theorem add_le_add {a b c d : Int} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_add_right h1 c) (add_le_add_left h2 b)

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

/-- `0 < c`, `c·a < c·b ⟹ a < b` (pure positive-mul `<`-cancellation). -/
theorem lt_of_mul_lt_mul_pos {c a b : Int} (hc : 0 < c) (h : c * a < c * b) : a < b := by
  rcases int_sign (a - b) with hge | hlt
  · exfalso
    have hba : b ≤ a := le_of_sub_nonneg (nonneg_of_le_zero hge)
    exact int_lt_irrefl (c * a) (lt_of_lt_of_le h (mul_le_mul_left_nonneg hba c (le_of_lt hc)))
  · have hp : (0 : Int) < b - a := by
      have hx := sub_pos_of_lt hlt; rwa [zero_sub, show -(a - b) = b - a from by ring_intZ] at hx
    exact lt_of_sub_pos hp

/-- `a.natAbs = 0 ⟹ a = 0`. -/
theorem natAbs_zero_imp {a : Int} (h : a.natAbs = 0) : a = 0 := by
  rcases Int.natAbs_eq a with he | he <;> rw [he, h] <;> decide

/-- `0 ≤ -x ⟹ x ≤ 0`. -/
theorem nonpos_of_neg_nonneg {x : Int} (h : 0 ≤ -x) : x ≤ 0 := by
  apply le_of_not_lt
  intro hpos
  have hc := add_le_add (show (1 : Int) ≤ x from hpos) h
  rw [Int.add_zero, show x + (-x) = x - x from by ring_intZ, sub_self_zero] at hc
  exact absurd hc (by decide)

/-- `0 ≤ a ⟹ (↑a.natAbs : ℤ) = a`. -/
theorem natCast_natAbs_nonneg {a : Int} (h : 0 ≤ a) : (a.natAbs : Int) = a := by
  rcases Int.natAbs_eq a with he | he
  · exact he.symm
  · have hle : (a.natAbs : Int) ≤ 0 := nonpos_of_neg_nonneg (he ▸ h)
    have hna : a.natAbs = 0 := Nat.le_zero.mp (E213.Meta.Int213.Order.le_of_ofNat_le hle)
    rw [hna, he, hna]; decide

/-- `(↑a : ℤ) < ↑b ⟹ a < b`. -/
theorem natCast_lt_imp {a b : Nat} (h : (a : Int) < (b : Int)) : a < b :=
  E213.Meta.Int213.Order.le_of_ofNat_le (show ((a + 1 : Nat) : Int) ≤ (b : Int) from h)

/-- `a ≠ 0 ⟹ 1 ≤ a.natAbs`. -/
theorem natAbs_pos_of_ne {a : Int} (h : a ≠ 0) : 1 ≤ a.natAbs :=
  Nat.pos_of_ne_zero (fun h0 => h (natAbs_zero_imp h0))

/-- `a + b = 0`, `0 ≤ b ⟹ a ≤ 0`. -/
theorem nonpos_of_add_eq_zero {a b : Int} (hb : 0 ≤ b) (h : a + b = 0) : a ≤ 0 := by
  apply nonpos_of_neg_nonneg
  have hba : -a = b := by
    have e2 : -a + (a + b) = b := by ring_intZ
    rw [h, Int.add_zero] at e2; exact e2
  rw [hba]; exact hb

/-- `a·a = 0 ⟹ a = 0`. -/
theorem sq_eq_zero {a : Int} (h : a * a = 0) : a = 0 := by
  rcases int_sign a with hge | hlt
  · exact le_antisymm (le_of_not_lt (fun hp => int_lt_irrefl 0 (h ▸ mul_pos hp hp))) hge
  · exfalso
    have hp : (0 : Int) < -a := by have hx := sub_pos_of_lt hlt; rwa [zero_sub] at hx
    have h2 : (0 : Int) < (-a) * (-a) := mul_pos hp hp
    rw [show (-a) * (-a) = a * a from by ring_intZ, h] at h2; exact int_lt_irrefl 0 h2

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

/-! ## §3 — parity helpers for the even-`m` halving -/

open E213.Lib.Math.NumberTheory.ModArith.CenteredDivision (centered_div_int)
open E213.Tactic.NatHelper (cases_lt_two)

/-- Every integer is even or odd.  Canonical proof in `CenteredDivision`; this is a
thin re-export so existing consumers keep the local name. -/
theorem int_even_or_odd (a : Int) : (∃ k, a = 2 * k) ∨ (∃ k, a = 2 * k + 1) :=
  E213.Lib.Math.NumberTheory.ModArith.CenteredDivision.int_even_or_odd a

/-- `a − b = 2k` ⟹ `a²+b² = 2(s²+t²)` for some `s,t` (`s=b+k, t=k`). -/
theorem sum_two_sq_of_even_diff (a b k : Int) (h : a - b = 2 * k) :
    ∃ s t, a * a + b * b = 2 * (s * s + t * t) := by
  refine ⟨b + k, k, ?_⟩
  have ha : a = b + 2 * k := by rw [← h]; ring_intZ
  rw [ha]; ring_intZ

/-- `2c ≠ 1` over `ℤ` (via `natAbs`: `2·natAbs = 1` impossible). -/
theorem two_c_ne_one (c : Int) : 2 * c ≠ 1 := by
  intro h
  have hn : (2 * c).natAbs = (1 : Int).natAbs := by rw [h]
  rw [E213.Lib.Math.NumberTheory.PolyRoot.natAbs_mul, show (2 : Int).natAbs = 2 from rfl,
    show (1 : Int).natAbs = 1 from rfl] at hn
  rcases Nat.eq_zero_or_pos c.natAbs with h0 | h0
  · rw [h0] at hn; exact absurd hn (by decide)
  · have h2 : 2 ≤ 2 * c.natAbs := by have := Nat.mul_le_mul_left 2 h0; rwa [Nat.mul_one] at this
    rw [hn] at h2; exact absurd h2 (by decide)

/-- `a²+b²` even ⟹ `a−b` even (same parity). -/
theorem sq_sum_even_imp_diff_even (a b : Int) (h : ∃ N, a * a + b * b = 2 * N) :
    ∃ u, a - b = 2 * u := by
  obtain ⟨N, hN⟩ := h
  rcases int_even_or_odd a with ⟨x, ha⟩ | ⟨x, ha⟩ <;> rcases int_even_or_odd b with ⟨y, hb⟩ | ⟨y, hb⟩
  · exact ⟨x - y, by rw [ha, hb]; ring_intZ⟩
  · exfalso; rw [ha, hb] at hN
    apply two_c_ne_one (N - (2 * x * x + 2 * y * y + 2 * y))
    rw [show 2 * (N - (2 * x * x + 2 * y * y + 2 * y))
      = 2 * N - 2 * (2 * x * x + 2 * y * y + 2 * y) from by ring_intZ, ← hN]; ring_intZ
  · exfalso; rw [ha, hb] at hN
    apply two_c_ne_one (N - (2 * x * x + 2 * x + 2 * y * y))
    rw [show 2 * (N - (2 * x * x + 2 * x + 2 * y * y))
      = 2 * N - 2 * (2 * x * x + 2 * x + 2 * y * y) from by ring_intZ, ← hN]; ring_intZ
  · exact ⟨x - y, by rw [ha, hb]; ring_intZ⟩

/-- Given a same-parity pair `(a,b)` and `Σ4²` even, halve into four squares. -/
theorem combine (a b c d : Int) (hab : ∃ u, a - b = 2 * u)
    (h : ∃ N, a * a + b * b + c * c + d * d = 2 * N) :
    ∃ s1 s2 s3 s4, a * a + b * b + c * c + d * d = 2 * (s1 * s1 + s2 * s2 + s3 * s3 + s4 * s4) := by
  obtain ⟨u, hu⟩ := hab
  obtain ⟨s, t, hst⟩ := sum_two_sq_of_even_diff a b u hu
  obtain ⟨N, hN⟩ := h
  have hcd : ∃ M, c * c + d * d = 2 * M := ⟨N - (s * s + t * t), by
    have e : c * c + d * d = 2 * N - (a * a + b * b) := by rw [← hN]; ring_intZ
    rw [e, hst]; ring_intZ⟩
  obtain ⟨v, hv⟩ := sq_sum_even_imp_diff_even c d hcd
  obtain ⟨s', t', hst'⟩ := sum_two_sq_of_even_diff c d v hv
  refine ⟨s, t, s', t', ?_⟩
  have e : a * a + b * b + c * c + d * d = (a * a + b * b) + (c * c + d * d) := by ring_intZ
  rw [e, hst, hst']; ring_intZ

/-- **Halving a sum of four squares.**  `Σaᵢ² = 2N` ⟹ `Σaᵢ² = 2·Σsᵢ²` (pair two same-parity
    `aᵢ` — pigeonhole on `a₁,a₂,a₃` — the complement matches by `Σ` even). -/
theorem halve4 (a1 a2 a3 a4 : Int) (h : ∃ N, a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4 = 2 * N) :
    ∃ s1 s2 s3 s4, a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4 = 2 * (s1 * s1 + s2 * s2 + s3 * s3 + s4 * s4) := by
  obtain ⟨N, hN⟩ := h
  have hh : ∀ b1 b2 b3 b4 : Int, b1 * b1 + b2 * b2 + b3 * b3 + b4 * b4 = a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4 →
      ∃ M, b1 * b1 + b2 * b2 + b3 * b3 + b4 * b4 = 2 * M := fun b1 b2 b3 b4 heq => ⟨N, by rw [heq]; exact hN⟩
  have conv : ∀ b1 b2 b3 b4 : Int, b1 * b1 + b2 * b2 + b3 * b3 + b4 * b4 = a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4 →
      (∃ s1 s2 s3 s4, b1 * b1 + b2 * b2 + b3 * b3 + b4 * b4 = 2 * (s1 * s1 + s2 * s2 + s3 * s3 + s4 * s4)) →
      ∃ s1 s2 s3 s4, a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4 = 2 * (s1 * s1 + s2 * s2 + s3 * s3 + s4 * s4) :=
    fun b1 b2 b3 b4 heq hex => by
      obtain ⟨s1, s2, s3, s4, hg⟩ := hex; exact ⟨s1, s2, s3, s4, by rw [← heq]; exact hg⟩
  rcases int_even_or_odd a1 with ⟨x1, p1⟩ | ⟨x1, p1⟩ <;>
    rcases int_even_or_odd a2 with ⟨x2, p2⟩ | ⟨x2, p2⟩ <;>
    rcases int_even_or_odd a3 with ⟨x3, p3⟩ | ⟨x3, p3⟩
  · exact combine a1 a2 a3 a4 ⟨x1 - x2, by rw [p1, p2]; ring_intZ⟩ ⟨N, hN⟩
  · exact combine a1 a2 a3 a4 ⟨x1 - x2, by rw [p1, p2]; ring_intZ⟩ ⟨N, hN⟩
  · exact conv a1 a3 a2 a4 (by ring_intZ) (combine a1 a3 a2 a4 ⟨x1 - x3, by rw [p1, p3]; ring_intZ⟩ (hh a1 a3 a2 a4 (by ring_intZ)))
  · exact conv a2 a3 a1 a4 (by ring_intZ) (combine a2 a3 a1 a4 ⟨x2 - x3, by rw [p2, p3]; ring_intZ⟩ (hh a2 a3 a1 a4 (by ring_intZ)))
  · exact conv a2 a3 a1 a4 (by ring_intZ) (combine a2 a3 a1 a4 ⟨x2 - x3, by rw [p2, p3]; ring_intZ⟩ (hh a2 a3 a1 a4 (by ring_intZ)))
  · exact conv a1 a3 a2 a4 (by ring_intZ) (combine a1 a3 a2 a4 ⟨x1 - x3, by rw [p1, p3]; ring_intZ⟩ (hh a1 a3 a2 a4 (by ring_intZ)))
  · exact combine a1 a2 a3 a4 ⟨x1 - x2, by rw [p1, p2]; ring_intZ⟩ ⟨N, hN⟩
  · exact combine a1 a2 a3 a4 ⟨x1 - x2, by rw [p1, p2]; ring_intZ⟩ ⟨N, hN⟩

/-- `2|A| ≤ 2k+1` (odd bound) ⟹ `4A² ≤ (2k)²` (strict: avoids the `r=m` edge for odd `m`). -/
theorem Asq_bound (A : Int) (k : Nat) (hb : 2 * A.natAbs ≤ 2 * k + 1) :
    4 * (A * A) ≤ (2 * (k : Int)) * (2 * (k : Int)) := by
  have hak : A.natAbs ≤ k := by
    rcases Nat.lt_or_ge A.natAbs (k + 1) with h | h
    · exact Nat.le_of_lt_succ h
    · exfalso
      have h2 : 2 * (k + 1) ≤ 2 * A.natAbs := Nat.mul_le_mul_left 2 h
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring_nat] at h2
      exact absurd (Nat.le_trans h2 hb) (Nat.not_succ_le_self _)
  have hsq : 4 * (A.natAbs * A.natAbs) ≤ 4 * (k * k) :=
    Nat.mul_le_mul_left 4 (Nat.mul_le_mul hak hak)
  have e1 : 4 * (A * A) = ((4 * (A.natAbs * A.natAbs) : Nat) : Int) := by
    rw [← Int.natAbs_mul_self (a := A)]; rfl
  have e2 : (2 * (k : Int)) * (2 * (k : Int)) = ((4 * (k * k) : Nat) : Int) := by
    rw [show ((4 * (k * k) : Nat) : Int) = 4 * ((k : Int) * (k : Int)) from rfl]; ring_intZ
  rw [e1, e2]; exact ofNat_le_of_le hsq

/-- `0 ≤ A²`. -/
theorem sq_nonneg (A : Int) : 0 ≤ A * A := by
  rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _

/-- The strict `r < m` bound (odd `m`): four coordinates with `4Aᵢ² ≤ (m−1)²` and `ΣAᵢ² = m·r`
    force `r < m` — `4(m·r) = 4ΣAᵢ² ≤ 4(m−1)² < 4m²`. -/
theorem rlt (m r A1 A2 A3 A4 : Int) (hmpos : 0 < m) (h1m : 1 ≤ m)
    (hb1 : 4 * (A1 * A1) ≤ (m - 1) * (m - 1)) (hb2 : 4 * (A2 * A2) ≤ (m - 1) * (m - 1))
    (hb3 : 4 * (A3 * A3) ≤ (m - 1) * (m - 1)) (hb4 : 4 * (A4 * A4) ≤ (m - 1) * (m - 1))
    (hmr : A1 * A1 + A2 * A2 + A3 * A3 + A4 * A4 = m * r) : r < m := by
  have hs := add_le_add (add_le_add (add_le_add hb1 hb2) hb3) hb4
  have hle : 4 * (m * r) ≤ 4 * ((m - 1) * (m - 1)) := by
    rw [show 4 * (m * r) = 4 * (A1 * A1) + 4 * (A2 * A2) + 4 * (A3 * A3) + 4 * (A4 * A4)
        from by rw [← hmr]; ring_intZ,
      show 4 * ((m - 1) * (m - 1))
        = (m - 1) * (m - 1) + (m - 1) * (m - 1) + (m - 1) * (m - 1) + (m - 1) * (m - 1)
        from by ring_intZ]
    exact hs
  have h8 : (8 : Int) ≤ 8 * m := by
    have := mul_le_mul_left_nonneg h1m 8 (by decide)
    rwa [show (8 : Int) * 1 = 8 from by ring_intZ] at this
  have hstrict : 4 * ((m - 1) * (m - 1)) < 4 * (m * m) := by
    apply lt_of_sub_pos
    rw [show 4 * (m * m) - 4 * ((m - 1) * (m - 1)) = 8 * m - 4 from by ring_intZ]
    have h4 : (4 : Int) ≤ 8 * m - 4 := by
      have := add_le_add_right h8 (-4)
      rwa [show (8 : Int) + (-4) = 4 from by ring_intZ,
        show 8 * m + (-4) = 8 * m - 4 from by ring_intZ] at this
    exact lt_of_lt_of_le (by decide) h4
  exact lt_of_mul_lt_mul_pos hmpos (lt_of_mul_lt_mul_pos (by decide) (lt_of_le_of_lt hle hstrict))

/-- ★★★ **Even-`m` descent (parity-halving).**  `isSum4 (2m'·p) ⟹ isSum4 (m'·p)`. -/
theorem halve_step (m' p : Int) (h : isSum4 (2 * m' * p)) : isSum4 (m' * p) := by
  obtain ⟨a1, a2, a3, a4, ha⟩ := h
  obtain ⟨s1, s2, s3, s4, hs⟩ := halve4 a1 a2 a3 a4 ⟨m' * p, by rw [← ha]; ring_intZ⟩
  refine ⟨s1, s2, s3, s4, ?_⟩
  apply mul_left_cancel_pos (show (0 : Int) < 2 by decide)
  rw [show 2 * (m' * p) = 2 * m' * p from by ring_intZ, ha]; exact hs

/-! ## §4 — the odd-`m` centred descent -/

open E213.Lib.Math.NumberTheory.ModArith.CenteredDivision (centered_div_int)
open E213.Lib.Math.NumberTheory.PolyRoot (int_dvd_to_nat)
open E213.Meta.Int213.PolyIntM (mul_zeroZ)
open E213.Meta.Int213 (add_nonneg)

/-- ★★★★ **Odd-`m` centred descent.**  `p` prime, `m = 2k+1` (`2 ≤ m < p`), `isSum4 (m·p)` ⟹
    `∃ r, 1 ≤ r < m ∧ isSum4 (r·p)`.  Centred residues `aᵢ = qᵢm + Aᵢ` give the explicit smaller
    multiple `r = p − 2Σaᵢqᵢ + mΣqᵢ²` (`descent_core`); the odd strict bound (`rlt`) forces
    `r < m` (no `r = m` edge), and `r = 0` would give `m ∣ p` (impossible for `2 ≤ m < p` prime). -/
theorem odd_descent (p : Nat) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (m k : Nat) (hmk : m = 2 * k + 1) (hm2 : 2 ≤ m) (hmlt : m < p)
    (h : isSum4 ((m : Int) * (p : Int))) :
    ∃ r : Nat, 1 ≤ r ∧ r < m ∧ isSum4 ((r : Int) * (p : Int)) := by
  obtain ⟨a1, a2, a3, a4, hsum⟩ := h
  have h1m : (1 : Int) ≤ (m : Int) := by
    have := ofNat_le_of_le (show 1 ≤ m from Nat.le_of_lt (Nat.lt_of_lt_of_le (by decide) hm2))
    rwa [show ((1 : Nat) : Int) = 1 from rfl] at this
  have hmpos : (0 : Int) < (m : Int) := h1m
  obtain ⟨q1, A1, hq1, hb1⟩ := centered_div_int a1 (m : Int) hmpos
  obtain ⟨q2, A2, hq2, hb2⟩ := centered_div_int a2 (m : Int) hmpos
  obtain ⟨q3, A3, hq3, hb3⟩ := centered_div_int a3 (m : Int) hmpos
  obtain ⟨q4, A4, hq4, hb4⟩ := centered_div_int a4 (m : Int) hmpos
  rw [Int.natAbs_ofNat, hmk] at hb1 hb2 hb3 hb4
  obtain ⟨rI, hrI⟩ : ∃ rI, (p : Int) - 2 * (a1 * q1 + a2 * q2 + a3 * q3 + a4 * q4)
      + (m : Int) * (q1 * q1 + q2 * q2 + q3 * q3 + q4 * q4) = rI := ⟨_, rfl⟩
  have hmr : A1 * A1 + A2 * A2 + A3 * A3 + A4 * A4 = (m : Int) * rI := by
    have hA1 : A1 = a1 - q1 * (m : Int) := by rw [hq1]; ring_intZ
    have hA2 : A2 = a2 - q2 * (m : Int) := by rw [hq2]; ring_intZ
    have hA3 : A3 = a3 - q3 * (m : Int) := by rw [hq3]; ring_intZ
    have hA4 : A4 = a4 - q4 * (m : Int) := by rw [hq4]; ring_intZ
    rw [hA1, hA2, hA3, hA4, ← hrI]
    have e : (a1 - q1 * (m : Int)) * (a1 - q1 * (m : Int))
        + (a2 - q2 * (m : Int)) * (a2 - q2 * (m : Int))
        + (a3 - q3 * (m : Int)) * (a3 - q3 * (m : Int))
        + (a4 - q4 * (m : Int)) * (a4 - q4 * (m : Int))
        = (a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4)
          - 2 * (m : Int) * (a1 * q1 + a2 * q2 + a3 * q3 + a4 * q4)
          + (m : Int) * (m : Int) * (q1 * q1 + q2 * q2 + q3 * q3 + q4 * q4) := by ring_intZ
    rw [e, ← hsum]; ring_intZ
  obtain ⟨d1, d2, d3, d4, hdc⟩ := descent_core (m : Int) (p : Int) rI a1 a2 a3 a4
    q1 q2 q3 q4 A1 A2 A3 A4 hmpos hq1 hq2 hq3 hq4 hsum.symm hmr
  have hmm1 : (2 * (k : Int)) = (m : Int) - 1 := by
    rw [hmk, show ((2 * k + 1 : Nat) : Int) = 2 * (k : Int) + 1 from rfl]; ring_intZ
  have hB1 := Asq_bound A1 k hb1; rw [hmm1] at hB1
  have hB2 := Asq_bound A2 k hb2; rw [hmm1] at hB2
  have hB3 := Asq_bound A3 k hb3; rw [hmm1] at hB3
  have hB4 := Asq_bound A4 k hb4; rw [hmm1] at hB4
  have hrltm : rI < (m : Int) := rlt (m : Int) rI A1 A2 A3 A4 hmpos h1m hB1 hB2 hB3 hB4 hmr
  have hSnn : 0 ≤ A1 * A1 + A2 * A2 + A3 * A3 + A4 * A4 :=
    add_nonneg (add_nonneg (add_nonneg (sq_nonneg A1) (sq_nonneg A2)) (sq_nonneg A3)) (sq_nonneg A4)
  have hmrnn : 0 ≤ (m : Int) * rI := hmr ▸ hSnn
  have hrnn : 0 ≤ rI := by
    rcases int_sign rI with hh | hh
    · exact hh
    · exfalso
      have hp : 0 < (m : Int) * (-rI) :=
        mul_pos hmpos (by have hx := sub_pos_of_lt hh; rwa [zero_sub] at hx)
      rw [mul_neg, ← zero_sub] at hp
      exact int_lt_irrefl _ (lt_of_lt_of_le (lt_of_sub_pos hp) hmrnn)
  have hrne : rI ≠ 0 := by
    intro hr0
    have hSum0 : A1 * A1 + A2 * A2 + A3 * A3 + A4 * A4 = 0 := by rw [hmr, hr0]; exact mul_zeroZ _
    have hA1z : A1 = 0 := sq_eq_zero (le_antisymm
      (nonpos_of_add_eq_zero (add_nonneg (add_nonneg (sq_nonneg A2) (sq_nonneg A3)) (sq_nonneg A4))
        (by rw [← hSum0]; ring_intZ)) (sq_nonneg A1))
    have hA2z : A2 = 0 := sq_eq_zero (le_antisymm
      (nonpos_of_add_eq_zero (add_nonneg (add_nonneg (sq_nonneg A1) (sq_nonneg A3)) (sq_nonneg A4))
        (by rw [← hSum0]; ring_intZ)) (sq_nonneg A2))
    have hA3z : A3 = 0 := sq_eq_zero (le_antisymm
      (nonpos_of_add_eq_zero (add_nonneg (add_nonneg (sq_nonneg A1) (sq_nonneg A2)) (sq_nonneg A4))
        (by rw [← hSum0]; ring_intZ)) (sq_nonneg A3))
    have hA4z : A4 = 0 := sq_eq_zero (le_antisymm
      (nonpos_of_add_eq_zero (add_nonneg (add_nonneg (sq_nonneg A1) (sq_nonneg A2)) (sq_nonneg A3))
        (by rw [← hSum0]; ring_intZ)) (sq_nonneg A4))
    have ha1 : a1 = q1 * (m : Int) := by rw [hq1, hA1z, Int.add_zero]
    have ha2 : a2 = q2 * (m : Int) := by rw [hq2, hA2z, Int.add_zero]
    have ha3 : a3 = q3 * (m : Int) := by rw [hq3, hA3z, Int.add_zero]
    have ha4 : a4 = q4 * (m : Int) := by rw [hq4, hA4z, Int.add_zero]
    have hpeq : (p : Int) = (m : Int) * (q1 * q1 + q2 * q2 + q3 * q3 + q4 * q4) := by
      apply mul_left_cancel_pos hmpos
      rw [hsum, ha1, ha2, ha3, ha4]; ring_intZ
    have hmdp : m ∣ p := by
      have := int_dvd_to_nat m (p : Int) ⟨q1 * q1 + q2 * q2 + q3 * q3 + q4 * q4, hpeq⟩
      rwa [Int.natAbs_ofNat] at this
    rcases hpr m hmdp with h1 | h1
    · rw [h1] at hm2; exact absurd hm2 (by decide)
    · exact absurd (h1 ▸ hmlt) (Nat.lt_irrefl p)
  refine ⟨rI.natAbs, natAbs_pos_of_ne hrne, ?_, ?_⟩
  · exact natCast_lt_imp (by rw [natCast_natAbs_nonneg hrnn]; exact hrltm)
  · rw [natCast_natAbs_nonneg hrnn]
    exact ⟨d1, d2, d3, d4, by rw [show rI * (p : Int) = (p : Int) * rI from by ring_intZ]; exact hdc⟩

/-! ## §5 — the parity-split fuel recursion -/

open E213.Meta.Nat.AddMod213 (div_add_mod)

/-- Every `Nat` is even or odd — `Meta.Nat.PureNat.nat_dichotomy`. -/
abbrev nat_even_or_odd := E213.Meta.Nat.PureNat.nat_dichotomy

/-- ★★★★★ **The descent recursion.**  `p` prime; for `1 ≤ m < p` with `isSum4 (m·p)`,
    every such `m` descends to `m = 1`, giving `isSum4 p`.  Even `m` halves (`halve_step`),
    odd `m > 1` strictly shrinks (`odd_descent`); the `fuel` bounds the descent length. -/
theorem descent_rec (p : Nat) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ (fuel m : Nat), m ≤ fuel → 1 ≤ m → m < p →
      isSum4 ((m : Int) * (p : Int)) → isSum4 ((p : Int)) := by
  intro fuel
  induction fuel with
  | zero => intro m hmf h1 _ _; exact absurd (Nat.le_trans h1 hmf) (by decide)
  | succ n ih =>
    intro m hmf h1 hmlt hsum
    rcases Nat.lt_or_ge 1 m with h2 | h2
    · rcases nat_even_or_odd m with ⟨m', he⟩ | ⟨k, ho⟩
      · -- even `m = 2 m'`
        have hm'1 : 1 ≤ m' := by
          rcases Nat.eq_zero_or_pos m' with hz | hz
          · rw [hz, Nat.mul_zero] at he; rw [he] at h2; exact absurd h2 (by decide)
          · exact hz
        have hm'lt : m' < m := by
          rw [he, Nat.two_mul]; exact Nat.lt_add_of_pos_left hm'1
        have hcast : (m : Int) = 2 * (m' : Int) := by rw [he]; rfl
        have hs2 : isSum4 (2 * (m' : Int) * (p : Int)) := by
          rw [show 2 * (m' : Int) * (p : Int) = (m : Int) * (p : Int) from by rw [hcast]]
          exact hsum
        exact ih m' (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hm'lt hmf)) hm'1
          (Nat.lt_trans hm'lt hmlt) (halve_step (m' : Int) (p : Int) hs2)
      · -- odd `m = 2 k + 1`, `m > 1`
        obtain ⟨r, hr1, hrlt, hrs⟩ :=
          odd_descent p hpr m k ho h2 hmlt hsum
        exact ih r (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hrlt hmf)) hr1
          (Nat.lt_trans hrlt hmlt) hrs
    · -- `m = 1`
      have hm1 : m = 1 := Nat.le_antisymm h2 h1
      rw [hm1, show ((1 : Nat) : Int) * (p : Int) = (p : Int) from by
        rw [show ((1 : Nat) : Int) = 1 from rfl]; ring_intZ] at hsum
      exact hsum

/-! ## §6 — seed → initial multiple -/

open E213.Lib.Math.NumberTheory.FourSquareSeed (four_square_seed)

/-- **Seed to initial multiple.**  For a prime `p = 2m+1`, the seed `p ∣ x²+y²+1` (`x,y ≤ m`)
    gives `k·p = x²+y²+1²+0²` with `1 ≤ k < p` (`k·p ≤ 2m²+1 < p²`). -/
theorem seed_multiple (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hpm : 2 * m + 1 = p) :
    ∃ k : Nat, 1 ≤ k ∧ k < p ∧ isSum4 ((k : Int) * (p : Int)) := by
  obtain ⟨x, y, hx, hy, hdvd⟩ := four_square_seed p m hp hpr hpm
  obtain ⟨k, hk⟩ := hdvd   -- hk : x*x+y*y+1 = p*k
  -- `m ≥ 1`
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hz | hz
    · exfalso; rw [hz, Nat.mul_zero, Nat.zero_add] at hpm
      rw [← hpm] at hp; exact absurd hp (by decide)
    · exact hz
  refine ⟨k, ?_, ?_, ?_⟩
  · -- `k ≥ 1`
    rcases Nat.eq_zero_or_pos k with hz | hz
    · exfalso; rw [hz, Nat.mul_zero] at hk; exact Nat.noConfusion hk
    · exact hz
  · -- `k < p`
    have hxm : x * x ≤ m * m := Nat.mul_le_mul hx hx
    have hym : y * y ≤ m * m := Nat.mul_le_mul hy hy
    have hbound : x * x + y * y + 1 ≤ m * m + m * m + 1 :=
      Nat.add_le_add (Nat.add_le_add hxm hym) (Nat.le_refl 1)
    have hpsq : m * m + m * m + 1 + (2 * (m * m) + 4 * m) = p * p := by rw [← hpm]; ring_nat
    have hppos : 0 < 2 * (m * m) + 4 * m :=
      Nat.lt_of_lt_of_le (Nat.mul_pos (by decide) hm1) (Nat.le_add_left (4 * m) (2 * (m * m)))
    have hstrict : m * m + m * m + 1 < p * p := by
      rw [← hpsq]; exact Nat.lt_add_of_pos_right hppos
    have hlt : x * x + y * y + 1 < p * p := Nat.lt_of_le_of_lt hbound hstrict
    have hpklt : p * k < p * p := by rw [← hk]; exact hlt
    cases Nat.lt_or_ge k p with
    | inl h => exact h
    | inr h =>
      exfalso
      exact absurd (Nat.lt_of_lt_of_le hpklt (Nat.mul_le_mul_left p h)) (Nat.lt_irrefl (p * k))
  · -- `isSum4 (k·p)`
    refine ⟨(x : Int), (y : Int), 1, 0, ?_⟩
    have e1 : (p : Int) * (k : Int) = (x : Int) * (x : Int) + (y : Int) * (y : Int) + 1 := by
      have h2 : ((x * x + y * y + 1 : Nat) : Int) = ((p * k : Nat) : Int) := by rw [hk]
      exact h2.symm
    rw [show (1 : Int) * 1 = 1 from rfl, show (0 : Int) * 0 = 0 from rfl, Int.add_zero,
      show (k : Int) * (p : Int) = (p : Int) * (k : Int) from by ring_intZ]
    exact e1

/-! ## §7 — prime factorization → all `n` -/

open E213.Lib.Math.NumberTheory.FourSquareSeed (mod_zero_of_dvd)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (dvd_trans_loc le_of_dvd_loc)
open E213.Meta.Nat.NatRing213 (nat_mul_lt_mul_right)

/-- Decidable divisibility (constructive), `∅`-axiom via `n % k`. -/
theorem dvd_dec (k n : Nat) (hk : 0 < k) : (k ∣ n) ∨ ¬ k ∣ n := by
  rcases Nat.eq_zero_or_pos (n % k) with h0 | hp
  · exact Or.inl (dvd_of_mod_eq_zero h0)
  · exact Or.inr (fun hd => by rw [mod_zero_of_dvd n k hd] at hp; exact Nat.lt_irrefl 0 hp)

/-- Bounded search: either `n` has a nontrivial divisor `2 ≤ d < n`, or no such `d < k` exists. -/
theorem searchDiv (n : Nat) : ∀ (k : Nat),
    (∃ d, 2 ≤ d ∧ d < n ∧ d ∣ n) ∨ (∀ d, 2 ≤ d → d < n → d < k → ¬ d ∣ n) := by
  intro k
  induction k with
  | zero => exact Or.inr (fun d _ _ hlt => absurd hlt (Nat.not_lt_zero d))
  | succ k ih =>
    rcases ih with hfound | hnone
    · exact Or.inl hfound
    · rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · refine Or.inr (fun d hd2 hdn hdk1 => ?_)
        rcases Nat.lt_or_ge d k with hdk | hdk
        · exact hnone d hd2 hdn hdk
        · have he : d = k := Nat.le_antisymm (Nat.le_of_lt_succ hdk1) hdk
          rw [he] at hd2; exact absurd (Nat.lt_of_le_of_lt hd2 hk2) (Nat.lt_irrefl 2)
      · rcases Nat.lt_or_ge k n with hkn | hkn
        · rcases dvd_dec k n (Nat.lt_of_lt_of_le (by decide) hk2) with hdvd | hndvd
          · exact Or.inl ⟨k, hk2, hkn, hdvd⟩
          · refine Or.inr (fun d hd2 hdn hdk1 => ?_)
            rcases Nat.lt_or_ge d k with hdk | hdk
            · exact hnone d hd2 hdn hdk
            · have he : d = k := Nat.le_antisymm (Nat.le_of_lt_succ hdk1) hdk
              rw [he]; exact hndvd
        · refine Or.inr (fun d hd2 hdn hdk1 => ?_)
          rcases Nat.lt_or_ge d k with hdk | hdk
          · exact hnone d hd2 hdn hdk
          · have he : d = k := Nat.le_antisymm (Nat.le_of_lt_succ hdk1) hdk
            rw [he] at hdn; exact absurd (Nat.lt_of_lt_of_le hdn hkn) (Nat.lt_irrefl k)

/-- **Every `n ≥ 2` has a prime factor** (`∅`-axiom; least-divisor argument via `searchDiv`). -/
theorem exists_prime_factor : ∀ (fuel n : Nat), n ≤ fuel → 2 ≤ n →
    ∃ q, 1 < q ∧ (∀ d, d ∣ q → d = 1 ∨ d = q) ∧ q ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro n hn h2; exact absurd (Nat.le_trans h2 hn) (by decide)
  | succ f ih =>
    intro n hnf h2
    rcases searchDiv n n with ⟨d, hd2, hdn, hddvd⟩ | hnone
    · obtain ⟨q, hq1, hqpr, hqd⟩ :=
        ih d (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hdn hnf)) hd2
      exact ⟨q, hq1, hqpr, dvd_trans_loc q d n hqd hddvd⟩
    · refine ⟨n, h2, ?_, ⟨1, (Nat.mul_one n).symm⟩⟩
      intro e hen
      have hen_le : e ≤ n := le_of_dvd_loc (Nat.lt_of_lt_of_le (by decide) h2) hen
      rcases Nat.lt_or_ge e n with helt | hege
      · rcases Nat.lt_or_ge e 2 with he2 | he2
        · rcases cases_lt_two he2 with h0 | h1
          · exfalso; rw [h0] at hen
            obtain ⟨c, hc⟩ := hen; rw [Nat.zero_mul] at hc
            rw [hc] at h2; exact absurd h2 (by decide)
          · exact Or.inl h1
        · exact absurd hen (hnone e he2 helt helt)
      · exact Or.inr (Nat.le_antisymm hen_le hege)

/-- **Every prime is a sum of four squares.**  `p = 2` directly; odd `p` via the seed multiple
    and the descent recursion. -/
theorem prime_isSum4 (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    isSum4 ((p : Int)) := by
  rcases nat_even_or_odd p with ⟨k, he⟩ | ⟨k, ho⟩
  · -- even ⟹ `p = 2`
    have h2p : (2 : Nat) = p := by
      rcases hpr 2 ⟨k, he⟩ with h | h
      · exact absurd h (by decide)
      · exact h
    rw [← h2p]; exact ⟨1, 1, 0, 0, by decide⟩
  · -- odd
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hz | hz
      · exfalso; rw [hz, Nat.mul_zero, Nat.zero_add] at ho
        rw [ho] at hp; exact absurd hp (by decide)
      · exact hz
    obtain ⟨c, hc1, hclt, hcs⟩ := seed_multiple p k hp hpr ho.symm
    exact descent_rec p hpr p c (Nat.le_of_lt hclt) hc1 hclt hcs

/-- ★★★★★ **Lagrange's four-square theorem.**  Every natural number is a sum of four squares. -/
theorem nat_isSum4 : ∀ (n : Nat), isSum4 ((n : Int)) := by
  have main : ∀ (fuel n : Nat), n ≤ fuel → isSum4 ((n : Int)) := by
    intro fuel
    induction fuel with
    | zero =>
      intro n hn
      have : n = 0 := Nat.le_antisymm hn (Nat.zero_le n)
      rw [this]; exact ⟨0, 0, 0, 0, by decide⟩
    | succ f ih =>
      intro n hnf
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · -- `n = 0` or `n = 1`
        rcases cases_lt_two hlt with h0 | h1
        · rw [h0]; exact ⟨0, 0, 0, 0, by decide⟩
        · rw [h1]; exact ⟨1, 0, 0, 0, by decide⟩
      · -- `n ≥ 2`: split off a prime factor
        obtain ⟨q, hq1, hqpr, hqd⟩ := exists_prime_factor n n (Nat.le_refl n) hge
        obtain ⟨r, hr⟩ := hqd   -- hr : n = q * r
        have hr1 : 1 ≤ r := by
          rcases Nat.eq_zero_or_pos r with hz | hz
          · exfalso; rw [hz, Nat.mul_zero] at hr
            rw [hr] at hge; exact absurd hge (by decide)
          · exact hz
        have hrlt : r < n := by
          rw [hr]
          have : 1 * r < q * r := nat_mul_lt_mul_right hr1 hq1
          rwa [Nat.one_mul] at this
        have hqsum : isSum4 ((q : Int)) := prime_isSum4 q hq1 hqpr
        have hrsum : isSum4 ((r : Int)) :=
          ih r (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hrlt hnf))
        have hmul : isSum4 ((q : Int) * (r : Int)) := isSum4_mul hqsum hrsum
        rw [hr]; exact hmul
  intro n; exact main n n (Nat.le_refl n)

end E213.Lib.Math.NumberTheory.FourSquare
