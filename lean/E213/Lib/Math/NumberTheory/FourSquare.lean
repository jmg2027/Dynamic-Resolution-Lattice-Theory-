import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.OrderMul
import E213.Meta.Tactic.NatHelper

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

/-- Every integer is even or odd. -/
theorem int_even_or_odd (a : Int) : (∃ k, a = 2 * k) ∨ (∃ k, a = 2 * k + 1) := by
  obtain ⟨q, r, hd, hr⟩ := centered_div_int a 2 (by decide)
  rw [show (2 : Int).natAbs = 2 from rfl] at hr
  have hle : r.natAbs ≤ 1 := by
    rcases Nat.lt_or_ge r.natAbs 2 with h | h
    · exact Nat.le_of_lt_succ h
    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 2 h) hr) (by decide)
  rcases cases_lt_two (Nat.lt_succ_of_le hle) with h0 | h1
  · left; refine ⟨q, ?_⟩
    have hr0 : r = 0 := by rcases Int.natAbs_eq r with he | he <;> rw [he, h0] <;> decide
    rw [hd, hr0, Int.add_zero]; ring_intZ
  · rcases Int.natAbs_eq r with he | he
    · right; exact ⟨q, by rw [hd, he, h1, show ((1 : Nat) : Int) = 1 from rfl]; ring_intZ⟩
    · right; exact ⟨q - 1, by rw [hd, he, h1, show ((1 : Nat) : Int) = 1 from rfl]; ring_intZ⟩

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

end E213.Lib.Math.NumberTheory.FourSquare
