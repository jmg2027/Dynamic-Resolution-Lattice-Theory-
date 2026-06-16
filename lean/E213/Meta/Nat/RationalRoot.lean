import E213.Meta.Nat.Gcd213

/-!
# RationalRoot — the rational root theorem, ℕ-native (∅-axiom)

The bottom rung of the number-system square (`research-notes/frontiers/
numbersystem_square.md`): **ℤ is the integral closure of ℕ in ℚ** — a rational
root `p/q` (in lowest terms) of a monic integer polynomial has `q = 1`, i.e. is an
integer.  Degree 2, stated ℕ-natively (the tuple is the number; no ℤ, no
subtraction — the monic equation `p² + a₁pq + a₀q² = c₁pq + c₀q²` is the
sign-split, subtraction-free two-sided form, the `a`-terms the positive
coefficients, the `c`-terms the negative parts, per `Int213.subNatNat` slot
reading).

The engine is Euclid: every term but `p²` carries a factor `q`, so `q ∣ p²`;
coprimality (`gcd213 p q = 1`) then forces `q ∣ p`, whence `q ∣ gcd213 p q = 1`.
All PURE — the propext-tainted core lemmas (`omega`, `Nat.mul_assoc`,
`Nat.dvd_refl`, `Nat.dvd_one`) are avoided in favour of the `Gcd213`/`mul_assoc_213`
∅-axiom replacements.
-/

namespace E213.Meta.Nat.RationalRoot

open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213
  (mul_assoc_213 gcd213_greatest mul_eq_one_left gcd213_comm
   dvd_add_213 add_left_cancel_213 coprime_dvd_of_dvd_mul)

/-- `q ∣ k * q` (explicit witness, no `Nat.dvd_mul_*` propext leak). -/
theorem dvd_mul_q (q k : Nat) : q ∣ k * q := ⟨k, Nat.mul_comm k q⟩

/-- `q ∣ k * (q * q)`. -/
theorem dvd_mul_qq (q k : Nat) : q ∣ k * (q * q) :=
  ⟨k * q, by rw [← mul_assoc_213 k q q, Nat.mul_comm (k * q) q]⟩

/-- **Cancel a divisible summand** (subtraction-free): `q ∣ a + b` and `q ∣ b`
    give `q ∣ a`.  No `Nat` subtraction — `a = q·d` is recovered by
    `add_left_cancel_213` after matching `a + b = b + q·d`. -/
theorem dvd_of_add_dvd_right {q a b : Nat} (hq : 0 < q)
    (hab : q ∣ a + b) (hb : q ∣ b) : q ∣ a := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hb
  have hnm : n ≤ m := by
    have hle : q * n ≤ q * m := by rw [← hn, ← hm]; exact Nat.le_add_left b a
    exact Nat.le_of_mul_le_mul_left hle hq
  obtain ⟨d, hd⟩ := Nat.le.dest hnm
  refine ⟨d, ?_⟩
  have key : a + b = b + q * d := by rw [hm, ← hd, Nat.mul_add, ← hn]
  have key2 : b + a = b + q * d := by rw [Nat.add_comm b a]; exact key
  exact add_left_cancel_213 b key2

/-- ★★★★★ **Rational root theorem (degree 2), ℕ-native.**  If `p/q` is in lowest
    terms (`gcd213 p q = 1`, `q > 0`) and satisfies the monic equation
    `p² + a₁pq + a₀q² = c₁pq + c₀q²` (the subtraction-free two-sided form of
    `(p/q)² + a₁(p/q) + a₀ = 0`), then `q = 1` — the root is an integer.  "ℤ is the
    integral closure of ℕ in ℚ" at degree 2. -/
theorem rational_root_monic_deg2 {p q a1 a0 c1 c0 : Nat}
    (hco : gcd213 p q = 1) (hq : 0 < q)
    (h : p * p + (a1 * p * q + a0 * (q * q)) = c1 * p * q + c0 * (q * q)) :
    q = 1 := by
  have hRHS : q ∣ c1 * p * q + c0 * (q * q) :=
    dvd_add_213 q _ _ (dvd_mul_q q (c1 * p)) (dvd_mul_qq q c0)
  have hX : q ∣ a1 * p * q + a0 * (q * q) :=
    dvd_add_213 q _ _ (dvd_mul_q q (a1 * p)) (dvd_mul_qq q a0)
  have hpp_plus : q ∣ p * p + (a1 * p * q + a0 * (q * q)) := by rw [h]; exact hRHS
  have hpp : q ∣ p * p := dvd_of_add_dvd_right hq hpp_plus hX
  have hqp : q ∣ p :=
    coprime_dvd_of_dvd_mul (show gcd213 q p = 1 by rw [gcd213_comm]; exact hco) hpp
  have hqq : q ∣ q := ⟨1, (Nat.mul_one q).symm⟩
  have hqg : q ∣ gcd213 p q := gcd213_greatest p q q hqp hqq
  rw [hco] at hqg
  obtain ⟨c, hc⟩ := hqg
  exact mul_eq_one_left q c hc.symm

/-- **Coprime divides a power ⟹ divides the base** (`gcd213 q p = 1`, `q ∣ pⁿ⁺¹`
    ⟹ `q ∣ p`).  Induction peeling one `p` per step through
    `coprime_dvd_of_dvd_mul`.  The missing lemma that lifts the rational root
    theorem from degree 2 to all degrees. -/
theorem coprime_dvd_of_dvd_pow {p q : Nat} (hco : gcd213 q p = 1) :
    ∀ n, q ∣ p ^ (n + 1) → q ∣ p
  | 0,     h => by rwa [Nat.pow_one] at h
  | n + 1, h => by
      rw [Nat.pow_succ, Nat.mul_comm] at h
      exact coprime_dvd_of_dvd_pow hco n (coprime_dvd_of_dvd_mul hco h)

/-- ★★★★★ **Rational root theorem (all degrees), ℕ-native.**  The structural
    heart, abstracted: if `p/q` is in lowest terms and the cleared monic equation
    has the form `pⁿ⁺¹ + A = C` where `A`, `C` are the lower-degree parts — each a
    multiple of `q` (every lower term carries a factor `q^{≥1}`, so `q ∣ A`,
    `q ∣ C`) — then `q = 1`.  "ℤ is the integral closure of ℕ in ℚ", every degree.
    `rational_root_monic_deg2` is the `n = 1` instance with
    `A = a₁pq + a₀q²`, `C = c₁pq + c₀q²` (both manifestly `q`-divisible via
    `dvd_mul_q` / `dvd_mul_qq`). -/
theorem rational_root_monic {p q n A C : Nat} (hco : gcd213 p q = 1) (hq : 0 < q)
    (hA : q ∣ A) (hC : q ∣ C) (h : p ^ (n + 1) + A = C) : q = 1 := by
  have hpp : q ∣ p ^ (n + 1) := dvd_of_add_dvd_right hq (by rw [h]; exact hC) hA
  have hqp : q ∣ p :=
    coprime_dvd_of_dvd_pow (show gcd213 q p = 1 by rw [gcd213_comm]; exact hco) n hpp
  have hqq : q ∣ q := ⟨1, (Nat.mul_one q).symm⟩
  have hqg : q ∣ gcd213 p q := gcd213_greatest p q q hqp hqq
  rw [hco] at hqg
  obtain ⟨c, hc⟩ := hqg
  exact mul_eq_one_left q c hc.symm

/-- The degree-2 theorem as the `n = 1` instance of the general form — a
    subsumption witness: `rational_root_monic` genuinely covers the concrete
    polynomial case (`A`, `C` the `q`-divisible lower-degree sums). -/
theorem rational_root_monic_deg2_via_general {p q a1 a0 c1 c0 : Nat}
    (hco : gcd213 p q = 1) (hq : 0 < q)
    (h : p * p + (a1 * p * q + a0 * (q * q)) = c1 * p * q + c0 * (q * q)) : q = 1 :=
  rational_root_monic (n := 1) hco hq
    (dvd_add_213 q _ _ (dvd_mul_q q (a1 * p)) (dvd_mul_qq q a0))
    (dvd_add_213 q _ _ (dvd_mul_q q (c1 * p)) (dvd_mul_qq q c0))
    (by rw [Nat.pow_succ, Nat.pow_one]; exact h)

end E213.Meta.Nat.RationalRoot
