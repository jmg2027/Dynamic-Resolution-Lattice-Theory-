import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertForm
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative

/-!
# A rational prime `q ≡ 2 (mod 3)` is prime in `ℤ[ω]` — `ℤ[ω]/(q) ≅ 𝔽_{q²}` (∅-axiom)

★★★★★ `inert_norm_prime_euclid` : for a rational prime `q ≡ 2 (mod 3)` (inert in `ℤ[ω]`),
`q ∣ αβ ⟹ q ∣ α ∨ q ∣ β` in `ℤ[ω]`.

The Euclidean gcd `d = s·α + t·q` of `α, q` (`gcd_bezout`) has `‖d‖² ∣ ‖q‖² = q²`, so `‖d‖² ∈ {1,q,q²}`
(`dvd_prime_sq`).  The middle value `‖d‖² = q` is **forbidden** (`normSq_ne_of_mod3_two`: the inert
obstruction — `q ≡ 2 (mod 3)` is a value of no Eisenstein norm), leaving the same dichotomy as the
split case:

  * `‖d‖² = q²` — `d` is an associate of `q` (`dvd_of_associate`), so `q ∣ d ∣ α`;
  * `‖d‖² = 1`  — `d` is a unit (Bezout ⟹ `q ∣ β`).

Hence `ℤ[ω]/(q)` is an integral domain (`inert_residue_no_zero_divisors`) — the field `𝔽_{q²}` the
cubic residue symbol `(π/q)₃` lives in.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertPrime

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd
  (normSq_dvd_of_dvd unit_of_normSq_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd
  (gcd_bezout zdvd_add ofInt_one_mul mul_ofInt_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (zdvd_trans)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime (dvd_of_associate)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertForm (normSq_ne_of_mod3_two)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Meta.Algebra213.Ring213 (mul_assoc add_mul add_zero)
open E213.Meta.Int213.OrderMul (natAbs_cast_of_nonneg ofNat_le_of_le)
open E213.Meta.Int213.Order (lt_of_lt_of_le)
open E213.Lib.Math.NumberTheory.PolyRoot (int_dvd_to_nat)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right gcd213_greatest gcd213_comm)
open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
  (coprime_mul_of_coprime eq_one_of_dvd_one)

/-- **Divisors of `q²` for a prime `q` are `1`, `q`, or `q²`.**  Split on `gcd(q,n) ∈ {1,q}`: coprime
    (`gcd = 1`) forces `n ∣ gcd(n, q²) = 1` so `n = 1`; `q ∣ n` writes `n = q·m`, and cancelling one `q`
    from `q·m ∣ q·q` gives `m ∣ q`, so `n ∈ {q, q²}`.  ∅-axiom. -/
theorem dvd_prime_sq (q : Nat) (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (hqpos : 0 < q)
    (n : Nat) (h : n ∣ q * q) : n = 1 ∨ n = q ∨ n = q * q := by
  rcases hqr (gcd213 q n) (gcd213_dvd_left q n) with hco | hqg
  · -- coprime: n ∣ gcd(n, q·q) = 1
    have hnq : gcd213 n q = 1 := (gcd213_comm q n).symm.trans hco
    have hnqq : gcd213 n (q * q) = 1 := coprime_mul_of_coprime hnq hnq
    have hng : n ∣ gcd213 n (q * q) :=
      gcd213_greatest n (q * q) n ⟨1, (Nat.mul_one n).symm⟩ h
    rw [hnqq] at hng
    exact Or.inl (eq_one_of_dvd_one hng)
  · -- q ∣ n
    have hqn : q ∣ n := hqg ▸ gcd213_dvd_right q n
    obtain ⟨m, hm⟩ := hqn
    rw [hm] at h
    obtain ⟨c, hc⟩ := h
    have hmc : q = m * c :=
      Nat.eq_of_mul_eq_mul_left hqpos (by rw [hc]; exact E213.Tactic.NatHelper.mul_assoc q m c)
    rcases hqr m ⟨c, hmc⟩ with hm1 | hmq
    · exact Or.inr (Or.inl (by rw [hm, hm1, Nat.mul_one]))
    · exact Or.inr (Or.inr (by rw [hm, hmq]))

/-- `‖ofInt z‖² = z²` — the rational integers embed with square norm (`⟨z,0⟩ ↦ z²`). -/
theorem ofInt_normSq (z : Int) : (ofInt z).normSq = z * z := by
  show z * z - z * 0 + 0 * 0 = z * z
  rw [Int.mul_zero, show (0 : Int) * 0 = 0 from by decide, Int.sub_eq_add_neg, Int.neg_zero,
      Int.add_zero, Int.add_zero]

/-- **The inert norm options** — for `q ≡ 2 (mod 3)` prime, a divisor of `‖q‖² = q²` has norm `1` or
    `q²`; norm `q` is excluded by the inert obstruction (`normSq_ne_of_mod3_two`).  ∅-axiom. -/
theorem inert_normSq_options {d : ZOmega} {q : Nat} (hq3 : q % 3 = 2)
    (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (hq1 : 1 < q)
    (hdq : d.normSq ∣ ((q : Int) * (q : Int))) :
    d.normSq = 1 ∨ d.normSq = (q : Int) * (q : Int) := by
  have hnn : (d.normSq.natAbs : Int) = d.normSq := natAbs_cast_of_nonneg (normSq_nonneg d)
  have hnat : d.normSq.natAbs ∣ (q * q) := by
    have hcast : (d.normSq.natAbs : Int) ∣ (((q * q : Nat)) : Int) := by
      rw [hnn]; exact hdq
    have hh := int_dvd_to_nat d.normSq.natAbs (((q * q : Nat)) : Int) hcast
    rwa [Int.natAbs_ofNat] at hh
  have hqpos : 0 < q := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hq1)
  rcases dvd_prime_sq q hqr hqpos d.normSq.natAbs hnat with h1 | hq | hq2
  · exact Or.inl (by rw [← hnn, h1]; rfl)
  · exact absurd (by rw [← hnn, hq] : d.normSq = (q : Int)) (normSq_ne_of_mod3_two hq3 d)
  · exact Or.inr (by rw [← hnn, hq2]; rfl)

/-- ★★★★★ **A rational prime `q ≡ 2 (mod 3)` is prime in `ℤ[ω]`** — `q ∣ αβ ⟹ q ∣ α ∨ q ∣ β`.
    The Euclidean gcd `d` of `α, q` has `‖d‖² ∈ {1, q²}` (`inert_normSq_options`, the inert obstruction
    kills `q`); `‖d‖² = q²` makes `d` an associate of `q` (`q ∣ d ∣ α`), `‖d‖² = 1` makes `d` a unit
    (Bezout ⟹ `q ∣ β`).  ∅-axiom, no excluded middle. -/
theorem inert_norm_prime_euclid {q : Nat} (hq3 : q % 3 = 2)
    (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (hq1 : 1 < q) {α β : ZOmega}
    (hdvd : ofInt (q : Int) ∣ α * β) : ofInt (q : Int) ∣ α ∨ ofInt (q : Int) ∣ β := by
  obtain ⟨d, s, t, hbez, hdα, hdπ⟩ :=
    gcd_bezout (ofInt (q : Int)).normSq.natAbs α (ofInt (q : Int)) (Nat.le_refl _)
  have hπnorm : (ofInt (q : Int)).normSq = (q : Int) * (q : Int) := ofInt_normSq (q : Int)
  have hdnorm : d.normSq ∣ ((q : Int) * (q : Int)) := by
    obtain ⟨c, hc⟩ := hdπ
    have h := normSq_dvd_of_dvd d (ofInt (q : Int)) c hc
    rwa [hπnorm] at h
  rcases inert_normSq_options hq3 hqr hq1 hdnorm with h1 | hq2
  · -- unit case: q ∣ β
    right
    have hunit : d * d.conj = ofInt 1 := unit_of_normSq_one d h1
    have hone : ofInt 1 = (s * α) * d.conj + (t * ofInt (q : Int)) * d.conj := by
      rw [← hunit, hbez, add_mul]
    have hβ : (s * α) * d.conj * β + (t * ofInt (q : Int)) * d.conj * β = β := by
      rw [← add_mul, ← hone, ofInt_one_mul]
    have dvd_mul_of : ∀ Y X : ZOmega, ofInt (q : Int) ∣ X → ofInt (q : Int) ∣ Y * X := by
      intro Y X hX
      obtain ⟨w, hw⟩ := hX
      exact ⟨Y * w, by rw [hw, ← mul_assoc, mul_comm Y (ofInt (q : Int)), mul_assoc]⟩
    have hterm1 : (s * α) * d.conj * β = (s * d.conj) * (α * β) := by
      rw [mul_assoc s α d.conj, mul_comm α d.conj, ← mul_assoc s d.conj α,
          mul_assoc (s * d.conj) α β]
    have hπ1 : ofInt (q : Int) ∣ (s * α) * d.conj * β := by
      rw [hterm1]; exact dvd_mul_of (s * d.conj) (α * β) hdvd
    have hterm2 : (t * ofInt (q : Int)) * d.conj * β = ofInt (q : Int) * (t * d.conj * β) := by
      rw [mul_comm t (ofInt (q : Int)), mul_assoc (ofInt (q : Int)) t d.conj,
          mul_assoc (ofInt (q : Int)) (t * d.conj) β]
    have hπ2 : ofInt (q : Int) ∣ (t * ofInt (q : Int)) * d.conj * β := ⟨t * d.conj * β, hterm2⟩
    rw [← hβ]; exact zdvd_add hπ1 hπ2
  · -- associate case: q ∣ α
    left
    have hpos : 0 < d.normSq := by
      rw [hq2]
      have h1q : (1 : Int) ≤ (((q * q : Nat)) : Int) :=
        ofNat_le_of_le (Nat.succ_le_of_lt (Nat.mul_pos
          (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hq1))
          (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hq1))))
      exact lt_of_lt_of_le (show (0 : Int) < 1 by decide) h1q
    have hπd : ofInt (q : Int) ∣ d := dvd_of_associate hdπ (hπnorm.trans hq2.symm) hpos
    exact zdvd_trans hπd hdα

/-- ★★★★★ **`ℤ[ω]/(q)` is an integral domain** for an inert prime `q ≡ 2 (mod 3)` — `αβ ≡ 0 (mod q)`
    forces `α ≡ 0` or `β ≡ 0`.  The residue-congruence reading of `inert_norm_prime_euclid`.
    ∅-axiom. -/
theorem inert_residue_no_zero_divisors {q : Nat} (hq3 : q % 3 = 2)
    (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (hq1 : 1 < q) {α β : ZOmega}
    (hab : ModEq (ofInt (q : Int)) (α * β) 0) :
    ModEq (ofInt (q : Int)) α 0 ∨ ModEq (ofInt (q : Int)) β 0 := by
  have hz0 : (-(0 : ZOmega)) = 0 := by decide
  have hdvd : ofInt (q : Int) ∣ α * β := by
    have h : ofInt (q : Int) ∣ (α * β + -0) := hab
    rwa [hz0, add_zero] at h
  rcases inert_norm_prime_euclid hq3 hqr hq1 hdvd with h | h
  · left;  show ofInt (q : Int) ∣ (α + -0); rw [hz0, add_zero]; exact h
  · right; show ofInt (q : Int) ∣ (β + -0); rw [hz0, add_zero]; exact h

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertPrime
