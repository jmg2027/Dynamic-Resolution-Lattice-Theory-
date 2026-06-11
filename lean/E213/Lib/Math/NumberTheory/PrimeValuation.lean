import E213.Meta.Nat.Valuation
import E213.Meta.Nat.Gcd213
import E213.Lib.Math.NumberTheory.Lcm213

/-!
# PrimeValuation — `vₚ` is additive over products, ∅-axiom

The `q`-adic valuation `vp` (`Meta/Nat/Valuation.lean`) becomes a group homomorphism
`ℕ_{>0} → ℕ` exactly at **primes**: `vₚ(a·b) = vₚ a + vₚ b`.  This is the foundational
gear for Legendre's factorial formula `vₚ(n!) = Σⱼ ⌊n/pʲ⌋` (the per-prime bucketing
that the ζ(3) lcm-bound brick's key-divisibility step folds the counting lemma
`LcmGrowthChebyshev.count30` through).

Primality enters in exactly one place — Euclid's lemma `p ∣ a·b → p ∣ a ∨ p ∣ b`
(`prime_dvd_mul`) — routed through the Bezout-free `Gcd213.coprime_dvd_of_dvd_mul`
via "a divisor of a prime is `1` or the prime itself".  Everything else is the
exact-valuation bookkeeping: extract the unit part `a = pᵅ·u` with `p ∤ u`, then
`a·b = p^{α+β}·(u·v)` with `p ∤ u·v`.

  * `Prime213 p` — `2 ≤ p ∧ (∀ d, d ∣ p → d = 1 ∨ d = p)`.
  * `prime_dvd_mul` — Euclid's lemma at a prime.
  * ★★★ `vp_mul` — `vₚ(a·b) = vₚ a + vₚ b` (`p` prime, `a,b > 0`).

All zero-axiom (no `propext`: pure `pow_add`/4-factor swap from `NatHelper`'s
`mul_assoc`/`mul_left_comm`, not `Nat.pow_add`/`Nat.mul_mul_mul_comm`).
-/

namespace E213.Lib.Math.NumberTheory.PrimeValuation

open E213.Meta.Nat.Valuation (vp pow_vp_dvd vp_not_dvd_succ le_vp_iff pow_dvd_of_le dtrans
  mod_zero_of_dvd)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right gcd213_greatest coprime_dvd_of_dvd_mul)
open E213.Lib.Math.NumberTheory.Lcm213 (lcm213 gcd_pos lcm_pos gcd_mul_lcm)
open E213.Tactic.NatHelper (gcd213 mul_assoc mul_left_comm add_left_cancel_pure)

/-! ## §0 — pure arithmetic helpers (the core analogues carry `propext`) -/

/-- Pure `p^(m+n) = p^m · p^n` (`Nat.pow_add` carries `propext`). -/
private theorem pow_add_pure (p m : Nat) : ∀ n, p ^ (m + n) = p ^ m * p ^ n
  | 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | n + 1 => by
    rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, pow_add_pure p m n, mul_assoc]

/-- Pure 4-factor swap `a·b·(c·d) = a·c·(b·d)` (`Nat.mul_mul_mul_comm` carries
    `propext`). -/
private theorem mul4_swap (a b c d : Nat) : a * b * (c * d) = a * c * (b * d) := by
  rw [mul_assoc, mul_left_comm b c d, ← mul_assoc]

/-! ## §1 — primality and Euclid's lemma -/

/-- A prime is `≥ 2` and has only the trivial divisors. -/
def Prime213 (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- A prime not dividing `u` is coprime to it: `gcd p u ∣ p` is `1` or `p`, and `p`
    would force `p ∣ u`. -/
theorem prime_coprime_of_not_dvd {p u : Nat} (hp : Prime213 p) (h : ¬ p ∣ u) :
    gcd213 p u = 1 := by
  rcases hp.2 _ (gcd213_dvd_left p u) with h1 | hpe
  · exact h1
  · exact absurd (hpe ▸ gcd213_dvd_right p u) h

/-- ★★ **Euclid's lemma at a prime**: `p ∣ a·b → p ∣ a ∨ p ∣ b`.  If `p ∤ a` then
    `gcd p a = 1`, and `Gcd213.coprime_dvd_of_dvd_mul` carries the divisibility onto
    `b`. -/
theorem prime_dvd_mul {p a b : Nat} (hp : Prime213 p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  -- case on `a % p = 0` (pure `decEq`, not the propext-carrying `Decidable (·∣·)`)
  by_cases ha : a % p = 0
  · exact Or.inl (dvd_of_mod_eq_zero ha)
  · refine Or.inr (coprime_dvd_of_dvd_mul (prime_coprime_of_not_dvd hp ?_) h)
    exact fun hpa => ha (mod_zero_of_dvd hp0 hpa)

/-! ## §2 — exact-valuation bookkeeping -/

/-- Left-cancellation of a positive factor in a divisibility. -/
private theorem dvd_of_mul_dvd_mul_left {c x y : Nat} (hc : 0 < c) (h : c * x ∣ c * y) :
    x ∣ y := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, Nat.eq_of_mul_eq_mul_left hc (by rw [hw]; exact mul_assoc c x w)⟩

/-- The unit part `a / pᵛ` is not divisible by `p` (else `p^{v+1} ∣ a`). -/
private theorem unit_not_dvd {p a u : Nat} (hp : Prime213 p) (ha : 0 < a)
    (hu : a = p ^ (vp p a) * u) : ¬ p ∣ u := by
  intro hdu
  obtain ⟨w, hw⟩ := hdu
  refine vp_not_dvd_succ p a hp.1 ha ⟨w, ?_⟩
  calc a = p ^ (vp p a) * u := hu
    _ = p ^ (vp p a) * (p * w) := by rw [hw]
    _ = p ^ (vp p a + 1) * w := by rw [Nat.pow_succ]; exact (mul_assoc _ _ _).symm

/-- ★★★ **`vₚ` is additive over products** at a prime: `vₚ(a·b) = vₚ a + vₚ b`
    (`a, b > 0`).  Lower bound from `p^{α}·p^{β} = p^{α+β} ∣ a·b`; upper bound from
    `a·b = p^{α+β}·(u·v)` with `p ∤ u·v` (Euclid), so `p^{α+β+1} ∤ a·b`. -/
theorem vp_mul {p a b : Nat} (hp : Prime213 p) (ha : 0 < a) (hb : 0 < b) :
    vp p (a * b) = vp p a + vp p b := by
  have hq : 2 ≤ p := hp.1
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hq
  have hab : 0 < a * b := Nat.mul_pos ha hb
  obtain ⟨u, hu⟩ := pow_vp_dvd p a
  obtain ⟨v, hv⟩ := pow_vp_dvd p b
  have hpu : ¬ p ∣ u := unit_not_dvd hp ha hu
  have hpv : ¬ p ∣ v := unit_not_dvd hp hb hv
  -- lower bound: p^{α+β} ∣ a·b
  have hlow : p ^ (vp p a + vp p b) ∣ a * b := by
    obtain ⟨ca, hca⟩ := pow_vp_dvd p a
    obtain ⟨cb, hcb⟩ := pow_vp_dvd p b
    refine ⟨ca * cb, ?_⟩
    calc a * b = (p ^ (vp p a) * ca) * (p ^ (vp p b) * cb) := by rw [← hca, ← hcb]
      _ = p ^ (vp p a + vp p b) * (ca * cb) := by rw [pow_add_pure]; exact mul4_swap _ _ _ _
  -- p^{α+β+1} ∤ a·b
  have hhigh : ¬ p ^ (vp p a + vp p b + 1) ∣ a * b := by
    intro hdv
    have hab_eq : a * b = p ^ (vp p a + vp p b) * (u * v) := by
      calc a * b = (p ^ (vp p a) * u) * (p ^ (vp p b) * v) := by rw [← hu, ← hv]
        _ = p ^ (vp p a + vp p b) * (u * v) := by rw [pow_add_pure]; exact mul4_swap _ _ _ _
    rw [hab_eq, show p ^ (vp p a + vp p b + 1) = p ^ (vp p a + vp p b) * p from by
      rw [Nat.pow_succ]] at hdv
    have hpuv : p ∣ u * v := dvd_of_mul_dvd_mul_left (Nat.pos_pow_of_pos _ hp0) hdv
    rcases prime_dvd_mul hp hpuv with h | h
    · exact hpu h
    · exact hpv h
  -- assemble: lower bound + (vp ≤ α+β from ¬p^{α+β+1}∣ via le_vp_iff's contrapositive)
  refine Nat.le_antisymm ?_ ((le_vp_iff p (a * b) _ hq hab).mp hlow)
  exact Nat.le_of_lt_succ (Nat.lt_of_not_le
    (mt (le_vp_iff p (a * b) (vp p a + vp p b + 1) hq hab).mpr hhigh))

/-! ## §3 — `vₚ` on gcd / lcm: monotone, `min`, `max`

The lcm-side companion to Legendre.  `vₚ` is monotone under `∣` (from `le_vp_iff`),
`vₚ(gcd) = min` and `vₚ(lcm) = max` (the latter from the former + the product
identity `gcd·lcm = a·b`, dodging Nat subtraction).  `min`/`max` are written as
explicit `if` to avoid the `propext`-carrying `Nat.min_*`/`Nat.max_*` lemmas. -/

/-- `vₚ` is monotone under divisibility: `a ∣ b → vₚ a ≤ vₚ b` (`b > 0`). -/
theorem vp_monotone {p a b : Nat} (hp : Prime213 p) (hb : 0 < b) (hdvd : a ∣ b) :
    vp p a ≤ vp p b :=
  (le_vp_iff p b (vp p a) hp.1 hb).mp (dtrans (pow_vp_dvd p a) hdvd)

/-- `vₚ(gcd a b) = min (vₚ a) (vₚ b)` (`a, b > 0`), `min` as explicit `if`. -/
theorem vp_gcd_min {p a b : Nat} (hp : Prime213 p) (ha : 0 < a) (hb : 0 < b) :
    vp p (gcd213 a b) = if vp p a ≤ vp p b then vp p a else vp p b := by
  have hg : 0 < gcd213 a b := gcd_pos a b ha
  have h1 : vp p (gcd213 a b) ≤ vp p a := vp_monotone hp ha (gcd213_dvd_left a b)
  have h2 : vp p (gcd213 a b) ≤ vp p b := vp_monotone hp hb (gcd213_dvd_right a b)
  by_cases hab : vp p a ≤ vp p b
  · rw [if_pos hab]
    refine Nat.le_antisymm h1 ?_
    exact (le_vp_iff p (gcd213 a b) (vp p a) hp.1 hg).mp
      (gcd213_greatest a b _ (pow_vp_dvd p a) ((le_vp_iff p b (vp p a) hp.1 hb).mpr hab))
  · rw [if_neg hab]
    refine Nat.le_antisymm h2 ?_
    have hvba : vp p b ≤ vp p a := Nat.le_of_lt (Nat.lt_of_not_le hab)
    exact (le_vp_iff p (gcd213 a b) (vp p b) hp.1 hg).mp
      (gcd213_greatest a b _ ((le_vp_iff p a (vp p b) hp.1 ha).mpr hvba) (pow_vp_dvd p b))

/-- ★★ **`vₚ(lcm a b) = max (vₚ a) (vₚ b)`** (`a, b > 0`), `max` as explicit `if`.
    From `vₚ(gcd)+vₚ(lcm) = vₚ(a·b) = vₚa+vₚb` (the product identity `gcd·lcm=a·b`
    + `vp_mul`) and `vₚ(gcd) = min`, cancelling. -/
theorem vp_lcm_max {p a b : Nat} (hp : Prime213 p) (ha : 0 < a) (hb : 0 < b) :
    vp p (lcm213 a b) = if vp p a ≤ vp p b then vp p b else vp p a := by
  have hg : 0 < gcd213 a b := gcd_pos a b ha
  have hl : 0 < lcm213 a b := lcm_pos a b ha hb
  have hmul : vp p (gcd213 a b) + vp p (lcm213 a b) = vp p a + vp p b := by
    calc vp p (gcd213 a b) + vp p (lcm213 a b)
        = vp p (gcd213 a b * lcm213 a b) := (vp_mul hp hg hl).symm
      _ = vp p (a * b) := by rw [gcd_mul_lcm a b ha]
      _ = vp p a + vp p b := vp_mul hp ha hb
  have hgmin := vp_gcd_min hp ha hb
  by_cases hab : vp p a ≤ vp p b
  · rw [if_pos hab]; rw [if_pos hab] at hgmin; rw [hgmin] at hmul
    exact add_left_cancel_pure hmul
  · rw [if_neg hab]; rw [if_neg hab] at hgmin; rw [hgmin] at hmul
    rw [Nat.add_comm (vp p a) (vp p b)] at hmul
    exact add_left_cancel_pure hmul

end E213.Lib.Math.NumberTheory.PrimeValuation
