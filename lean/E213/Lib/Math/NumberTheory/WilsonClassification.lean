import E213.Lib.Math.NumberTheory.SqrtOnePrimePower
import E213.Lib.Math.NumberTheory.SqrtOneTwoPrimePower
import E213.Lib.Math.NumberTheory.WilsonExistence
import E213.Lib.Math.NumberTheory.OddPartDecomposition
import E213.Lib.Math.NumberTheory.ModArith.QPart
import E213.Lib.Math.NumberTheory.ModArith.ValuationAlg

/-!
# Gauss–Wilson `±1` classification capstone (∅-axiom scratch)

Assembles the landed Wilson keystones into the classification

  `∏(units of ℤ/n) ≡ −1 (mod n)  ⟺  n ∈ {1,2,4,pᵏ,2pᵏ}`  (the
  primitive-root moduli),  and  `≡ +1` otherwise (for `2 < n`).

`PrimitiveRootModulus` names the right-hand side.
-/

namespace E213.Lib.Math.NumberTheory.WilsonClassification

open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.EulerTheorem (totativeList)
open E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem (prodMod)
open E213.Lib.Math.NumberTheory.SqrtOnePrimePower (wilson_neg_one_prime_power)
open E213.Lib.Math.NumberTheory.SqrtOneTwoPrimePower
  (wilson_neg_one_two_prime_power wilson_neg_one_four)
open E213.Lib.Math.NumberTheory.WilsonExistence
  (wilson_plus_one_of_coprime_split wilson_plus_one_two_pow)
open E213.Lib.Math.NumberTheory.OddPartDecomposition
  (oddPart v2 decomp oddPart_odd oddPart_pos)
open E213.Lib.Math.NumberTheory.ModArith.QPart
  (qpart qpart_dvd qpart_pos q_not_dvd_quot gcd_qpow_qfree)
open E213.Lib.Math.NumberTheory.ModArith.ValuationAlg (one_le_vp)
open E213.Lib.Math.NumberTheory.PrimeFactorization (minFac minFac_div)
open E213.Lib.Math.NumberTheory.PrimesThreeModFour (minFac_isPrime)
open E213.Meta.Nat.Valuation (vp mod_zero_of_dvd dtrans)
open E213.Lib.Math.NumberTheory.Lcm213 (mul_div_cancel_of_dvd)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)

/-! ## §0 — the classification predicate -/

/-- **Primitive-root moduli** (those `n` for which `(ℤ/n)ˣ` is cyclic):
    `1, 2, 4, pᵏ` (odd prime power), `2pᵏ`. -/
def PrimitiveRootModulus (n : Nat) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 4 ∨
  (∃ p k, IsPrime213 p ∧ p % 2 = 1 ∧ 1 ≤ k ∧ n = p ^ k) ∨
  (∃ p k, IsPrime213 p ∧ p % 2 = 1 ∧ 1 ≤ k ∧ n = 2 * p ^ k)

/-! ## §1 — ★ the `⟸` direction (clean: pure assembly of landed keystones) -/

/-- ★ **Wilson `−1` for a primitive-root modulus.**  For `2 < n` with
    `PrimitiveRootModulus n`, `∏(units of ℤ/n) ≡ n−1 ≡ −1 (mod n)`.
    Case-split on the disjunction: `n=4` → `wilson_neg_one_four`;
    `n=pᵏ` → `wilson_neg_one_prime_power`; `n=2pᵏ` →
    `wilson_neg_one_two_prime_power`; `n∈{1,2}` excluded by `2<n`. -/
theorem prod_units_neg_one_of_primitive (n : Nat) (hn : 2 < n)
    (hpr : PrimitiveRootModulus n) :
    prodMod n (totativeList n) % n = (n - 1) % n := by
  rcases hpr with h1 | h2 | h4 | hpk | h2pk
  · exact absurd (h1 ▸ hn) (by decide)
  · exact absurd (h2 ▸ hn) (by decide)
  · -- n = 4
    rw [h4]
    show prodMod 4 (totativeList 4) % 4 = (4 - 1) % 4
    rw [wilson_neg_one_four]
  · -- n = pᵏ
    obtain ⟨p, k, hp, hodd, hk, hnpk⟩ := hpk
    subst hnpk
    exact wilson_neg_one_prime_power p k hp hodd hk hn
  · -- n = 2pᵏ
    obtain ⟨p, k, hp, hodd, hk, hn2pk⟩ := h2pk
    subst hn2pk
    exact wilson_neg_one_two_prime_power p k hp hodd hk hn

/-! ## §3 — the `⟹` direction (the factorization case-split, STRETCH)

For `2 < n` with `¬PrimitiveRootModulus n`, `∏(units) ≡ +1`.

**Spine** (`OddPartDecomposition`): `n = 2^e · m` with `m = oddPart n` odd,
`m > 0`, `e = v2 n`.

  * `m = 1` (`n = 2^e`): not primitive ⟹ `e ≥ 3`; use `wilson_plus_one_two_pow`.
  * `m > 1`: let `p = minFac m` (an odd prime, `p ≥ 3`), and split
    `(a,b) = (qpart p n, n / qpart p n) = (p^(vp p n), n / p^(vp p n))`.
    `gcd a b = 1` (`gcd_qpow_qfree`: `p` prime, `p ∤ b`), `a·b = n`, `a ≥ p ≥ 3`.
    `b ≤ 2` would force `n = p^k` (b=1) or `n = 2p^k` (b=2), both **primitive**;
    so non-primitivity gives `b > 2`.  Apply `wilson_plus_one_of_coprime_split`.

This **avoids prime-power detection entirely** — the same `(p-part, complement)`
split handles every non-2-power `n`; non-primitivity rules out the two small
complements. -/

/-- `p ∣ m`, `m` odd ⟹ `p % 2 = 1` (`p` even would put `2 ∣ m`). -/
theorem odd_of_dvd_odd {p m : Nat} (hpm : p ∣ m) (hm : m % 2 = 1) : p % 2 = 1 := by
  rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one p with h0 | h1
  · exfalso
    have h2p : (2 : Nat) ∣ p := dvd_of_mod_eq_zero h0
    have h2m : (2 : Nat) ∣ m := dtrans h2p hpm
    have : m % 2 = 0 := mod_zero_of_dvd (by decide) h2m
    rw [hm] at this; exact absurd this (by decide)
  · exact h1

/-- `minFac m` for `m ≥ 2`: prime (`IsPrime213`), `≥ 3` when `m` odd, divides `m`. -/
theorem minFac_odd_prime {m : Nat} (hm2 : 2 ≤ m) (hmodd : m % 2 = 1) :
    IsPrime213 (minFac m) ∧ minFac m % 2 = 1 ∧ minFac m ∣ m := by
  have hpr : IsPrime213 (minFac m) := minFac_isPrime hm2
  have hdvd : minFac m ∣ m := ⟨m / minFac m, (minFac_div hm2).1.symm⟩
  exact ⟨hpr, odd_of_dvd_odd hdvd hmodd, hdvd⟩

/-- ★★ **Constructive classification dichotomy.**  For `2 < n`, EITHER `n` is a
    primitive-root modulus, OR `∏(units of ℤ/n) ≡ 1 (mod n)`.  Each non-2-power
    `n` is split as `(p-part, complement)` with `p = minFac (oddPart n)`; the
    only complements `≤ 2` exhibit a primitivity witness (`pᵏ` / `2pᵏ`), every
    other `n` gives the `+1` product.  Fully constructive — no `Classical`, no
    `by_cases` on `PrimitiveRootModulus`. -/
theorem classify (n : Nat) (hn : 2 < n) :
    PrimitiveRootModulus n ∨ prodMod n (totativeList n) % n = 1 % n := by
  have hnpos : 0 < n := Nat.lt_trans (by decide) hn
  -- spine: n = 2^e · m, m = oddPart n odd, m > 0
  have hdec : n = 2 ^ v2 n * oddPart n := decomp hnpos
  have hmodd : oddPart n % 2 = 1 := oddPart_odd hnpos
  have hmpos : 0 < oddPart n := oddPart_pos hnpos
  -- case on oddPart n = 1 (n a power of 2) vs ≥ 2
  rcases Nat.lt_or_ge (oddPart n) 2 with hm1 | hm2
  · -- oddPart n = 1 : n = 2^e
    have hm_eq1 : oddPart n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hm1) hmpos
    have hn2e : n = 2 ^ v2 n := by
      have h := hdec               -- n = 2^(v2 n) * oddPart n
      rw [hm_eq1, Nat.mul_one] at h
      exact h
    -- with n = 2^(v2 n) and 2 < n, either v2 n ≥ 3 (→ +1) or n = 4 (→ primitive)
    rcases Nat.lt_or_ge (v2 n) 3 with hlt | hge
    · -- v2 n ≤ 2; 2 < n = 2^e forces e = 2, n = 4 : primitive
      left
      have he_le2 : v2 n ≤ 2 := Nat.le_of_lt_succ hlt
      have hge2 : 2 ≤ v2 n := by
        rcases Nat.lt_or_ge (v2 n) 2 with hlo | hhi
        · exfalso
          have : n ≤ 2 := by
            rw [hn2e]
            calc 2 ^ v2 n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ hlo)
              _ = 2 := by decide
          exact absurd (Nat.lt_of_lt_of_le hn this) (Nat.lt_irrefl 2)
        · exact hhi
      have he_eq2 : v2 n = 2 := Nat.le_antisymm he_le2 hge2
      have hn4 : n = 4 := by rw [hn2e, he_eq2]
      exact Or.inr (Or.inr (Or.inl hn4))
    · -- v2 n ≥ 3 : n = 2^e, +1
      right
      rw [hn2e]
      exact wilson_plus_one_two_pow (v2 n) hge
  · -- oddPart n ≥ 2 (odd, so ≥ 3): use the (p-part, complement) split
    obtain ⟨hp_pr, hp_odd, hp_dvd_m⟩ := minFac_odd_prime hm2 hmodd
    -- p := minFac (oddPart n)
    obtain ⟨p, hpdef⟩ : ∃ p, p = minFac (oddPart n) := ⟨_, rfl⟩
    rw [← hpdef] at hp_pr hp_odd hp_dvd_m
    have hp2 : 2 ≤ p := hp_pr.1
    have hp3 : 3 ≤ p := by
      rcases Nat.lt_or_ge p 3 with h | h
      · exfalso
        have hpe : p = 2 := Nat.le_antisymm (Nat.le_of_lt_succ h) hp2
        rw [hpe] at hp_odd; exact absurd hp_odd (by decide)
      · exact h
    -- p ∣ n  (p ∣ oddPart n ∣ n)
    have hm_dvd_n : oddPart n ∣ n :=
      ⟨2 ^ v2 n, by rw [Nat.mul_comm (oddPart n) (2 ^ v2 n)]; exact hdec⟩
    have hp_dvd_n : p ∣ n := dtrans hp_dvd_m hm_dvd_n
    -- protect the exponent E := vp p n (so later `n`-rewrites don't touch it)
    obtain ⟨E, hE⟩ : ∃ E, vp p n = E := ⟨_, rfl⟩
    -- a := qpart p n = p^E, b := n / a
    obtain ⟨a, hadef⟩ : ∃ a, a = qpart p n := ⟨_, rfl⟩
    have ha_pE : a = p ^ E := by rw [hadef]; show p ^ vp p n = p ^ E; rw [hE]
    obtain ⟨b, hbdef⟩ : ∃ b, b = n / a := ⟨_, rfl⟩
    have ha_dvd : a ∣ n := hadef ▸ qpart_dvd p n
    have hapos : 0 < a := hadef ▸ qpart_pos p n hp2
    have hab : a * b = n := by rw [hbdef]; exact mul_div_cancel_of_dvd a n hapos ha_dvd
    -- a = p^E, with E ≥ 1
    have hvp1 : 1 ≤ E := hE ▸ one_le_vp p n hp2 hnpos hp_dvd_n
    have ha_ge_p : p ≤ a := by
      rw [ha_pE]
      have : p ^ 1 ≤ p ^ E := Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hp2) hvp1
      rwa [Nat.pow_one] at this
    have ha2 : 2 < a := Nat.lt_of_lt_of_le hp3 ha_ge_p
    -- p ∤ b ⟹ gcd a b = 1
    have hp_not_dvd_b : ¬ p ∣ b := by rw [hbdef, hadef]; exact q_not_dvd_quot p n hp2 hnpos
    have hcop : gcd213 a b = 1 := by
      rw [ha_pE]; exact gcd_qpow_qfree p E b hp2 hp_pr.2 hp_not_dvd_b
    -- b > 0
    have hbpos : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h0 | hpos
      · exfalso
        rw [h0, Nat.mul_zero] at hab  -- hab : 0 = n
        rw [← hab] at hnpos           -- hnpos : 0 < 0
        exact absurd hnpos (Nat.lt_irrefl 0)
      · exact hpos
    -- b ∈ {1,2} ⟹ primitive witness; else b > 2 ⟹ coprime split ⟹ +1
    rcases Nat.lt_or_ge b 3 with hblt | hbge
    · -- 0 < b < 3 ⟹ b = 1 ∨ b = 2 — both give a primitivity witness
      left
      have hble2 : b ≤ 2 := Nat.le_of_lt_succ hblt
      have hb12 : b = 1 ∨ b = 2 := by
        rcases Nat.lt_or_ge b 2 with hlo | hhi
        · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hlo) hbpos)
        · exact Or.inr (Nat.le_antisymm hble2 hhi)
      rcases hb12 with hb1 | hb2'
      · -- b = 1 ⟹ n = a*1 = a = p^E
        have hna : n = p ^ E := by rw [← hab, hb1, Nat.mul_one, ha_pE]
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, E, hp_pr, hp_odd, hvp1, hna⟩)))
      · -- b = 2 ⟹ n = a*2 = 2·p^E
        have hna : n = 2 * p ^ E := by
          rw [← hab, hb2', ha_pE, Nat.mul_comm (p ^ E) 2]
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, E, hp_pr, hp_odd, hvp1, hna⟩)))
    · -- b ≥ 3 : coprime split (a,b), both > 2 ⟹ +1
      right
      rw [← hab]
      exact wilson_plus_one_of_coprime_split a b ha2 hbge hcop

/-- ★★ **The `⟹` direction** (corollary of `classify`).  For `2 < n` with
    `¬PrimitiveRootModulus n`, `∏(units of ℤ/n) ≡ 1 (mod n)`. -/
theorem prod_units_plus_one_of_not_primitive (n : Nat) (hn : 2 < n)
    (hnp : ¬ PrimitiveRootModulus n) :
    prodMod n (totativeList n) % n = 1 % n := by
  rcases classify n hn with hpr | hplus
  · exact absurd hpr hnp
  · exact hplus

/-! ## §4 — ★ the full classification (the iff) -/

/-- ★ **The Gauss–Wilson `±1` classification.**  For `2 < n`,
    `∏(units of ℤ/n) ≡ −1 (mod n)  ⟺  PrimitiveRootModulus n`.
    The two product-values `(n−1)%n` and `1%n` are distinct for `n > 2`,
    so the equivalence is well-posed. -/
theorem prod_units_neg_one_iff (n : Nat) (hn : 2 < n) :
    prodMod n (totativeList n) % n = (n - 1) % n ↔ PrimitiveRootModulus n := by
  constructor
  · -- ⟹ : via the constructive dichotomy `classify` (no `Classical`/`by_cases`)
    intro hval
    rcases classify n hn with hpr | hplus
    · exact hpr
    · -- prod ≡ 1 and prod ≡ (n-1): the two values differ for n > 2 — contradiction
      exfalso
      rw [hplus] at hval  -- hval : 1 % n = (n-1) % n
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, (E213.Tactic.NatHelper.sub_add_cancel hn).symm⟩
      have h1 : (1 : Nat) % (m + 3) = 1 :=
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 3 m))
      have hn1 : (m + 3 - 1) % (m + 3) = m + 2 := by
        show (m + 2) % (m + 3) = m + 2
        exact Nat.mod_eq_of_lt (Nat.lt_succ_self (m + 2))
      rw [h1, hn1] at hval  -- hval : 1 = m + 2
      have : (2 : Nat) ≤ 1 := hval ▸ Nat.le_add_left 2 m
      exact absurd this (by decide)
  · exact prod_units_neg_one_of_primitive n hn

/-! ## §2 — smokes (`decide` on closed numerals) -/

/-- `IsPrime213 3` (∅-axiom): `minFac 3 = 3` reduces, then `minFac_isPrime`. -/
theorem isPrime213_3 : IsPrime213 3 := by
  have h := E213.Lib.Math.NumberTheory.PrimesThreeModFour.minFac_isPrime
    (n := 3) (by decide)
  have he : E213.Lib.Math.NumberTheory.PrimeFactorization.minFac 3 = 3 := by decide
  rwa [he] at h

/-- `IsPrime213 5` (∅-axiom). -/
theorem isPrime213_5 : IsPrime213 5 := by
  have h := E213.Lib.Math.NumberTheory.PrimesThreeModFour.minFac_isPrime
    (n := 5) (by decide)
  have he : E213.Lib.Math.NumberTheory.PrimeFactorization.minFac 5 = 5 := by decide
  rwa [he] at h

/-- `PrimitiveRootModulus 9` (`= 3²`). -/
theorem prim_9 : PrimitiveRootModulus 9 :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨3, 2, isPrime213_3, by decide, by decide, by decide⟩)))

/-- `PrimitiveRootModulus 25` (`= 5²`). -/
theorem prim_25 : PrimitiveRootModulus 25 :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨5, 2, isPrime213_5, by decide, by decide, by decide⟩)))

/-- `PrimitiveRootModulus 18` (`= 2·3²`). -/
theorem prim_18 : PrimitiveRootModulus 18 :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨3, 2, isPrime213_3, by decide, by decide, by decide⟩)))

/-- Classification value at `n = 9` (`≡ −1`): `∏ units ≡ 8 (mod 9)`. -/
theorem class_9 :
    prodMod 9 (totativeList 9) % 9 = (9 - 1) % 9 :=
  prod_units_neg_one_of_primitive 9 (by decide) prim_9

/-- The full iff at `n = 9` (`≡ −1` ⟺ primitive): `9` is primitive, so `≡ −1`. -/
theorem iff_9 :
    (prodMod 9 (totativeList 9) % 9 = (9 - 1) % 9) ↔ PrimitiveRootModulus 9 :=
  prod_units_neg_one_iff 9 (by decide)

/-- Classification value at `n = 15` (`≡ +1`): `15 = 3·5` is non-primitive, so
    `∏ units ≡ 1 (mod 15)`.  Verified by `decide` (the product is a closed
    numeral); matches the `⟹`/coprime-split branch (`classify` returns `+1`). -/
theorem class_15 :
    prodMod 15 (totativeList 15) % 15 = 1 % 15 := by decide

/-- The iff at `n = 15`, contrapositive form: `15` is NOT a primitive-root modulus
    (its `∏ units ≡ +1 ≠ −1`).  From `prod_units_neg_one_iff`: if `15` were
    primitive the product would be `≡ −1 ≡ 14`, but it is `1`. -/
theorem not_prim_15 : ¬ PrimitiveRootModulus 15 := by
  intro hpr
  have hneg : prodMod 15 (totativeList 15) % 15 = (15 - 1) % 15 :=
    (prod_units_neg_one_iff 15 (by decide)).mpr hpr
  rw [class_15] at hneg
  exact absurd hneg (by decide)

end E213.Lib.Math.NumberTheory.WilsonClassification


