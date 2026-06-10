import E213.Lib.Math.NumberTheory.ModArith.OrderPow
import E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative

/-!
# CoprimeOrder — `gcd(ord a, ord b) = 1 ⟹ ord(a·b) = ord a · ord b`

Brick 3 of the primitive-root marathon: the multiplicative order of a product of elements with
**coprime orders** is the product of the orders.

  * ★★★ `ord_mul_coprime` — for units `a, b` with `gcd(ordModP a p, ordModP b p) = 1`,
    `ordModP ((a·b) % p) p = ordModP a p · ordModP b p`.

`γ ∣ αβ` is the product collapse `(aᵅ)ᵝ·(bᵝ)ᵅ ≡ 1`; `α ∣ γ` and `β ∣ γ` come from
`(ab)^{γβ} ≡ 1 ⟹ a^{γβ} ≡ 1 ⟹ α ∣ γβ` (`euclid_of_coprime`); then `αβ = lcm(α,β) ∣ γ`
(brick 1's `lcm_dvd` + `gcd_mul_lcm`).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.CoprimeOrder

open E213.Lib.Math.NumberTheory.ModArith.MulOrder (ordModP pow_ord ord_pos ord_dvd)
open E213.Lib.Math.NumberTheory.ModArith.OrderPow (ord_mod_eq)
open E213.Lib.Math.NumberTheory.Lcm213 (lcm213 lcm_dvd gcd_mul_lcm)
open E213.Meta.Nat.Gcd213 (dvd_antisymm_213 gcd213_comm)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Meta.Nat.AddMod213 (mod_mod)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (pow_mul_loc euclid_of_coprime)
open E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative (mul_pow_loc)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Tactic.NatHelper (gcd213)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- `gcd(α,β) = 1 ∧ α∣γ ∧ β∣γ ⟹ αβ ∣ γ` (via `lcm = αβ`). -/
private theorem coprime_mul_dvd (α β γ : Nat) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hco : gcd213 α β = 1) (hαγ : α ∣ γ) (hβγ : β ∣ γ) : α * β ∣ γ := by
  have hlcm : lcm213 α β = α * β := by
    have h := gcd_mul_lcm α β hα0; rw [hco, Nat.one_mul] at h; exact h
  rw [← hlcm]; exact lcm_dvd α β γ hα0 hβ0 hαγ hβγ

/-- `α ∣ γ` from `α ∣ β·γ` with `gcd(α,β) = 1` (handles `α = 1`). -/
private theorem dvd_of_coprime_mul (α β γ : Nat) (hα0 : 0 < α) (hco : gcd213 α β = 1)
    (hd : α ∣ β * γ) : α ∣ γ := by
  rcases Nat.lt_or_ge α 2 with h2 | h2
  · have : α = 1 := Nat.le_antisymm (Nat.le_of_lt_succ h2) hα0
    rw [this]; exact Nat.one_dvd γ
  · exact euclid_of_coprime β γ α h2 ((gcd213_comm α β) ▸ hco) hd

/-- ★★★ **Coprime-product order.**  For units `a, b` (`1 ≤ · < p`, `p` prime) with
    `gcd(ordModP a p, ordModP b p) = 1`, `ordModP ((a·b) % p) p = ordModP a p · ordModP b p`. -/
theorem ord_mul_coprime (a b p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) (hb0 : 0 < b) (hblt : b < p)
    (hco : gcd213 (ordModP a p) (ordModP b p) = 1) :
    ordModP ((a * b) % p) p = ordModP a p * ordModP b p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hna : ¬ p ∣ a := fun h => absurd (le_of_dvd_pos p a ha0 h) (Nat.not_le.mpr halt)
  have hnb : ¬ p ∣ b := fun h => absurd (le_of_dvd_pos p b hb0 h) (Nat.not_le.mpr hblt)
  have hnab : ¬ p ∣ (a * b) := fun h => (nat_prime_dvd_mul p hp hpr a b h).elim hna hnb
  have hab0 : 0 < (a * b) % p :=
    Nat.pos_of_ne_zero (fun h0 => hnab (E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero h0))
  have hablt : (a * b) % p < p := Nat.mod_lt _ hppos
  -- abbreviations
  obtain ⟨α, hαdef⟩ : ∃ x, ordModP a p = x := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ x, ordModP b p = x := ⟨_, rfl⟩
  have hα0 : 0 < α := hαdef ▸ ord_pos a p hp hpr ha0 halt
  have hβ0 : 0 < β := hβdef ▸ ord_pos b p hp hpr hb0 hblt
  have hco' : gcd213 α β = 1 := by rw [← hαdef, ← hβdef]; exact hco
  have haα : a ^ α % p = 1 := by rw [← hαdef]; exact pow_ord a p hp hpr ha0 halt
  have hbβ : b ^ β % p = 1 := by rw [← hβdef]; exact pow_ord b p hp hpr hb0 hblt
  -- helpers
  have pow_mul_one : ∀ (x m n : Nat), x ^ m % p = 1 → x ^ (m * n) % p = 1 := by
    intro x m n h
    rw [pow_mul_loc x m n, pow_mod_base (x ^ m) p n, h, Nat.one_pow]
    exact Nat.mod_eq_of_lt hp
  have hcm : ∀ m, ((a * b) % p) ^ m % p = (a ^ m * b ^ m) % p := by
    intro m; rw [← pow_mod_base (a * b) p m, mul_pow_loc a b m]
  -- (1) γ ∣ α·β
  have hd1 : ordModP ((a * b) % p) p ∣ α * β := by
    apply ord_dvd ((a * b) % p) p hp hpr hab0 hablt
    rw [hcm (α * β), mul_mod_pure (a ^ (α * β)) (b ^ (α * β)) p,
        pow_mul_one a α β haα,
        show b ^ (α * β) = b ^ (β * α) from by rw [Nat.mul_comm], pow_mul_one b β α hbβ,
        Nat.one_mul]
    exact Nat.mod_eq_of_lt hp
  -- the order of the product
  obtain ⟨γ, hγdef⟩ : ∃ x, ordModP ((a * b) % p) p = x := ⟨_, rfl⟩
  have hcγ : ((a * b) % p) ^ γ % p = 1 := by rw [← hγdef]; exact pow_ord ((a * b) % p) p hp hpr hab0 hablt
  -- (2a) α ∣ γ:  a^(γβ) ≡ (ab)^(γβ) ≡ 1
  have hαγ : α ∣ γ := by
    have hcgb : ((a * b) % p) ^ (γ * β) % p = 1 := pow_mul_one ((a * b) % p) γ β hcγ
    have hagb : a ^ (γ * β) % p = 1 := by
      have h := hcgb
      rw [hcm (γ * β), mul_mod_pure (a ^ (γ * β)) (b ^ (γ * β)) p,
          show b ^ (γ * β) = b ^ (β * γ) from by rw [Nat.mul_comm], pow_mul_one b β γ hbβ,
          Nat.mul_one, mod_mod] at h
      exact h
    have hαgb : α ∣ (γ * β) := by rw [← hαdef]; exact ord_dvd a p hp hpr ha0 halt (γ * β) hagb
    exact dvd_of_coprime_mul α β γ hα0 hco' (by rw [Nat.mul_comm β γ]; exact hαgb)
  -- (2b) β ∣ γ:  b^(γα) ≡ (ab)^(γα) ≡ 1
  have hβγ : β ∣ γ := by
    have hcga : ((a * b) % p) ^ (γ * α) % p = 1 := pow_mul_one ((a * b) % p) γ α hcγ
    have hbga : b ^ (γ * α) % p = 1 := by
      have h := hcga
      rw [hcm (γ * α), mul_mod_pure (a ^ (γ * α)) (b ^ (γ * α)) p,
          show a ^ (γ * α) = a ^ (α * γ) from by rw [Nat.mul_comm], pow_mul_one a α γ haα,
          Nat.one_mul, mod_mod] at h
      exact h
    have hβga : β ∣ (γ * α) := by rw [← hβdef]; exact ord_dvd b p hp hpr hb0 hblt (γ * α) hbga
    exact dvd_of_coprime_mul β α γ hβ0 ((gcd213_comm α β) ▸ hco') (by rw [Nat.mul_comm α γ]; exact hβga)
  -- assemble: γ = α·β
  rw [hγdef, hαdef, hβdef]
  exact dvd_antisymm_213 _ _ (hγdef ▸ hd1) (coprime_mul_dvd α β γ hα0 hβ0 hco' hαγ hβγ)

end E213.Lib.Math.NumberTheory.ModArith.CoprimeOrder
