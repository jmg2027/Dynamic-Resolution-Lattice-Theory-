import E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge
import E213.Lib.Math.NumberTheory.FactorialLcmDvd
import E213.Meta.Nat.MulMod213

/-!
# The Gauss–Jacobi reindex index identity (∅-axiom, Phase A3 / route b)

For the Gauss-square coefficient `(g⋆g)(n) = Σ_i χ_ω(i)·χ_ω((n+p−i)%p)`, the multiplicative reindex
`i = (n·t)%p` needs the inner index

  `(n + p − (n·t)%p) % p = (n · ((1 + (p − t)) % p)) % p`   (`gj_index`),

i.e. `n − n·t ≡ n·(1 − t) (mod p)`.  The crux is the modular negation `(n·(p−t))%p = p − (n·t)%p`
(`ZolotarevMuBridge.neg_mul_mod`); the rest is `add_sub_assoc` + `mod_add_mod` bookkeeping.  This is the
reindex that turns `(g⋆g)(n)` into `χ_ω(n)²·J` (the Gauss–Jacobi relation `g(χ)² = J·g(χ²)`).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiIndex

open E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge (neg_mul_mod)
open E213.Lib.Math.NumberTheory.FactorialLcmDvd (le_of_dvd_pos)
open E213.Meta.Nat.MulMod213 (mul_mod_right_pure)
open E213.Meta.Nat.AddMod213 (mod_add_mod)
open E213.Tactic.NatHelper (add_sub_assoc)

/-- `¬ p ∣ n` for `1 ≤ n < p`. -/
theorem not_dvd_of_pos_lt {p n : Nat} (hn1 : 1 ≤ n) (hnp : n < p) : ¬ p ∣ n :=
  fun h => absurd (le_of_dvd_pos hn1 h) (Nat.not_le.mpr hnp)

/-- ★★★★ **The Gauss–Jacobi reindex index** — for `1 ≤ n, t < p` with `p ∤ n`,
    `(n + p − (n·t)%p) % p = (n · ((1 + (p − t)) % p)) % p`.  Modular negation `neg_mul_mod`
    (`(n·(p−t))%p = p − (n·t)%p`) plus `add_sub_assoc` / `mod_add_mod`.  ∅-axiom. -/
theorem gj_index {p n t : Nat} (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpn : ¬ p ∣ n) (ht1 : 1 ≤ t) (htp : t < p) :
    (n + p - (n * t) % p) % p = (n * ((1 + (p - t)) % p)) % p := by
  have hppos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hnm : (n * (p - t)) % p = p - (n * t) % p := neg_mul_mod n p t hp hpr hnpn ht1 htp
  rw [← mul_mod_right_pure n (1 + (p - t)) p,
      show n * (1 + (p - t)) = n + n * (p - t) from by rw [Nat.mul_add, Nat.mul_one],
      add_sub_assoc n (Nat.le_of_lt (Nat.mod_lt (n * t) hppos)), ← hnm,
      Nat.add_comm n ((n * (p - t)) % p), mod_add_mod hppos (n * (p - t)) n,
      Nat.add_comm (n * (p - t)) n]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussJacobiIndex
