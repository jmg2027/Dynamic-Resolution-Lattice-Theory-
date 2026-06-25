import E213.Lib.Math.Combinatorics.LucasStepGeneral
import E213.Lib.Math.NumberTheory.FactorialLcmProduct
import E213.Lib.Math.NumberTheory.LcmGrowthChebyshev
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.NatDiv213

/-!
# Lucas' theorem — the explicit base-`p` digit product (∅-axiom)

★★★★★ `lucas_digits` : for a prime `p` and `n < p^L`,

  `choose m n ≡ ∏_{i<L} choose ((m / p^i) % p) ((n / p^i) % p)  (mod p)`

— the **canonical form** of Lucas' theorem: the binomial coefficient mod `p` is the product of the
binomials of the base-`p` digits.  Built by iterating the recursive form
`LucasStepGeneral.lucas_div` (`choose m n ≡ choose (m/p) (n/p) · choose (m%p) (n%p)`) down the
quotient tower, with `L` ranging over enough digit positions to cover `n` (the unread high digits of
`m` pair with `n`'s zero digits, contributing factor `1`).

Reuses `FactorialLcmProduct.prodTo` (range product) with three generic Σ-style helpers
(`prodTo_congr`, `prodTo_split_first`, `prodTo_mod`).  The descent of the digit indices uses the pure
nested-floor `div_div_pure` (`m / p^{i+1} = (m/p) / p^i`).  ∅-axiom throughout.
-/

namespace E213.Lib.Math.Combinatorics.LucasDigitProduct

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_zero_right)
open E213.Lib.Math.Combinatorics.LucasStepGeneral (lucas_div)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberTheory.FactorialLcmProduct (prodTo)
open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev (div_div_pure)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.AddMod213 (mod_mod)
open E213.Meta.Nat.NatDiv213 (div_lt_of_lt_mul mul_div_cancel_left_pure)
open E213.Tactic.NatHelper (mul_assoc)

/-- `m / 1 = m` (∅-axiom; Lean-core `Nat.div_one` is `[propext]`). -/
private theorem div_one_pure (m : Nat) : m / 1 = m := by
  have h := mul_div_cancel_left_pure 1 m (by decide : 0 < 1); rwa [Nat.one_mul] at h

/-- Range-product congruence: agree on `[0, n)` ⟹ equal products. -/
theorem prodTo_congr : ∀ (n : Nat) (f g : Nat → Nat),
    (∀ k, k < n → f k = g k) → prodTo n f = prodTo n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
      show prodTo n f * f n = prodTo n g * g n
      rw [prodTo_congr n f g (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

/-- Extract the first factor: `∏_{k<n+1} f k = f 0 · ∏_{k<n} f (k+1)`. -/
theorem prodTo_split_first : ∀ (n : Nat) (f : Nat → Nat),
    prodTo (n + 1) f = f 0 * prodTo n (fun k => f (k + 1))
  | 0, f => by show (1 : Nat) * f 0 = f 0 * 1; rw [Nat.one_mul, Nat.mul_one]
  | n + 1, f => by
      show prodTo (n + 1) f * f (n + 1) = f 0 * (prodTo n (fun k => f (k + 1)) * f (n + 1))
      rw [prodTo_split_first n f, mul_assoc]

/-- Mod-`p` distributes over a range product. -/
theorem prodTo_mod (p : Nat) : ∀ (n : Nat) (f : Nat → Nat),
    (prodTo n f) % p = (prodTo n (fun k => f k % p)) % p
  | 0, _ => rfl
  | n + 1, f => by
      show (prodTo n f * f n) % p = (prodTo n (fun k => f k % p) * (f n % p)) % p
      rw [mul_mod_pure (prodTo n f) (f n) p, prodTo_mod p n f,
          mul_mod_pure (prodTo n (fun k => f k % p)) (f n % p) p, mod_mod (f n) p]

/-- The base-`p` digit product `∏_{i<L} C((m/p^i) mod p, (n/p^i) mod p)`. -/
def lucasProd (p m n L : Nat) : Nat :=
  prodTo L (fun i => choose ((m / p ^ i) % p) ((n / p ^ i) % p))

/-- Peel the lowest digit: `lucasProd p m n (L+1) = C(m%p, n%p) · lucasProd p (m/p) (n/p) L`.
    The higher digits reindex via the nested floor `m / p^{i+1} = (m/p) / p^i` (`div_div_pure`). -/
theorem lucasProd_succ (p m n L : Nat) (hp0 : 0 < p) :
    lucasProd p m n (L + 1)
      = choose (m % p) (n % p) * lucasProd p (m / p) (n / p) L := by
  unfold lucasProd
  rw [prodTo_split_first]
  have h0 : choose ((m / p ^ 0) % p) ((n / p ^ 0) % p) = choose (m % p) (n % p) := by
    rw [Nat.pow_zero, div_one_pure, div_one_pure]
  rw [h0]
  congr 1
  apply prodTo_congr
  intro i _
  have hps : p ^ (i + 1) = p * p ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
  show choose ((m / p ^ (i + 1)) % p) ((n / p ^ (i + 1)) % p)
     = choose ((m / p / p ^ i) % p) ((n / p / p ^ i) % p)
  rw [hps, div_div_pure m p (p ^ i) hp0 (Nat.pos_pow_of_pos i hp0),
      div_div_pure n p (p ^ i) hp0 (Nat.pos_pow_of_pos i hp0)]

/-- ★★★★★ **Lucas' theorem (explicit digit-product form)** — for a prime `p` and `n < p^L`:
    `choose m n ≡ ∏_{i<L} choose ((m / p^i) % p) ((n / p^i) % p)  (mod p)`.  The binomial mod `p` is
    the product of the binomials of the base-`p` digits.  Induction on `L`: the base `L = 0` forces
    `n = 0` (`choose m 0 = 1`, empty product `= 1`); the step is `lucas_div` (split off the low
    digits) matched to `lucasProd_succ`, with `n / p < p^L` carrying the bound down.  ∅-axiom. -/
theorem lucas_digits {p : Nat} (hp : Prime213 p) :
    ∀ (L m n : Nat), n < p ^ L → (choose m n) % p = (lucasProd p m n L) % p
  | 0, m, n, hn => by
      have hn0 : n = 0 := Nat.le_antisymm (Nat.le_of_lt_succ hn) (Nat.zero_le n)
      subst hn0
      show (choose m 0) % p = (prodTo 0 _) % p
      rw [choose_zero_right]; rfl
  | L + 1, m, n, hn => by
      have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
      have hnp : n / p < p ^ L := by
        apply div_lt_of_lt_mul
        rw [Nat.mul_comm, ← Nat.pow_succ]; exact hn
      rw [lucas_div hp m n, lucasProd_succ p m n L hp0,
          mul_mod_pure (choose (m % p) (n % p)) (lucasProd p (m / p) (n / p) L) p,
          ← lucas_digits hp L (m / p) (n / p) hnp,
          ← mul_mod_pure (choose (m % p) (n % p)) (choose (m / p) (n / p)) p,
          Nat.mul_comm (choose (m % p) (n % p)) (choose (m / p) (n / p))]

/-! ## Smoke test -/

open E213.Lib.Math.NumberTheory.ModArith.LucasTheorem (prime5)

/-- p=5, m=13=(2,3)₅, n=7=(1,2)₅: `C(13,7) ≡ C(3,2)·C(2,1) (mod 5)` via the digit product
    (`lucasProd 5 13 7 2 = 6`, `C(13,7) = 1716`, both `≡ 1 mod 5`). -/
theorem lucas_digits_5_smoke : (choose 13 7) % 5 = (lucasProd 5 13 7 2) % 5 :=
  lucas_digits prime5 2 13 7 (by decide)

end E213.Lib.Math.Combinatorics.LucasDigitProduct
