import E213.Lib.Math.Combinatorics.FibonacciDivisibility
import E213.Meta.Nat.Gcd213
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative

/-!
# The Fibonacci-gcd theorem `gcd(Fₘ, Fₙ) = F_gcd(m,n)` (∅-axiom)

The crown jewel of Fibonacci number theory — the gcd of two Fibonacci numbers is
the Fibonacci of their index gcd.  Built on the addition formula + divisibility
of `FibonacciDivisibility` and the `gcd213` Euclidean kernel.

  * **G1 `fib_consecutive_coprime`** `gcd(Fₙ, F_{n+1}) = 1` — consecutive Fibonaccis
    are coprime (induction + the `gcd(a, a+b) = gcd(a,b)` step).
  * **G2 `fib_gcd_add_reduce`** `gcd(Fₘ, F_{m+n}) = gcd(Fₘ, Fₙ)` — the addition-formula
    reduction: any `e ∣ Fₘ` is coprime to `F_{m+1}` (G1), so Euclid's lemma transfers
    divisibility through `F_{m+n} = F_{m+1}F_{n+1} + Fₘ Fₙ`.
  * **G3 `fib_gcd`** `gcd(Fₘ, Fₙ) = F_gcd(m,n)` — strong induction on the first index
    mirroring `gcd213`'s own `%`-recursion (`fib_gcd_mod_step` lines the index Euclid
    step up with the Fibonacci-gcd step via `div_add_mod` + G2-iterated `drop_mult`).

All ∅-axiom (`Nat.strongRecOn` verified PURE; `fib` is the local two-step
recurrence from `FibonacciDivisibility`).
-/

namespace E213.Lib.Math.Combinatorics.FibonacciGcd

open E213.Tactic.NatHelper (gcd213 add_sub_cancel_right sub_add_cancel)
open E213.Lib.Math.Combinatorics.FibonacciDivisibility
  (fib fib_rec fib_add fib_dvd_fib_mul dvd_refl_n dvd_mul_of_dvd dvd_add_n)
open E213.Meta.Nat.Gcd213
  (gcd213_comm gcd213_rec gcd213_sub_left gcd213_succ_self gcd213_mul_left
   gcd213_dvd_left gcd213_dvd_right gcd213_greatest dvd_antisymm_213
   gcd213_self gcd213_one_left coprime_dvd_of_dvd_mul gcd213_zero_left
   mul_assoc_213 dvd_sub_213 dvd_add_213)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
  (dvd_trans_213 eq_one_of_dvd_one coprime_mul_iff)
open E213.Meta.Nat.AddMod213 (div_add_mod)

/-! ## G1: consecutive Fibonaccis coprime -/

/-- ★ **G1** — `gcd213 (fib n) (fib (n+1)) = 1`. -/
theorem fib_consecutive_coprime : ∀ n : Nat, gcd213 (fib n) (fib (n + 1)) = 1
  | 0 => by decide
  | n + 1 => by
    have ih : gcd213 (fib n) (fib (n + 1)) = 1 := fib_consecutive_coprime n
    have hfib2 : fib (n + 2) = fib (n + 1) + fib n := by
      rw [fib_rec n]; exact Nat.add_comm (fib n) (fib (n + 1))
    rw [gcd213_comm (fib (n + 1)) (fib (n + 2)), hfib2]
    rw [gcd213_sub_left (fib (n + 1) + fib n) (fib (n + 1)) (Nat.le_add_right _ _)]
    have hsub : fib (n + 1) + fib n - fib (n + 1) = fib n := by
      rw [Nat.add_comm (fib (n + 1)) (fib n)]
      exact add_sub_cancel_right (fib n) (fib (n + 1))
    rw [hsub]
    exact ih

/-! ## G2: the addition-formula reduction -/

/-- `gcd213 a 0 = a`. -/
theorem gcd213_zero_right (a : Nat) : gcd213 a 0 = a :=
  (gcd213_comm a 0).trans (gcd213_zero_left a)

/-- If `e ∣ fib m`, then `e` is coprime to `fib (m+1)` (G1 via `gcd213_greatest`). -/
theorem coprime_succ_of_dvd_fib {e m : Nat} (he : e ∣ fib m) :
    gcd213 e (fib (m + 1)) = 1 := by
  have hda : gcd213 e (fib (m + 1)) ∣ fib m :=
    dvd_trans_213 (gcd213_dvd_left e (fib (m + 1))) he
  have hdb : gcd213 e (fib (m + 1)) ∣ fib (m + 1) := gcd213_dvd_right e (fib (m + 1))
  have hdg : gcd213 e (fib (m + 1)) ∣ gcd213 (fib m) (fib (m + 1)) :=
    gcd213_greatest (fib m) (fib (m + 1)) _ hda hdb
  have hg1 : gcd213 (fib m) (fib (m + 1)) = 1 := fib_consecutive_coprime m
  rw [hg1] at hdg
  exact eq_one_of_dvd_one hdg

/-- Divisor-transfer: with `e ∣ fib m`, `e ∣ fib (m + (k+1)) ↔ e ∣ fib (k+1)`. -/
theorem dvd_fib_add_iff {e m k : Nat} (he : e ∣ fib m) :
    e ∣ fib (m + (k + 1)) ↔ e ∣ fib (k + 1) := by
  have hidx : m + (k + 1) = m + k + 1 := rfl
  have hform : fib (m + (k + 1)) = fib (m + 1) * fib (k + 1) + fib m * fib k := by
    rw [hidx]; exact fib_add m k
  have hco : gcd213 e (fib (m + 1)) = 1 := coprime_succ_of_dvd_fib he
  constructor
  · intro hsum
    have hmk : e ∣ fib m * fib k := dvd_mul_of_dvd he (fib k)
    have hge : fib m * fib k ≤ fib (m + (k + 1)) := by
      rw [hform]; exact Nat.le_add_left _ _
    have hsub : e ∣ (fib (m + (k + 1)) - fib m * fib k) :=
      dvd_sub_213 (fib m * fib k) (fib (m + (k + 1))) e hge hmk hsum
    have heq : fib (m + (k + 1)) - fib m * fib k = fib (m + 1) * fib (k + 1) := by
      rw [hform]; exact add_sub_cancel_right (fib (m + 1) * fib (k + 1)) (fib m * fib k)
    rw [heq] at hsub
    exact coprime_dvd_of_dvd_mul hco hsub
  · intro hk1
    have h1 : e ∣ fib (m + 1) * fib (k + 1) := by
      rw [Nat.mul_comm (fib (m + 1)) (fib (k + 1))]
      exact dvd_mul_of_dvd hk1 (fib (m + 1))
    have h2 : e ∣ fib m * fib k := dvd_mul_of_dvd he (fib k)
    have hsum : e ∣ (fib (m + 1) * fib (k + 1) + fib m * fib k) := dvd_add_213 e _ _ h1 h2
    rw [hform]; exact hsum

/-- ★★ **G2 — addition-formula reduction**:
    `gcd213 (fib m) (fib (m + n)) = gcd213 (fib m) (fib n)`. -/
theorem fib_gcd_add_reduce (m : Nat) :
    ∀ n : Nat, gcd213 (fib m) (fib (m + n)) = gcd213 (fib m) (fib n)
  | 0 => by
    show gcd213 (fib m) (fib m) = gcd213 (fib m) (fib 0)
    rw [gcd213_self (fib m)]
    show fib m = gcd213 (fib m) 0
    rw [gcd213_zero_right (fib m)]
  | k + 1 => by
    apply dvd_antisymm_213
    · apply gcd213_greatest
      · exact gcd213_dvd_left (fib m) (fib (m + (k + 1)))
      · have hdm : gcd213 (fib m) (fib (m + (k + 1))) ∣ fib m :=
          gcd213_dvd_left (fib m) (fib (m + (k + 1)))
        have hdsum : gcd213 (fib m) (fib (m + (k + 1))) ∣ fib (m + (k + 1)) :=
          gcd213_dvd_right (fib m) (fib (m + (k + 1)))
        exact (dvd_fib_add_iff hdm).mp hdsum
    · apply gcd213_greatest
      · exact gcd213_dvd_left (fib m) (fib (k + 1))
      · have hdm : gcd213 (fib m) (fib (k + 1)) ∣ fib m :=
          gcd213_dvd_left (fib m) (fib (k + 1))
        have hdk : gcd213 (fib m) (fib (k + 1)) ∣ fib (k + 1) :=
          gcd213_dvd_right (fib m) (fib (k + 1))
        exact (dvd_fib_add_iff hdm).mpr hdk

/-! ## G3: the Fibonacci-gcd theorem -/

/-- Drop a multiple of the index: `gcd213 (fib m) (fib (q*m + r)) = gcd213 (fib m) (fib r)`.
    Induction on `q` via G2. -/
theorem fib_gcd_drop_mult (m r : Nat) :
    ∀ q : Nat, gcd213 (fib m) (fib (q * m + r)) = gcd213 (fib m) (fib r)
  | 0 => by
    show gcd213 (fib m) (fib (0 * m + r)) = gcd213 (fib m) (fib r)
    rw [Nat.zero_mul, Nat.zero_add]
  | q + 1 => by
    have hidx : (q + 1) * m + r = m + (q * m + r) := by ring_nat
    rw [hidx, fib_gcd_add_reduce m (q * m + r)]
    exact fib_gcd_drop_mult m r q

/-- Mod step on indices, mirroring `gcd213_rec`: for `0 < a`,
    `gcd213 (fib a) (fib b) = gcd213 (fib (b % a)) (fib a)`. -/
theorem fib_gcd_mod_step (a b : Nat) (_ha : 0 < a) :
    gcd213 (fib a) (fib b) = gcd213 (fib (b % a)) (fib a) := by
  have hdm : a * (b / a) + b % a = b := div_add_mod b a
  have hsplit : (b / a) * a + b % a = b := by
    rw [Nat.mul_comm (b / a) a]; exact hdm
  -- rewrite ONLY the `fib b` occurrence via `congrArg` (a plain `rw` corrupts `fib (b%a)`).
  have hfibeq : fib b = fib ((b / a) * a + b % a) := congrArg fib hsplit.symm
  have hstep : gcd213 (fib a) (fib b) = gcd213 (fib a) (fib (b % a)) := by
    rw [hfibeq]; exact fib_gcd_drop_mult a (b % a) (b / a)
  rw [hstep]; exact gcd213_comm (fib a) (fib (b % a))

/-- ★★★ **Fibonacci-gcd theorem**: `gcd213 (fib a) (fib b) = fib (gcd213 a b)`.
    Strong induction on `a`, mirroring the Euclidean recursion
    `gcd213 (a'+1) b = gcd213 (b % (a'+1)) (a'+1)`. -/
theorem fib_gcd : ∀ (a b : Nat), gcd213 (fib a) (fib b) = fib (gcd213 a b) := fun a =>
  Nat.strongRecOn a
    (motive := fun a => ∀ b, gcd213 (fib a) (fib b) = fib (gcd213 a b))
    fun a ih b => by
      show gcd213 (fib a) (fib b) = fib (gcd213 a b)
      cases a with
      | zero =>
        rw [gcd213_zero_left b]
        show gcd213 (fib 0) (fib b) = fib b
        show gcd213 0 (fib b) = fib b
        exact gcd213_zero_left (fib b)
      | succ a' =>
        have ha : 0 < a' + 1 := Nat.succ_pos a'
        have hmod_lt : b % (a' + 1) < a' + 1 := Nat.mod_lt b ha
        rw [gcd213_rec (a' + 1) b ha]
        rw [← ih (b % (a' + 1)) hmod_lt (a' + 1)]
        exact fib_gcd_mod_step (a' + 1) b ha

/-! ## Smoke checks -/

theorem fib_gcd_smoke1 : gcd213 (fib 6) (fib 9) = fib (gcd213 6 9) := by decide
theorem fib_gcd_smoke2 : gcd213 (fib 8) (fib 12) = fib (gcd213 8 12) := by decide

end E213.Lib.Math.Combinatorics.FibonacciGcd
