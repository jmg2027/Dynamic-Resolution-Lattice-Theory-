import E213.Lib.Math.NumberTheory.Legendre
import E213.Lib.Math.NumberTheory.LcmGrowthChebyshev
import E213.Lib.Math.NumberTheory.FactorialLcmIdentity
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.NatRing213

/-!
# Legendre's factorial formula — recurrence + de Polignac digit-sum forms (∅-axiom)

The closed Σ-floor form `vₚ(n!) = Σ_{j<n} ⌊n/p^{j+1}⌋` already lives in the corpus as
`E213.Lib.Math.NumberTheory.Legendre.legendre` (PURE).  This scratch derives the two
genuinely-absent forms on top of it:

  * ★★★ `vp_fact_recurrence` — `vₚ(n!) = ⌊n/p⌋ + vₚ((⌊n/p⌋)!)` (Legendre/de Polignac
        recursive form, the must-have — it IS Legendre's formula unrolled).
  * ★★ `de_polignac` — `(p−1)·vₚ(n!) + s_p(n) = n` (de Polignac digit-sum, additive /
        subtraction-free form), with `s_p` = base-`p` digit sum.
-/

namespace E213.Lib.Math.NumberTheory.LegendreDePolignac

open E213.Meta.Nat.Valuation (vp vp_lt)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_zero
  factorial_succ factorial_pos)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ sumTo_zero)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr sumTo_add_func)
open E213.Lib.Math.NumberTheory.Legendre (legendre)
open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev (div_div_pure)
open E213.Lib.Math.NumberTheory.FactorialLcmIdentity (sumTo_extend_vanish)
open E213.Meta.Nat.FloorLog (lt_pow_self)
open E213.Meta.Nat.PureNat (pow_add)
open E213.Meta.Nat.NatRing213 (nat_mul_lt_mul_right)
open E213.Meta.Nat.NatDiv213 (div_add_mod_pure div_lt_of_lt_mul)

/-! ## §1 — sum peel-front infrastructure -/

/-- Peel the first term: `Σ_{k<n+1} f k = f 0 + Σ_{k<n} f (k+1)`. -/
theorem sumTo_succ_front (f : Nat → Nat) :
    ∀ n, sumTo (n + 1) f = f 0 + sumTo n (fun k => f (k + 1))
  | 0 => by rw [sumTo_succ, sumTo_zero, sumTo_zero, Nat.zero_add, Nat.add_zero]
  | n + 1 => by
    rw [sumTo_succ, sumTo_succ_front f n, sumTo_succ]
    show f 0 + sumTo n (fun k => f (k + 1)) + f (n + 1)
      = f 0 + (sumTo n (fun k => f (k + 1)) + f (n + 1))
    exact (Nat.add_assoc _ _ _)

/-! ## §2 — the recurrence `vₚ(n!) = ⌊n/p⌋ + vₚ((⌊n/p⌋)!)`

`legendre` gives `vₚ(n!) = Σ_{j<n} ⌊n/p^{j+1}⌋`.  Peel `j=0` (= `⌊n/p⌋`); the tail is
`Σ_{k<n-1} ⌊n/p^{k+2}⌋ = Σ_{k<n-1} ⌊(n/p)/p^{k+1}⌋` (nested floor `div_div_pure`), and
`fact_vp_extend` recognises this (extended to bound `n-1 ≥ n/p`) as `vₚ((n/p)!)`. -/

/-- ★★★ **Legendre / de Polignac recurrence**: `vₚ(n!) = ⌊n/p⌋ + vₚ((⌊n/p⌋)!)`
    (`p` prime).  This IS Legendre's formula, written recursively (one `÷p` per level). -/
theorem vp_fact_recurrence {p : Nat} (hp : Prime213 p) (n : Nat) :
    vp p (factorial n) = n / p + vp p (factorial (n / p)) := by
  have hq : 2 ≤ p := hp.1
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hq
  cases n with
  | zero =>
    rw [show (0 : Nat) / p = 0 from Nat.zero_div p, Nat.zero_add]
  | succ m =>
    rw [legendre hp (m + 1), sumTo_succ_front (fun j => (m + 1) / p ^ (j + 1)) m]
    show (m + 1) / p ^ (0 + 1) + sumTo m (fun k => (m + 1) / p ^ (k + 1 + 1))
      = (m + 1) / p + vp p (factorial ((m + 1) / p))
    rw [show (0 : Nat) + 1 = 1 from rfl, Nat.pow_one]
    -- rewrite tail summand: (m+1)/p^(k+2) = ((m+1)/p)/p^(k+1)
    have htail : sumTo m (fun k => (m + 1) / p ^ (k + 1 + 1))
        = sumTo m (fun k => ((m + 1) / p) / p ^ (k + 1)) := by
      refine sumTo_congr m _ _ (fun k _ => ?_)
      rw [show k + 1 + 1 = 1 + (k + 1) from by rw [Nat.add_comm], pow_add p 1 (k + 1),
          Nat.pow_one,
          div_div_pure (m + 1) p (p ^ (k + 1)) hp0 (Nat.pos_pow_of_pos (k + 1) hp0)]
    rw [htail]
    -- the tail = vₚ(((m+1)/p)!): legendre at (m+1)/p, extended to bound m ≥ (m+1)/p
    have hbnd : (m + 1) / p ≤ m := by
      have : (m + 1) / p < m + 1 := div_lt_of_lt_mul (by
        have h1 : 1 * (m + 1) < p * (m + 1) :=
          nat_mul_lt_mul_right (Nat.succ_pos m) (Nat.lt_of_lt_of_le (by decide) hq)
        rwa [Nat.one_mul] at h1)
      exact Nat.le_of_lt_succ this
    have hvan : ∀ e, (m + 1) / p ≤ e → ((m + 1) / p) / p ^ (e + 1) = 0 := by
      intro e he
      exact Nat.div_eq_of_lt (Nat.lt_of_le_of_lt he
        (Nat.lt_trans (Nat.lt_succ_self e) (lt_pow_self hq (e + 1))))
    rw [legendre hp ((m + 1) / p),
        sumTo_extend_vanish hvan m hbnd]

/-! ## §3 — de Polignac digit-sum form `(p−1)·vₚ(n!) + s_p(n) = n`

`s_p n` = sum of base-`p` digits of `n`, fuel-defined (`OddPartDecomposition.stripTwo`
template); recurrence `s_p n = s_p (n/p) + n%p`.  Then the recurrence `vp_fact_recurrence`
+ `(p−1)·q + q = p·q` + `p·(n/p) + n%p = n` gives the additive (subtraction-free) form. -/

/-- `sDigitF fuel p n` = sum of base-`p` digits of `n`, fuel-bounded.  Recurses on
    `n/p < n` (`p ≥ 2`, `n > 0`); exact once `fuel ≥ n`. -/
def sDigitF : Nat → Nat → Nat → Nat
  | 0,     _, _       => 0
  | _ + 1, _, 0       => 0
  | f + 1, p, (n + 1) => (n + 1) % p + sDigitF f p ((n + 1) / p)

/-- `n/p < n` in the form `(n+1)/p < n+1` (`p ≥ 2`). -/
private theorem div_lt_succ {p : Nat} (hq : 2 ≤ p) (n : Nat) : (n + 1) / p < n + 1 := by
  apply div_lt_of_lt_mul
  have h1 : 1 * (n + 1) < p * (n + 1) :=
    nat_mul_lt_mul_right (Nat.succ_pos n) (Nat.lt_of_lt_of_le (by decide) hq)
  rwa [Nat.one_mul] at h1

/-- Fuel irrelevance: `sDigitF` is independent of fuel once `fuel ≥ n` (`p ≥ 2`). -/
theorem sDigitF_fuel_eq {p : Nat} (hq : 2 ≤ p) :
    ∀ n f g, n ≤ f → n ≤ g → sDigitF f p n = sDigitF g p n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f g hf hg
    match n, f, g, hf, hg with
    | 0,     f,     g,     _,  _  => cases f <;> cases g <;> rfl
    | n + 1, f + 1, g + 1, hf, hg =>
      have hlt : (n + 1) / p < n + 1 := div_lt_succ hq n
      have hhf : (n + 1) / p ≤ f := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hf)
      have hhg : (n + 1) / p ≤ g := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hg)
      show (n + 1) % p + sDigitF f p ((n + 1) / p)
        = (n + 1) % p + sDigitF g p ((n + 1) / p)
      rw [ih ((n + 1) / p) hlt f g hhf hhg]

/-- `s_p n` = sum of base-`p` digits of `n` (fuel `= n`, the exact value). -/
def sDigit (p n : Nat) : Nat := sDigitF n p n

/-- The digit recurrence: `s_p n = s_p (n/p) + n%p` for `n > 0` (`p ≥ 2`).  `s_p 0 = 0`. -/
theorem sDigit_succ {p : Nat} (hq : 2 ≤ p) (n : Nat) :
    sDigit p (n + 1) = sDigit p ((n + 1) / p) + (n + 1) % p := by
  have hlt : (n + 1) / p < n + 1 := div_lt_succ hq n
  show sDigitF (n + 1) p (n + 1) = sDigitF ((n + 1) / p) p ((n + 1) / p) + (n + 1) % p
  show (n + 1) % p + sDigitF n p ((n + 1) / p)
    = sDigitF ((n + 1) / p) p ((n + 1) / p) + (n + 1) % p
  rw [sDigitF_fuel_eq hq ((n + 1) / p) n ((n + 1) / p)
        (Nat.le_of_lt_succ hlt) (Nat.le_refl _),
      Nat.add_comm]

theorem sDigit_zero (p : Nat) : sDigit p 0 = 0 := rfl

/-- `(p−1)·q + q = p·q` (`p ≥ 1`), the truncated `p−1` rejoined additively. -/
private theorem pred_mul_add {p : Nat} (hq : 2 ≤ p) (q : Nat) : (p - 1) * q + q = p * q := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 :=
    ⟨p - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le (by decide) hq)).symm⟩
  show k * q + q = (k + 1) * q
  rw [Nat.succ_mul]

/-- ★★ **de Polignac digit-sum form** (additive / subtraction-free):
    `(p−1)·vₚ(n!) + s_p(n) = n` (`p` prime).  Strong induction on `n`, through the
    recurrence `vp_fact_recurrence` + the digit recurrence `sDigit_succ`. -/
theorem de_polignac {p : Nat} (hp : Prime213 p) :
    ∀ n, (p - 1) * vp p (factorial n) + sDigit p n = n := by
  have hq : 2 ≤ p := hp.1
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 =>
      show (p - 1) * vp p (factorial 0) + sDigit p 0 = 0
      rw [factorial_zero, sDigit_zero]
      show (p - 1) * vp p 1 + 0 = 0
      rw [E213.Lib.Math.NumberTheory.Legendre.vp_one hq, Nat.mul_zero]
    | n + 1 =>
      have hlt : (n + 1) / p < n + 1 := div_lt_succ hq n
      have hIH : (p - 1) * vp p (factorial ((n + 1) / p)) + sDigit p ((n + 1) / p)
          = (n + 1) / p := ih ((n + 1) / p) hlt
      rw [vp_fact_recurrence hp (n + 1), sDigit_succ hq n,
          Nat.mul_add]
      -- goal: (p-1)*((n+1)/p) + (p-1)*vp(fact((n+1)/p)) + (sDigit((n+1)/p) + (n+1)%p) = n+1
      calc (p - 1) * ((n + 1) / p) + (p - 1) * vp p (factorial ((n + 1) / p))
              + (sDigit p ((n + 1) / p) + (n + 1) % p)
          = (p - 1) * ((n + 1) / p)
              + ((p - 1) * vp p (factorial ((n + 1) / p)) + sDigit p ((n + 1) / p))
              + (n + 1) % p := by
            rw [Nat.add_assoc ((p - 1) * ((n + 1) / p)), Nat.add_assoc,
                Nat.add_assoc ((p - 1) * vp p (factorial ((n + 1) / p)))]
        _ = (p - 1) * ((n + 1) / p) + (n + 1) / p + (n + 1) % p := by rw [hIH]
        _ = p * ((n + 1) / p) + (n + 1) % p := by rw [pred_mul_add hq]
        _ = n + 1 := div_add_mod_pure (n + 1) p

/-! ## §4 — concrete `decide` smokes (closed numeric, axiom-clean).

    `vp q n` runs `vpSearch` with fuel `= n`, so `decide` on `vp q (factorial n)`
    evaluates `q^(factorial n)` — feasible only for small factorials (`factorial 4 =
    24`; `factorial 6 = 720` already blows the kernel exponent budget).  The
    digit-sum `sDigit` smokes carry larger `n`. -/

theorem smoke_vp2_fact4 : vp 2 (factorial 4) = 3 := by decide
theorem smoke_vp3_fact4 : vp 3 (factorial 4) = 1 := by decide

/-- Recurrence smoke: `vp 2 (4!) = 4/2 + vp 2 (2!)` = `2 + 1 = 3`. -/
theorem smoke_rec : vp 2 (factorial 4) = 4 / 2 + vp 2 (factorial (4 / 2)) := by decide
/-- Digit-sum smoke: `(2-1)·vp 2 (4!) + s_2(4) = 3 + 1 = 4` (`4 = 100₂`). -/
theorem smoke_polignac : (2 - 1) * vp 2 (factorial 4) + sDigit 2 4 = 4 := by decide
/-- Base-`p` digit-sum smokes: `s_2(6) = 2` (`110₂`), `s_3(8) = 4` (`22₃`),
    `s_5(26) = 2` (`101₅`). -/
theorem smoke_sdigit2 : sDigit 2 6 = 2 := by decide
theorem smoke_sdigit3 : sDigit 3 8 = 4 := by decide
theorem smoke_sdigit5 : sDigit 5 26 = 2 := by decide

end E213.Lib.Math.NumberTheory.LegendreDePolignac
