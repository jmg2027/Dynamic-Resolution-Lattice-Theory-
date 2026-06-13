import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PolyNatMTactic
import E213.Lens.Number.Nat213.MultSystemValue
import E213.Lib.Math.NumberTheory.Legendre
import E213.Lib.Math.NumberTheory.LcmGrowthChebyshev
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem

/-!
# Lens.Number.Nat213.ChebyshevLower — the Chebyshev lower bound `π(N) ≥ c·N/ln N`

The matching direction to the density cut (`MultSystemValue.primeDensityToZero`).
Route: `2^n ≤ C(2n,n) ≤ (2n)^{π(2n)}`, so `n ≤ π(2n)·log₂(2n)`.

This file builds the **Kummer prime-power bound** `vp_p(C(2n,n)) ≤ ⌊log_p(2n)⌋`
(via Legendre's formula `vp_p(m!) = Σ ⌊m/p^i⌋` and the per-term floor inequality
`⌊2n/d⌋ ≤ 2⌊n/d⌋ + [d ≤ 2n]`), then `C(2n,n) ≤ (2n)^{π(2n)}` and the lower bound.

Lives under `Lens/` (not `Lib/Math/`) because it builds on the central-binomial
machinery in `MultSystemValue` (`Lens/`); `Legendre`/`LcmGrowthChebyshev` (`Lib/`)
are imported in the allowed `Lens → Lib` direction.  All ∅-axiom.
-/

namespace E213.Lens.Number.Nat213.ChebyshevLower

open E213.Meta.Nat.NatDiv213
  (div_add_mod_pure add_mul_div_left_pure div_lt_of_lt_mul le_of_add_le_add_left_pure)
open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.PureNat (lt_two_pow)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 vp_mul)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_succ factorial_pos)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ sumTo_zero)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_add_func sumTo_congr)
open E213.Lib.Math.NumberTheory.Legendre (legendre)
open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev (sumTo_le_sumTo lcmExpCount_eq_floorLog floorLog)
open E213.Meta.Nat.FloorLog (floorLog_pow_le)
open E213.Lens.Number.Nat213.MultSystem (binom)
open E213.Lens.Number.Nat213.MultSystemValue (fact fact_pos central_binom_factorial primePi)

/-- **The per-term Kummer inequality**: `⌊2n/d⌋ ≤ 2⌊n/d⌋ + [d ≤ 2n]` (`d > 0`).
    For `d ≤ 2n`: `⌊2n/d⌋ ≤ 2⌊n/d⌋ + 1` (the floor of a doubled quotient gains at
    most one).  For `d > 2n`: `⌊2n/d⌋ = 0`.  The heart of Kummer's bound on
    `vp_p(C(2n,n))`. -/
theorem floor_two_mul_div_le (n d : Nat) (hd : 0 < d) :
    2 * n / d ≤ 2 * (n / d) + (if d ≤ 2 * n then 1 else 0) := by
  by_cases h : d ≤ 2 * n
  · rw [if_pos h]
    have hdm : d * (n / d) + n % d = n := div_add_mod_pure n d
    have h2n : 2 * n = 2 * (n % d) + d * (2 * (n / d)) := by
      have hexp : 2 * (d * (n / d) + n % d) = 2 * (n % d) + d * (2 * (n / d)) := by ring_nat
      rwa [hdm] at hexp
    have hkey : 2 * n / d = 2 * (n / d) + 2 * (n % d) / d := by
      rw [h2n, add_mul_div_left_pure (2 * (n % d)) d (2 * (n / d)) hd]
      exact Nat.add_comm _ _
    have hmodlt : 2 * (n % d) < d * 2 := by
      have hlt : n % d < d := Nat.mod_lt n hd
      calc 2 * (n % d) < 2 * (n % d) + 2 := Nat.lt_add_of_pos_right (by decide)
        _ = 2 * (n % d + 1) := by ring_nat
        _ ≤ 2 * d := Nat.mul_le_mul (Nat.le_refl 2) hlt
        _ = d * 2 := by ring_nat
    have hmod1 : 2 * (n % d) / d ≤ 1 := Nat.le_of_lt_succ (div_lt_of_lt_mul hmodlt)
    rw [hkey]; exact Nat.add_le_add (Nat.le_refl _) hmod1
  · rw [if_neg h, Nat.add_zero, Nat.div_eq_of_lt (Nat.not_le.mp h)]
    exact Nat.zero_le _

/-- `fact = factorial` — the two factorial defs (`MultSystemValue.fact`,
    `CutFactorial.factorial`) are identical; bridge for using Legendre. -/
theorem fact_eq_factorial : ∀ n, fact n = factorial n
  | 0     => rfl
  | n + 1 => by
      show (n + 1) * fact n = factorial (n + 1)
      rw [factorial_succ, fact_eq_factorial n]

/-- `2 · Σ = Σ 2·` (scalar pull-in). -/
theorem sumTo_two_mul (n : Nat) (f : Nat → Nat) :
    2 * sumTo n f = sumTo n (fun k => 2 * f k) := by
  rw [Nat.two_mul, sumTo_add_func n f f]
  exact sumTo_congr n _ _ (fun k _ => (Nat.two_mul (f k)).symm)

/-- Extending a sum past where the summand vanishes leaves it unchanged. -/
theorem sumTo_extend_vanish {f : Nat → Nat} {a : Nat} (hvan : ∀ j, a ≤ j → f j = 0) :
    ∀ b, a ≤ b → sumTo a f = sumTo b f := by
  intro b
  induction b with
  | zero => intro hab; rw [Nat.le_antisymm hab (Nat.zero_le _)]
  | succ k ih =>
      intro hab
      rcases Nat.lt_or_ge a (k + 1) with hlt | hge
      · have hak : a ≤ k := Nat.le_of_lt_succ hlt
        rw [sumTo_succ, ← ih hak, hvan k hak, Nat.add_zero]
      · rw [Nat.le_antisymm hab hge]

open E213.Lens.Number.Nat213.MultSystemValue (central_binom_pos)

/-- **Kummer's prime-power bound**: `vp_p(C(2n,n)) ≤ ⌊log_p(2n)⌋` (`p` prime,
    `n ≥ 1`).  From `vp_p(C(2n,n)) + 2·vp_p(n!) = vp_p((2n)!)` (`central_binom_factorial`
    + `vp_mul`), Legendre `vp_p(m!) = Σ_{j} ⌊m/p^{j+1}⌋`, and the per-term bound
    `⌊2n/p^{j+1}⌋ ≤ 2⌊n/p^{j+1}⌋ + [p^{j+1} ≤ 2n]` summed (`lcmExpCount_eq_floorLog`
    gives the indicator sum `= ⌊log_p(2n)⌋`).  No Nat subtraction: cancel `2·vp_p(n!)`
    additively. -/
theorem vp_central_binom_le_floorLog {p n : Nat} (hp : Prime213 p) (hn : 1 ≤ n) :
    vp p (binom (2 * n) n) ≤ floorLog p (2 * n) := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have h2npos : 1 ≤ 2 * n := Nat.le_trans hn (by rw [Nat.two_mul]; exact Nat.le_add_left n n)
  have hbpos : 0 < binom (2 * n) n := central_binom_pos n
  have hfpos : 0 < factorial n := factorial_pos n
  -- factorial form of the central-binomial identity
  have hcbf : binom (2 * n) n * (factorial n * factorial n) = factorial (2 * n) := by
    have h := central_binom_factorial n
    rw [fact_eq_factorial n, fact_eq_factorial (2 * n)] at h
    exact h
  -- vp relation (additive, subtraction-free)
  have hvp : vp p (binom (2 * n) n) + (vp p (factorial n) + vp p (factorial n))
      = vp p (factorial (2 * n)) := by
    have h := congrArg (vp p) hcbf
    rw [vp_mul hp hbpos (Nat.mul_pos hfpos hfpos), vp_mul hp hfpos hfpos] at h
    exact h
  -- Legendre on both factorials
  have hlegn : vp p (factorial n) = sumTo n (fun j => n / p ^ (j + 1)) := legendre hp n
  rw [legendre hp (2 * n), hlegn] at hvp
  -- extend the `n!` sums to range `2n`
  have hvan : ∀ j, n ≤ j → (fun j => n / p ^ (j + 1)) j = 0 := by
    intro j hj
    show n / p ^ (j + 1) = 0
    apply Nat.div_eq_of_lt
    calc n < 2 ^ (n + 1) := Nat.lt_trans (Nat.lt_succ_self n) (lt_two_pow (n + 1))
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ hj)
      _ ≤ p ^ (j + 1) := Nat.pow_le_pow_left hp.1 (j + 1)
  have hext : sumTo n (fun j => n / p ^ (j + 1)) = sumTo (2 * n) (fun j => n / p ^ (j + 1)) :=
    sumTo_extend_vanish hvan (2 * n) (by rw [Nat.two_mul]; exact Nat.le_add_left n n)
  rw [hext] at hvp
  -- the summed per-term bound
  have hsumbound : sumTo (2 * n) (fun j => 2 * n / p ^ (j + 1))
      ≤ 2 * sumTo (2 * n) (fun j => n / p ^ (j + 1)) + floorLog p (2 * n) := by
    have hterm : sumTo (2 * n) (fun j => 2 * n / p ^ (j + 1))
        ≤ sumTo (2 * n)
            (fun j => 2 * (n / p ^ (j + 1)) + (if p ^ (j + 1) ≤ 2 * n then 1 else 0)) := by
      apply sumTo_le_sumTo
      exact fun k _ => floor_two_mul_div_le n (p ^ (k + 1)) (Nat.pos_pow_of_pos (k + 1) hp0)
    rw [← sumTo_add_func (2 * n) (fun j => 2 * (n / p ^ (j + 1)))
          (fun j => if p ^ (j + 1) ≤ 2 * n then 1 else 0),
        ← sumTo_two_mul (2 * n) (fun j => n / p ^ (j + 1)),
        lcmExpCount_eq_floorLog hp.1 h2npos] at hterm
    exact hterm
  -- combine + cancel 2·vp_p(n!)
  have hSS : sumTo (2 * n) (fun j => n / p ^ (j + 1)) + sumTo (2 * n) (fun j => n / p ^ (j + 1))
      = 2 * sumTo (2 * n) (fun j => n / p ^ (j + 1)) := (Nat.two_mul _).symm
  rw [hSS] at hvp
  have hcomb : vp p (binom (2 * n) n) + 2 * sumTo (2 * n) (fun j => n / p ^ (j + 1))
      ≤ 2 * sumTo (2 * n) (fun j => n / p ^ (j + 1)) + floorLog p (2 * n) := by
    rw [hvp]; exact hsumbound
  rw [Nat.add_comm (vp p (binom (2 * n) n)) (2 * sumTo (2 * n) (fun j => n / p ^ (j + 1)))] at hcomb
  exact le_of_add_le_add_left_pure hcomb

/-- **Each prime power dividing `C(2n,n)` is `≤ 2n`** (`p` prime, `n ≥ 1`).  The
    Kummer bound `vp_p(C(2n,n)) ≤ ⌊log_p(2n)⌋` exponentiated against the `floorLog`
    sandwich `p^{⌊log_p(2n)⌋} ≤ 2n`.  The factor bound for `C(2n,n) ≤ (2n)^{π(2n)}`. -/
theorem prime_pow_vp_central_binom_le {p n : Nat} (hp : Prime213 p) (hn : 1 ≤ n) :
    p ^ vp p (binom (2 * n) n) ≤ 2 * n := by
  have h2n : 1 ≤ 2 * n := Nat.le_trans hn (by rw [Nat.two_mul]; exact Nat.le_add_left n n)
  exact Nat.le_trans
    (Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hp.1)
      (vp_central_binom_le_floorLog hp hn))
    (floorLog_pow_le h2n)

end E213.Lens.Number.Nat213.ChebyshevLower
