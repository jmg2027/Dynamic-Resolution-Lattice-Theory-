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

Narrative: `theory/math/numbertheory/chebyshev_prime_counting.md` (both halves of
Chebyshev's theorem + the PNT density cut).
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
open E213.Meta.Nat.FloorLog (floorLog_pow_le lt_pow_floorLog_succ pow_lt_pow_of_lt floorLog_pow_self)
open E213.Meta.Nat.PowBasic (pow_mul_pure)
open E213.Lens.Number.Nat213.MultSystemValue (central_binom_ge_two_pow prime_not_dvd_fact)
open E213.Meta.Nat.Valuation (pow_vp_dvd)
open E213.Meta.Nat.VpMul (IsPrime213 vp_pow vp_self_pow)
open E213.Meta.Nat.VpSeparation (exists_prime_factor vp_eq_zero_of_not_dvd dvd_iff_one_le_vp)
open E213.Meta.Nat.FoldCriterion (prime_not_dvd_prime)
open E213.Lens.Number.Nat213.MultSystemValue
  (primePi primeIndicator primeIndicator_eq_one_iff primeIndicator_le_one decPrime)
open E213.Lens.Number.Nat213.MultSystem (binom)
open E213.Lens.Number.Nat213.MultSystemValue (fact fact_pos central_binom_factorial primePi)
open E213.Lens.Number.Nat213.MultSystemValue (chebBound primePi_pow_two_le_chebBound chebBound_mul_le)

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

/-- **`m ≤ B^{π(N)}`** when every prime factor of `m` is `≤ N` and every prime
    power `p^{vp_p m} ≤ B` (`m > 0`, `B ≥ 1`).  Induction on the prime range `N`:
    at a prime `N+1`, peel its full power `(N+1)^{vp}·m'` (`pow_vp_dvd`; `m'`
    coprime to `N+1`), apply the IH to `m'` (primes `≤ N`), and `(N+1)^{vp} ≤ B`
    bumps the bound by one factor (`π(N+1) = π(N)+1`).  The distinct-prime grouping
    done inductively — no explicit product-over-primes object. -/
theorem le_pow_primePi (B : Nat) (hB : 1 ≤ B) : ∀ N m, 0 < m →
    (∀ p, IsPrime213 p → p ∣ m → p ≤ N) →
    (∀ q, IsPrime213 q → q ^ vp q m ≤ B) →
    m ≤ B ^ primePi N := by
  intro N
  induction N with
  | zero =>
      intro m hm hdvd _
      have hm1 : m ≤ 1 := by
        rcases Nat.lt_or_ge m 2 with h2 | h2
        · exact Nat.le_of_lt_succ h2
        · obtain ⟨q, hq, hqm⟩ := exists_prime_factor m m (Nat.le_refl m) h2
          exact absurd (hdvd q hq hqm)
            (Nat.not_le.mpr (Nat.lt_of_lt_of_le (by decide) hq.two_le))
      show m ≤ B ^ primePi 0
      rw [show primePi 0 = 0 from rfl, Nat.pow_zero]; exact hm1
  | succ N ih =>
      intro m hm hdvd hpow
      haveI : Decidable (IsPrime213 (N + 1)) := decPrime (N + 1)
      by_cases hpp : IsPrime213 (N + 1)
      · obtain ⟨m', hm'⟩ := pow_vp_dvd (N + 1) m
        have hpe_pos : 0 < (N + 1) ^ vp (N + 1) m := Nat.pos_pow_of_pos _ (Nat.succ_pos N)
        have hm'pos : 0 < m' := by
          rcases Nat.eq_zero_or_pos m' with h0 | h
          · rw [h0, Nat.mul_zero] at hm'; rw [hm'] at hm; exact absurd hm (Nat.lt_irrefl 0)
          · exact h
        have hself : vp (N + 1) (N + 1) = 1 := by
          have := vp_self_pow hpp 1; rwa [Nat.pow_one] at this
        have hvpm' : vp (N + 1) m' = 0 := by
          have hc := congrArg (vp (N + 1)) hm'
          rw [vp_mul hpp hpe_pos hm'pos, vp_pow hpp (Nat.succ_pos N), hself, Nat.mul_one] at hc
          have hle : vp (N + 1) m + vp (N + 1) m' ≤ vp (N + 1) m + 0 := by
            rw [Nat.add_zero]; exact Nat.le_of_eq hc.symm
          exact Nat.le_antisymm (le_of_add_le_add_left_pure hle) (Nat.zero_le _)
        have hdvd' : ∀ p, IsPrime213 p → p ∣ m' → p ≤ N := by
          intro q hq hqm'
          obtain ⟨c1, hc1⟩ := hqm'
          have aux : ∀ e, m = (N + 1) ^ e * m' → q ∣ m := fun e h1 =>
            ⟨(N + 1) ^ e * c1, by rw [h1, hc1]; ring_nat⟩
          have hqm : q ∣ m := aux (vp (N + 1) m) hm'
          rcases Nat.lt_or_ge q (N + 1) with h | h
          · exact Nat.le_of_lt_succ h
          · have hqeq : q = N + 1 := Nat.le_antisymm (hdvd q hq hqm) h
            have hge1 : 1 ≤ vp (N + 1) m' :=
              (dvd_iff_one_le_vp hpp hm'pos).mp (hqeq ▸ ⟨c1, hc1⟩)
            rw [hvpm'] at hge1; exact absurd hge1 (by decide)
        have hpow' : ∀ q, IsPrime213 q → q ^ vp q m' ≤ B := by
          intro q hq
          by_cases hqp : q = N + 1
          · subst hqp; rw [hvpm', Nat.pow_zero]; exact hB
          · have hvpq : vp q m' = vp q m := by
              have hc := congrArg (vp q) hm'
              rw [vp_mul hq hpe_pos hm'pos, vp_pow hq (Nat.succ_pos N),
                  vp_eq_zero_of_not_dvd hq (Nat.succ_pos N) (prime_not_dvd_prime hq hpp hqp),
                  Nat.mul_zero, Nat.zero_add] at hc
              exact hc.symm
            rw [hvpq]; exact hpow q hq
        have hpi : primePi (N + 1) = primePi N + 1 := by
          show primePi N + primeIndicator (N + 1) = primePi N + 1
          rw [(primeIndicator_eq_one_iff (N + 1)).mpr hpp]
        rw [hm', hpi, Nat.pow_succ]
        calc (N + 1) ^ vp (N + 1) m * m' ≤ B * B ^ primePi N :=
              Nat.mul_le_mul (hpow (N + 1) hpp) (ih m' hm'pos hdvd' hpow')
          _ = B ^ primePi N * B := Nat.mul_comm _ _
      · have hdvd' : ∀ p, IsPrime213 p → p ∣ m → p ≤ N := by
          intro q hq hqm
          rcases Nat.lt_or_ge q (N + 1) with h | h
          · exact Nat.le_of_lt_succ h
          · exact absurd ((Nat.le_antisymm (hdvd q hq hqm) h) ▸ hq) hpp
        have hind0 : primeIndicator (N + 1) = 0 := by
          rcases Nat.eq_zero_or_pos (primeIndicator (N + 1)) with h0 | h
          · exact h0
          · exact absurd ((primeIndicator_eq_one_iff (N + 1)).mp
              (Nat.le_antisymm (primeIndicator_le_one (N + 1)) h)) hpp
        have hpi : primePi (N + 1) = primePi N := by
          show primePi N + primeIndicator (N + 1) = primePi N
          rw [hind0, Nat.add_zero]
        rw [hpi]; exact ih m hm hdvd' hpow

/-- **`C(2n,n) ≤ (2n)^{π(2n)}`** (`n ≥ 1`).  `le_pow_primePi` at `B = N = 2n`:
    every prime factor of `C(2n,n)` is `≤ 2n` (it divides `(2n)!`,
    `prime_not_dvd_fact`), and every prime power `p^{vp_p(C(2n,n))} ≤ 2n`
    (`prime_pow_vp_central_binom_le`). -/
theorem central_binom_le_pow_primePi {n : Nat} (hn : 1 ≤ n) :
    binom (2 * n) n ≤ (2 * n) ^ primePi (2 * n) := by
  have h2n : 1 ≤ 2 * n := Nat.le_trans hn (by rw [Nat.two_mul]; exact Nat.le_add_left n n)
  refine le_pow_primePi (2 * n) h2n (2 * n) (binom (2 * n) n) (central_binom_pos n) ?_ ?_
  · intro p hp hpdvd
    obtain ⟨c, hc⟩ := hpdvd
    have hpfact : p ∣ fact (2 * n) :=
      ⟨c * (fact n * fact n), by rw [← central_binom_factorial n, hc]; ring_nat⟩
    rcases Nat.lt_or_ge (2 * n) p with hlt | hge
    · exact absurd hpfact (prime_not_dvd_fact hp hlt)
    · exact hge
  · exact fun q hq => prime_pow_vp_central_binom_le hq hn

/-- **`2^n ≤ (2n)^{π(2n)}`** (`n ≥ 1`) — the cleared-denominator Chebyshev lower
    bound: `central_binom_ge_two_pow` ∘ `central_binom_le_pow_primePi`. -/
theorem two_pow_le_pow_primePi {n : Nat} (hn : 1 ≤ n) :
    2 ^ n ≤ (2 * n) ^ primePi (2 * n) :=
  Nat.le_trans (central_binom_ge_two_pow n) (central_binom_le_pow_primePi hn)

/-- **The Chebyshev lower bound**: `n ≤ (⌊log₂(2n)⌋ + 1) · π(2n)` (`n ≥ 1`), i.e.
    `π(2n) ≥ n / (⌊log₂(2n)⌋ + 1) ≈ n / log₂(2n)`.  Take `log₂` of `2^n ≤
    (2n)^{π(2n)} ≤ (2^{⌊log₂(2n)⌋+1})^{π(2n)}` (`2n < 2^{⌊log₂(2n)⌋+1}`).  Together
    with the upper bound (`primeDensityToZero`/`chebBound`), this is both halves of
    Chebyshev's theorem `c·N/ln N ≤ π(N) ≤ C·N/ln N`. -/
theorem chebyshev_lower {n : Nat} (hn : 1 ≤ n) :
    n ≤ (floorLog 2 (2 * n) + 1) * primePi (2 * n) := by
  have hbase : 2 * n ≤ 2 ^ (floorLog 2 (2 * n) + 1) :=
    Nat.le_of_lt (lt_pow_floorLog_succ (by decide))
  have hchain : (2 : Nat) ^ n ≤ 2 ^ ((floorLog 2 (2 * n) + 1) * primePi (2 * n)) :=
    calc (2 : Nat) ^ n ≤ (2 * n) ^ primePi (2 * n) := two_pow_le_pow_primePi hn
      _ ≤ (2 ^ (floorLog 2 (2 * n) + 1)) ^ primePi (2 * n) := Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((floorLog 2 (2 * n) + 1) * primePi (2 * n)) :=
          (pow_mul_pure 2 (floorLog 2 (2 * n) + 1) (primePi (2 * n))).symm
  rcases Nat.lt_or_ge ((floorLog 2 (2 * n) + 1) * primePi (2 * n)) n with hlt | hge
  · exact absurd hchain (Nat.not_le.mpr (pow_lt_pow_of_lt (by decide) hlt))
  · exact hge

/-! ## The two-sided Chebyshev order theorem — `π(2^m) = Θ(2^m/m)`

Both halves cut at the dyadic points `N = 2^{m+1}`, where the lower bound
(`chebyshev_lower`) and the upper bound (`chebBound`) line up cleanly with
`floorLog 2 N = m+1`.  The result is the genuine *order* statement
`c·N/log₂N ≤ π(N) ≤ C·N/log₂N` with explicit constants — Chebyshev's theorem
proper, the precise finite ∅-axiom content that *points at* PNT (the `~ N/ln N`
limit with constant `1`, a `Real213` pointing horizon reached by none). -/

/-- **Dyadic Chebyshev lower bound**: `2^m ≤ (m+2)·π(2^{m+1})` (all `m`), i.e.
    `π(2^{m+1}) ≥ 2^m/(m+2) ≈ N/(2·log₂N)`.  `chebyshev_lower` at `n = 2^m`:
    `2*2^m = 2^{m+1}` and `floorLog 2 (2^{m+1}) = m+1` (`floorLog_pow_self`). -/
theorem two_pow_le_succ_primePi (m : Nat) :
    2 ^ m ≤ (m + 2) * primePi (2 ^ (m + 1)) := by
  have hpow : 2 * 2 ^ m = 2 ^ (m + 1) := by rw [Nat.pow_succ]; ring_nat
  have hflog : floorLog 2 (2 * 2 ^ m) = m + 1 := by
    rw [hpow]; exact floorLog_pow_self (by decide) (m + 1)
  have h := chebyshev_lower (n := 2 ^ m) (Nat.pos_pow_of_pos m (by decide))
  rw [hflog, hpow] at h
  exact h

/-- **Dyadic Chebyshev upper bound (cleared-denominator)**: `(m+1)·π(2^{m+1}) ≤
    6·2^{m+1}`, i.e. `π(2^{m+1}) ≤ 6·2^{m+1}/(m+1) ≈ 6·N/log₂N`.  `π(2^{m+1}) ≤
    chebBound(m+1)` (`primePi_pow_two_le_chebBound`) times the partial-sum bound
    `chebBound(m+1)·(m+1) ≤ 6·2^{m+1}` (`chebBound_mul_le`). -/
theorem succ_mul_primePi_pow_two_le (m : Nat) :
    (m + 1) * primePi (2 ^ (m + 1)) ≤ 6 * 2 ^ (m + 1) := by
  calc (m + 1) * primePi (2 ^ (m + 1))
      = primePi (2 ^ (m + 1)) * (m + 1) := Nat.mul_comm _ _
    _ ≤ chebBound (m + 1) * (m + 1) :=
        Nat.mul_le_mul (primePi_pow_two_le_chebBound (m + 1)) (Nat.le_refl _)
    _ ≤ 6 * 2 ^ (m + 1) := (chebBound_mul_le m).1

/-- **Chebyshev's theorem (order form), `π(N) = Θ(N/log₂N)` at dyadic `N = 2^{m+1}`**:
    `2^{m+1} ≤ 2·(m+2)·π(2^{m+1})` (lower, `π ≥ N/(2(L+1))`) and `(m+1)·π(2^{m+1}) ≤
    6·2^{m+1}` (upper, `π ≤ 6·N/L`), where `L = floorLog 2 N = m+1`.  Both halves
    of Chebyshev's theorem in one statement, explicit constants, ∅-axiom — the
    finite skeleton of which PNT (`π(N)·ln N/N → 1`) is the asymptotic horizon. -/
theorem chebyshev_order (m : Nat) :
    2 ^ (m + 1) ≤ 2 * (m + 2) * primePi (2 ^ (m + 1)) ∧
      (m + 1) * primePi (2 ^ (m + 1)) ≤ 6 * 2 ^ (m + 1) := by
  refine ⟨?_, succ_mul_primePi_pow_two_le m⟩
  calc 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; ring_nat
    _ ≤ 2 * ((m + 2) * primePi (2 ^ (m + 1))) :=
        Nat.mul_le_mul (Nat.le_refl 2) (two_pow_le_succ_primePi m)
    _ = 2 * (m + 2) * primePi (2 ^ (m + 1)) := by ring_nat

end E213.Lens.Number.Nat213.ChebyshevLower
