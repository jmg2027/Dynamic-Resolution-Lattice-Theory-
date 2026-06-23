import E213.Lib.Math.NumberTheory.PrimePowFactorization
import E213.Lib.Math.NumberTheory.BertrandWindow
import E213.Lib.Math.NumberTheory.BinomChooseBridge
import E213.Lib.Math.NumberTheory.Primorial
import E213.Lib.Math.NumberTheory.IntSqrt
import E213.Meta.Nat.PowBasic
import E213.Meta.Nat.FloorLog

/-!
# Central binomial coefficient — explicit prime factorization (∅-axiom)

Combining the explicit FTA product form (`prod_prime_pow_eq`) with the Kummer
prime-power bound (`prime_pow_vp_central_binom_le`: `p^{vₚ(C(2n,n))} ≤ 2n`) gives
the explicit prime factorization of the central binomial coefficient over the
fixed index set of primes `≤ 2n`:

  `C(2n,n) = ∏_{p ≤ 2n, prime} p^{vₚ(C(2n,n))}`   (`central_binom_factorization`).

This is the object the Erdős proof of Bertrand's postulate **upper-bounds** by
splitting the index list `primesIn 0 (2n)` by the size of `p` (via
`primePowProd_append` + `primesIn_split`) and bounding each range.  The key input
beyond the FTA form is that every prime factor of `C(2n,n)` is `≤ 2n`
(`central_binom_prime_factors_le`), which is exactly what pins the index set.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.CentralBinomFactorization

open E213.Lib.Math.NumberTheory.PrimePowFactorization
  (primePowProd prod_prime_pow_eq primePowProd_append mem_primesIn
   primePowProd_le_pow_length primePowProd_le_listProd primesIn_length_le)
open E213.Lens.Number.Nat213.MultSystem (binom)
open E213.Lens.Number.Nat213.MultSystemValue
  (central_binom_pos primesIn mem_primesIn_prime mem_primesIn_gt mem_primesIn_le
   primesIn_split listProd listProd_append listProd_pos four_pow_le_succ_mul_central_binom)
open E213.Lib.Math.NumberTheory.Primorial (primorial_le_four_pow)
open E213.Lib.Math.NumberTheory.IntSqrt (isqrt isqrt_bracket)
open E213.Lens.Number.Nat213.ChebyshevLower (prime_pow_vp_central_binom_le vp_central_binom_le_floorLog)
open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpSeparation (dvd_iff_one_le_vp)
open E213.Meta.Nat.PowBasic (one_le_pow)
open E213.Meta.Nat.FloorLog (floorLog floorLog_le_of_lt_pow)
open E213.Meta.Nat.NatDiv213 (two_cancel_lt div_add_mod_pure le_of_add_le_add_left_pure)
open E213.Lib.Math.NumberTheory.BinomChooseBridge (binom_eq_choose)
open E213.Lib.Math.NumberTheory.BertrandWindow (prime_not_dvd_central_binom_mid)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)

/-- **Every prime factor of `C(2n,n)` is `≤ 2n`.**  If `q ∣ C(2n,n)` then
    `1 ≤ vₚ(C)`, so `q = q¹ ≤ q^{vₚ(C)} ≤ 2n` (`prime_pow_vp_central_binom_le`).
    Pins the index set for the explicit factorization. -/
theorem central_binom_prime_factors_le {q n : Nat} (hq : IsPrime213 q) (hn : 1 ≤ n)
    (hdvd : q ∣ binom (2 * n) n) : q ≤ 2 * n := by
  have hcpos : 0 < binom (2 * n) n := central_binom_pos n
  have hk : 1 ≤ vp q (binom (2 * n) n) := (dvd_iff_one_le_vp hq hcpos).mp hdvd
  have hbound : q ^ vp q (binom (2 * n) n) ≤ 2 * n := prime_pow_vp_central_binom_le hq hn
  have hqpos : 0 < q := Nat.lt_of_lt_of_le (by decide) hq.two_le
  have hqle : q ≤ q ^ vp q (binom (2 * n) n) := by
    obtain ⟨k, hk2⟩ : ∃ k, vp q (binom (2 * n) n) = k + 1 := by
      cases hvp : vp q (binom (2 * n) n) with
      | zero => rw [hvp] at hk; exact absurd hk (by decide)
      | succ k => exact ⟨k, rfl⟩
    rw [hk2]
    have h1 : 1 ≤ q ^ k := one_le_pow (Nat.le_trans (by decide) hq.two_le) k
    calc q = 1 * q := (Nat.one_mul q).symm
      _ ≤ q ^ k * q := Nat.mul_le_mul_right q h1
      _ = q ^ (k + 1) := rfl
  exact Nat.le_trans hqle hbound

/-- **Large primes have valuation ≤ 1.**  If `2n < p²` (a prime `p > √(2n)`), then
    `vₚ(C(2n,n)) ≤ 1`: Kummer gives `vₚ(C) ≤ ⌊log_p 2n⌋`, and `2n < p²` forces that
    floor-log `≤ 1`.  (Erdős's medium range `√(2n) < p ≤ 2n/3`.) -/
theorem vp_central_binom_le_one {p n : Nat} (hp : IsPrime213 p) (hn : 1 ≤ n)
    (hsq : 2 * n < p * p) : vp p (binom (2 * n) n) ≤ 1 := by
  have h2npos : 1 ≤ 2 * n := Nat.le_trans hn (by rw [Nat.two_mul]; exact Nat.le_add_left n n)
  have hpe : p ^ (1 + 1) = p * p := by rw [Nat.pow_succ, Nat.pow_one]
  have hlt : 2 * n < p ^ (1 + 1) := by rw [hpe]; exact hsq
  have hfl : floorLog p (2 * n) ≤ 1 := floorLog_le_of_lt_pow hp.1 h2npos hlt
  exact Nat.le_trans (vp_central_binom_le_floorLog hp hn) hfl

/-- **Large-prime factor ≤ `p`.**  For a prime `p` with `2n < p²`, the `p`-block of
    `C(2n,n)` is `p^{vₚ(C)} ≤ p` (since `vₚ(C) ≤ 1`).  The per-prime hypothesis of
    `primePowProd_le_listProd` for the medium range. -/
theorem central_binom_pow_le_self {p n : Nat} (hp : IsPrime213 p) (hn : 1 ≤ n)
    (hsq : 2 * n < p * p) : p ^ (vp p (binom (2 * n) n)) ≤ p := by
  have h1 : vp p (binom (2 * n) n) ≤ 1 := vp_central_binom_le_one hp hn hsq
  rcases Nat.eq_zero_or_pos (vp p (binom (2 * n) n)) with h0 | hpos
  · rw [h0]; show (1 : Nat) ≤ p; exact Nat.le_trans (show (1 : Nat) ≤ 2 by decide) hp.1
  · have he1 : vp p (binom (2 * n) n) = 1 := Nat.le_antisymm h1 hpos
    have hp1 : p ^ 1 = p := Nat.pow_one p
    rw [he1, hp1]
    exact Nat.le_refl p

/-! ## §5 — under the Bertrand negation, all prime factors are `≤ 2n/3` -/

/-- Pure division helper: `c·a ≤ b → a ≤ b/c` (`c > 0`).  The `≤`-companion of
    `NatDiv213.div_lt_of_lt_mul`, propext-free via `div_add_mod_pure`. -/
private theorem le_div_of_mul_le {c a b : Nat} (hc : 0 < c) (h : c * a ≤ b) : a ≤ b / c := by
  rcases Nat.lt_or_ge (b / c) a with hlt | hge
  · exfalso
    have h1 : b / c + 1 ≤ a := hlt
    have h2 : c * (b / c) + c ≤ c * a := by
      have e : c * (b / c) + c = c * (b / c + 1) := by ring_nat
      rw [e]; exact Nat.mul_le_mul (Nat.le_refl c) h1
    have hdm : c * (b / c) + b % c = b := div_add_mod_pure b c
    have h3 : c * (b / c) + c ≤ c * (b / c) + b % c := by rw [hdm]; exact Nat.le_trans h2 h
    have h4 : c ≤ b % c := le_of_add_le_add_left_pure h3
    exact Nat.lt_irrefl c (Nat.lt_of_le_of_lt h4 (Nat.mod_lt b hc))
  · exact hge

/-- **The Bertrand-negation collapses the prime range.**  Assume *no* prime lies in
    `(n, 2n]` (the negation of Bertrand's postulate at `n`, here as: no such prime
    divides `C(2n,n)` — automatic since every prime in `(n,2n]` does divide it).
    Then every prime factor `q` of `C(2n,n)` satisfies `3q ≤ 2n`, i.e. `q ≤ 2n/3`:
    `q ≤ 2n` always; `q ≤ n` (else `q ∈ (n,2n]`); and `q ∉ (2n/3, n]` by the
    vanishing window (`prime_not_dvd_central_binom_mid`, with `2n < 3q ≤ q²` for
    `q ≥ 3`).  Needs `n ≥ 3` (small `n` go to the finite chain).  ∅-axiom. -/
theorem central_binom_factor_le_div {q n : Nat} (hq : IsPrime213 q) (hn : 3 ≤ n)
    (hnobig : ∀ p, IsPrime213 p → n < p → p ≤ 2 * n → False)
    (hdvd : q ∣ binom (2 * n) n) : q ≤ 2 * n / 3 := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) hn
  apply le_div_of_mul_le (by decide : 0 < 3)
  rcases Nat.lt_or_ge (2 * n) (3 * q) with h3q | hge
  · -- 2n < 3q is impossible: it would force the vanishing window, contradicting q ∣ C
    have hq2n : q ≤ 2 * n := central_binom_prime_factors_le hq hn1 hdvd
    have hqn : q ≤ n := by
      rcases Nat.lt_or_ge n q with hlt | hge2
      · exact (hnobig q hq hlt hq2n).elim
      · exact hge2
    have hq3 : 3 ≤ q := by
      rcases Nat.lt_or_ge q 3 with hlt3 | hge3
      · exfalso
        have hq2 : q = 2 := Nat.le_antisymm (Nat.le_of_lt_succ hlt3) hq.1
        rw [hq2] at h3q
        have he : (3 : Nat) * 2 = 2 * 3 := by decide
        rw [he] at h3q
        exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le (two_cancel_lt n 3 h3q) hn)
      · exact hge3
    have hsq : 2 * n < q * q := Nat.lt_of_lt_of_le h3q (Nat.mul_le_mul_right q hq3)
    have hwin : ¬ q ∣ choose (2 * n) n :=
      prime_not_dvd_central_binom_mid hq hn1 hqn h3q hsq
    rw [binom_eq_choose (2 * n) n] at hdvd
    exact absurd hdvd hwin
  · exact hge

/-- ★★★ **Bertrand-negation factorization.**  If no prime lies in `(n, 2n]`
    (`n ≥ 3`), then `C(2n,n) = ∏_{p ≤ 2n/3, prime} p^{vₚ(C(2n,n))}` — the prime
    range collapses from `≤ 2n` to `≤ 2n/3` (`central_binom_factor_le_div`).  This
    is the step that makes the upper bound `C(2n,n) ≤ (2n)^{√(2n)}·4^{2n/3}`
    available (the low block is primorial-bounded by `4^{2n/3}`).  ∅-axiom. -/
theorem central_binom_factorization_le_two_thirds {n : Nat} (hn : 3 ≤ n)
    (hnobig : ∀ p, IsPrime213 p → n < p → p ≤ 2 * n → False) :
    binom (2 * n) n
      = primePowProd (fun p => vp p (binom (2 * n) n)) (primesIn 0 (2 * n / 3)) :=
  prod_prime_pow_eq (central_binom_pos n)
    (fun _q hq hd => central_binom_factor_le_div hq hn hnobig hd)

/-! ## §6 — the Erdős upper bound `C(2n,n) ≤ 4^{2n/3}·(2n)^{√(2n)}` -/

/-- Pure pow-monotone-in-exponent: `1 ≤ a → m ≤ n → aᵐ ≤ aⁿ` (induction on the gap;
    `aᵏ⁺¹ = aᵏ·a ≥ aᵏ`). -/
private theorem pow_le_pow_right_le {a : Nat} (ha : 1 ≤ a) :
    ∀ {m d : Nat}, a ^ m ≤ a ^ (m + d) := by
  intro m d
  induction d with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      have hpow : a ^ (m + (k + 1)) = a ^ (m + k) * a := by
        rw [← Nat.add_assoc]; exact Nat.pow_succ a (m + k)
      rw [hpow]
      calc a ^ m ≤ a ^ (m + k) := ih
        _ = a ^ (m + k) * 1 := (Nat.mul_one _).symm
        _ ≤ a ^ (m + k) * a := Nat.mul_le_mul (Nat.le_refl _) ha

private theorem pow_le_pow_of_le {a m n : Nat} (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd]; exact pow_le_pow_right_le ha

/-- ★★★ **The Erdős upper bound.**  If no prime lies in `(n, 2n]` (`n ≥ 3`, and the
    arithmetically-true `√(2n) ≤ 2n/3`), then

      `C(2n,n) ≤ 4^{2n/3} · (2n)^{√(2n)}`.

    Split the collapsed product `∏_{p ≤ 2n/3} p^{vₚ(C)}` at `√(2n)`:
    - primes `≤ √(2n)`: each block `p^{vₚ(C)} ≤ 2n` (Kummer), and there are
      `≤ √(2n)` of them, so the low part is `≤ (2n)^{√(2n)}`;
    - primes `√(2n) < p ≤ 2n/3`: `vₚ(C) ≤ 1` (since `p² > 2n`), so `p^{vₚ(C)} ≤ p`,
      and `∏ p ≤ ∏_{p ≤ 2n/3} p ≤ 4^{2n/3}` (primorial).
    Contradicts `4ⁿ ≤ (2n+1)·C(2n,n)` for large `n` — the crossover (item 3).  ∅-axiom. -/
theorem central_binom_upper_bound {n : Nat} (hn : 3 ≤ n)
    (hsplit : isqrt (2 * n) ≤ 2 * n / 3)
    (hnobig : ∀ p, IsPrime213 p → n < p → p ≤ 2 * n → False) :
    binom (2 * n) n ≤ 4 ^ (2 * n / 3) * (2 * n) ^ (isqrt (2 * n)) := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) hn
  have h2n1 : 1 ≤ 2 * n := Nat.le_trans hn1 (by rw [Nat.two_mul]; exact Nat.le_add_left n n)
  have hfact : binom (2 * n) n
      = primePowProd (fun p => vp p (binom (2 * n) n)) (primesIn 0 (2 * n / 3)) :=
    central_binom_factorization_le_two_thirds hn hnobig
  have hsp : primesIn 0 (2 * n / 3)
      = primesIn (isqrt (2 * n)) (2 * n / 3) ++ primesIn 0 (isqrt (2 * n)) :=
    primesIn_split (Nat.zero_le _) hsplit
  rw [hfact, hsp, primePowProd_append]
  -- low block ≤ (2n)^{√2n}
  have hlow : primePowProd (fun p => vp p (binom (2 * n) n)) (primesIn 0 (isqrt (2 * n)))
      ≤ (2 * n) ^ (isqrt (2 * n)) := by
    have hb := primePowProd_le_pow_length (fun p => vp p (binom (2 * n) n)) (2 * n)
      (ps := primesIn 0 (isqrt (2 * n)))
      (fun p hp => prime_pow_vp_central_binom_le (mem_primesIn_prime hp) hn1)
    exact Nat.le_trans hb (pow_le_pow_of_le h2n1 primesIn_length_le)
  -- high block ≤ 4^{2n/3}
  have hhigh : primePowProd (fun p => vp p (binom (2 * n) n)) (primesIn (isqrt (2 * n)) (2 * n / 3))
      ≤ 4 ^ (2 * n / 3) := by
    have hb := primePowProd_le_listProd (fun p => vp p (binom (2 * n) n))
      (ps := primesIn (isqrt (2 * n)) (2 * n / 3))
      (fun p hp => by
        have hpp : IsPrime213 p := mem_primesIn_prime hp
        have hgt : isqrt (2 * n) < p := mem_primesIn_gt hp
        have hKp : isqrt (2 * n) + 1 ≤ p := hgt
        have hsq : 2 * n < p * p :=
          Nat.lt_of_lt_of_le (isqrt_bracket (2 * n)).2 (Nat.mul_le_mul hKp hKp)
        exact central_binom_pow_le_self hpp hn1 hsq)
    have hmono : listProd (primesIn (isqrt (2 * n)) (2 * n / 3)) ≤ listProd (primesIn 0 (2 * n / 3)) := by
      rw [hsp, listProd_append]
      exact Nat.le_mul_of_pos_right _
        (listProd_pos (fun p hp => Nat.lt_of_lt_of_le (by decide) (mem_primesIn_prime hp).1))
    exact Nat.le_trans (Nat.le_trans hb hmono) (primorial_le_four_pow (2 * n / 3))
  exact Nat.mul_le_mul hhigh hlow

/-! ## §7 — Bertrand for large `n`, reduced to the crossover inequality -/

/-- ★★★ **Bertrand's postulate for large `n`, modulo the crossover.**  Given the two
    pure-`Nat` facts that hold for `n ≥ N₀` — `√(2n) ≤ 2n/3` and the **crossover**
    `(2n+1)·4^{2n/3}·(2n)^{√(2n)} < 4ⁿ` — there is a prime `p` with `n < p ≤ 2n`.

    Constructive (no `by_contra`/Classical): case on whether `primesIn n (2n)` is
    empty.  Nonempty ⟹ its head is the witness.  Empty ⟹ no prime in `(n,2n]`, so
    the Erdős upper bound `C(2n,n) ≤ 4^{2n/3}·(2n)^{√(2n)}` holds; combined with the
    lower bound `4ⁿ ≤ (2n+1)·C(2n,n)` and the crossover, `4ⁿ < 4ⁿ` — contradiction.
    The remaining work for full Bertrand is purely discharging the two hypotheses
    (the asymptotic, `n ≥ N₀`) + a finite prime chain for `n < N₀`.  ∅-axiom. -/
theorem exists_prime_in_window {n : Nat} (hn : 3 ≤ n)
    (hsplit : isqrt (2 * n) ≤ 2 * n / 3)
    (hcross : (2 * n + 1) * (4 ^ (2 * n / 3) * (2 * n) ^ (isqrt (2 * n))) < 4 ^ n) :
    ∃ p, IsPrime213 p ∧ n < p ∧ p ≤ 2 * n := by
  cases hl : primesIn n (2 * n) with
  | cons q rest =>
      have hmem : q ∈ primesIn n (2 * n) := by rw [hl]; exact List.Mem.head rest
      exact ⟨q, mem_primesIn_prime hmem, mem_primesIn_gt hmem, mem_primesIn_le hmem⟩
  | nil =>
      exfalso
      have hnobig : ∀ p, IsPrime213 p → n < p → p ≤ 2 * n → False := by
        intro p hp h1 h2
        have hpm : p ∈ primesIn n (2 * n) := mem_primesIn hp h1 h2
        rw [hl] at hpm; nomatch hpm
      have hlow : 4 ^ n ≤ (2 * n + 1) * binom (2 * n) n :=
        four_pow_le_succ_mul_central_binom n
      have hupp : binom (2 * n) n ≤ 4 ^ (2 * n / 3) * (2 * n) ^ (isqrt (2 * n)) :=
        central_binom_upper_bound hn hsplit hnobig
      have hcomb : 4 ^ n ≤ (2 * n + 1) * (4 ^ (2 * n / 3) * (2 * n) ^ (isqrt (2 * n))) :=
        Nat.le_trans hlow (Nat.mul_le_mul (Nat.le_refl (2 * n + 1)) hupp)
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hcross hcomb)

/-- ★★★ **Explicit prime factorization of the central binomial coefficient.**
    `C(2n,n) = ∏_{p ≤ 2n, prime} p^{vₚ(C(2n,n))}` — the FTA product form
    (`prod_prime_pow_eq`) instantiated at `m = C(2n,n)`, `B = 2n`, with the index
    set pinned by `central_binom_prime_factors_le`.  The object Erdős upper-bounds
    by size-ranges (`primePowProd_append` over `primesIn_split`).  ∅-axiom. -/
theorem central_binom_factorization (n : Nat) (hn : 1 ≤ n) :
    binom (2 * n) n
      = primePowProd (fun p => vp p (binom (2 * n) n)) (primesIn 0 (2 * n)) :=
  prod_prime_pow_eq (central_binom_pos n)
    (fun _q hq hd => central_binom_prime_factors_le hq hn hd)

end E213.Lib.Math.NumberTheory.CentralBinomFactorization
