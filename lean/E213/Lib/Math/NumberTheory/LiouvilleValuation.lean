import E213.Lib.Math.NumberTheory.MobiusMultiplicative
import E213.Lib.Math.NumberTheory.MobiusDivisorSum
import E213.Lib.Math.NumberTheory.SquareValuation
import E213.Lib.Math.NumberTheory.LiouvilleFunction
import E213.Meta.Int213.PolyIntM

/-!
# Liouville (valuation form) `λV(n) = (−1)^Ω(n)` — completely multiplicative (∅-axiom)

A clean ∅-axiom **completely multiplicative** function built from the prime-exponent
lattice: `λV n = ∏_{p prime ≤ n} (−1)^{vp p n}`, the guarded product mirroring
`MobiusMultiplicative.muStruct` but with the Liouville per-prime factor
`(−1)^{vp p n}` (which, unlike μ's `mFactor`, is *completely* multiplicative — no
coprimality needed) in place of `mFactor`.

  * `lProd_mul` / `lambdaV_mul` — `λV(m·n) = λV(m)·λV(n)` for ALL positive `m,n`
    (incl. non-coprime), via `vp_mul` (valuation additivity, prime `p`) +
    `powInt_add` (`(−1)^{a+b} = (−1)^a·(−1)^b`).  The GENERAL complete
    multiplicativity the trial-division `liouville` table only sampled.
  * `lambdaV_prime_pow` — `λV(pⁱ) = (−1)ⁱ` (window isolates the single prime).
  * `lambdaV_divisorSum_mul` — `Σ_{d∣ab} λV(d) = (Σ_{d∣a})·(Σ_{d∣b})` for coprime
    `a,b` (the summatory function is multiplicative).
  * ★★ `lambdaV_divisor_sum_isSquare` / `lambdaV_divisor_sum_eq_one_iff_isSquare` —
    `Σ_{d∣n} λV(d) = 1` iff `n` is a perfect square, else `0`, for ALL `n > 0`
    (the general theorem the corpus only sampled as `liouville_divisor_sum_table`,
    `n ≤ 16`).  Strong induction on the smallest-prime-power split
    (`exists_prime_pow_cofactor`) + `Σ_{i=0}^k (−1)ⁱ = [k even]` (`altSum_parity`)
    + `isSquare_prime_pow_iff` + `coprime_isSquare_mul`.
  * `lambdaV_eq_liouville_range` — `λV = liouville` value-for-value on `n=1..16`
    (bridge to the corpus trial-division `liouville`; general bridge open, same
    `muAux`-scan-invariant obstruction as μ).
-/

namespace E213.Lib.Math.NumberTheory.LiouvilleValuation

open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpMul (IsPrime213 vp_mul vp_self_pow)
open E213.Lib.Math.NumberTheory.MobiusMultiplicative
  (primB prime_of_primB not_dvd_of_gt vp_zero_of_not_dvd)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum (primB_of_prime)
open E213.Meta.Int213.PolyIntM (powInt powInt_add)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberTheory.MobiusFunction (sumZ divisorSumZ)
open E213.Lib.Math.NumberTheory.EulerTotient (dvdInd)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum
  (divisorSumZ_product_reindex inner_factor sumZ_mul_right
   coprime_of_divisors divisorSumZ_prime_pow_reindex sumPowZ
   exists_prime_pow_cofactor castOne_mul castZero_mul)
open E213.Lib.Math.NumberTheory.MobiusPrimeCase
  (sumZ_succ sumZ_congr)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative
  (dvdInd_eq_one_iff dvdInd_zero_or_one)
open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.SquareCharacterization (IsSquare coprime_isSquare_mul)
open E213.Lib.Math.NumberTheory.SigmaParityComplete (isSquare_prime_pow_iff)

/-! ## §1 — the Liouville per-prime factor `(−1)^{vp q n}`, guarded by primality -/

/-- The guarded per-candidate Liouville factor: `(−1)^{vp q n}` at primes, `1` elsewhere. -/
def lFactor (q n : Nat) : Int := cond (primB q) (powInt (-1) (vp q n)) 1

theorem lFactor_nonprime {q n : Nat} (h : primB q = false) : lFactor q n = 1 := by
  unfold lFactor; rw [h]; rfl

theorem lFactor_prime {q n : Nat} (h : primB q = true) :
    lFactor q n = powInt (-1) (vp q n) := by
  unfold lFactor; rw [h]; rfl

/-- `powInt (-1) 0 = 1`. -/
theorem powInt_neg_one_zero : powInt (-1 : Int) 0 = 1 := rfl

/-! ## §2 — complete multiplicativity of the guarded factor (ALL positive pairs) -/

/-- ★ **Per-candidate complete multiplicativity**: for `a,b > 0` and any `q`,
    `lFactor q (a·b) = lFactor q a · lFactor q b`.  No coprimality: the prime
    branch uses only `vp_mul` (valuation additivity) + `powInt_add`. -/
theorem lFactor_mul {a b : Nat} (ha : 0 < a) (hb : 0 < b) (q : Nat) :
    lFactor q (a * b) = lFactor q a * lFactor q b := by
  cases hq : primB q with
  | false =>
      rw [lFactor_nonprime hq, lFactor_nonprime hq, lFactor_nonprime hq]
      rw [E213.Meta.Int213.mul_one]
  | true =>
      have hpr : IsPrime213 q := prime_of_primB hq
      rw [lFactor_prime hq, lFactor_prime hq, lFactor_prime hq]
      rw [vp_mul hpr ha hb, powInt_add]

/-! ## §3 — the guarded product over candidates `2 .. n+1` -/

/-- `lProd start n len = ∏_{j<len} lFactor (start + j) n`. -/
def lProd (start n : Nat) : Nat → Int
  | 0       => 1
  | len + 1 => lProd start n len * lFactor (start + len) n

theorem lProd_zero (start n : Nat) : lProd start n 0 = 1 := rfl

theorem lProd_succ (start n len : Nat) :
    lProd start n (len + 1) = lProd start n len * lFactor (start + len) n := rfl

/-- ★★ **Guarded-product complete multiplicativity** (fixed window): for `a,b > 0`,
    `lProd start (a·b) len = lProd start a len · lProd start b len`. -/
theorem lProd_mul {a b : Nat} (ha : 0 < a) (hb : 0 < b) (start : Nat) :
    ∀ len, lProd start (a * b) len = lProd start a len * lProd start b len
  | 0       => by rw [lProd_zero, lProd_zero, lProd_zero, E213.Meta.Int213.mul_one]
  | len + 1 => by
      rw [lProd_succ, lProd_succ, lProd_succ,
          lProd_mul ha hb start len,
          lFactor_mul ha hb (start + len)]
      generalize lProd start a len = PA
      generalize lProd start b len = PB
      generalize lFactor (start + len) a = GA
      generalize lFactor (start + len) b = GB
      ring_intZ

/-! ## §4 — window-length independence ⇒ global complete multiplicativity -/

/-- Tail factor is trivial: for `q > n > 0`, `lFactor q n = 1`. -/
theorem lFactor_one_of_gt {q n : Nat} (hn : 0 < n) (hq : n < q) : lFactor q n = 1 := by
  cases hp : primB q with
  | false => exact lFactor_nonprime hp
  | true =>
      have hpr := prime_of_primB hp
      rw [lFactor_prime hp]
      rw [vp_zero_of_not_dvd hpr hn (not_dvd_of_gt hn hq)]
      rfl

/-- Window extension by trivial tail: if every added candidate exceeds `n`,
    extending the window leaves the product unchanged. -/
theorem lProd_extend {n : Nat} (hn : 0 < n) (start : Nat) :
    ∀ (len extra : Nat), (∀ j, len ≤ j → n < start + j) →
      lProd start n (len + extra) = lProd start n len
  | len, 0,         _  => by rw [Nat.add_zero]
  | len, extra + 1, hj => by
      rw [show len + (extra + 1) = (len + extra) + 1 from by rw [Nat.add_assoc]]
      rw [lProd_succ]
      rw [lFactor_one_of_gt hn (hj (len + extra) (Nat.le_add_right len extra))]
      rw [E213.Meta.Int213.mul_one]
      exact lProd_extend hn start len extra hj

/-- Window stability at `start = 2`: for `L ≥ n`, `lProd 2 n L = lProd 2 n n`. -/
theorem lProd2_stable {n : Nat} (hn : 0 < n) {L : Nat} (hL : n ≤ L) :
    lProd 2 n L = lProd 2 n n := by
  obtain ⟨extra, hextra⟩ := Nat.le.dest hL
  rw [← hextra]
  exact lProd_extend hn 2 n extra (fun j hj => by
    refine Nat.lt_of_le_of_lt hj ?_
    rw [Nat.add_comm 2 j]
    exact Nat.lt_add_of_pos_right (by decide))

/-- **Liouville function (valuation form)**: the guarded product of `(−1)^{vp p n}`
    over candidate primes `2 .. n+1` (window length `n`, covering every prime
    factor `≤ n`).  `λV 0 = 1` (empty support); `λV n` for `n ≥ 1` is the genuine
    `(−1)^{Ω(n)}`. -/
def lambdaV (n : Nat) : Int := lProd 2 n n

theorem lambdaV_one : lambdaV 1 = 1 := by
  show lProd 2 1 1 = 1
  rw [lProd_succ, lProd_zero, lFactor_one_of_gt (by decide) (by decide),
      E213.Meta.Int213.mul_one]

/-- ★★★ **Complete multiplicativity of `λV`**: `λV(m·n) = λV(m)·λV(n)` for ALL
    positive `m,n` (incl. non-coprime — the property the corpus trial-division
    `liouville` only verified on a finite table). -/
theorem lambdaV_mul {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    lambdaV (m * n) = lambdaV m * lambdaV n := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have hm_le : m ≤ m * n := Nat.le_mul_of_pos_right m hn
  have hn_le : n ≤ m * n := Nat.le_mul_of_pos_left n hm
  have hM : lambdaV m = lProd 2 m (m * n) := (lProd2_stable hm hm_le).symm
  have hN : lambdaV n = lProd 2 n (m * n) := (lProd2_stable hn hn_le).symm
  show lProd 2 (m * n) (m * n) = lambdaV m * lambdaV n
  rw [hM, hN, lProd_mul hm hn 2 (m * n)]

/-! ## §5 — multiplicative divisor sum `D(λV)(a·b) = D(λV)(a)·D(λV)(b)` (coprime)

A direct port of `MobiusDivisorSum.muStruct_divisorSum_mul` with `lambdaV` in place
of `muStruct`; the only function-specific input is `lambdaV_mul` (coprime suffices —
in fact `lambdaV` is completely multiplicative).  The reindex/sum engine is reused. -/

/-- Cell factorization for `lambdaV`. -/
theorem lambdaV_cell_factor {a b : Nat} (hab : gcd213 a b = 1) (i k : Nat) :
    (dvdInd i a : Int) * (dvdInd k b : Int) * lambdaV ((i + 1) * (k + 1))
      = ((dvdInd i a : Int) * lambdaV (i + 1)) * ((dvdInd k b : Int) * lambdaV (k + 1)) := by
  cases dvdInd_zero_or_one i a with
  | inl hi0 =>
    rw [hi0, castZero_mul]
    show (0 : Int) * lambdaV ((i + 1) * (k + 1))
       = ((0 : Nat) : Int) * lambdaV (i + 1) * ((dvdInd k b : Int) * lambdaV (k + 1))
    rw [castZero_mul, E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_mul]
  | inr hi1 =>
    cases dvdInd_zero_or_one k b with
    | inl hk0 =>
      rw [hk0]
      show (dvdInd i a : Int) * ((0 : Int)) * lambdaV ((i + 1) * (k + 1))
         = ((dvdInd i a : Int) * lambdaV (i + 1)) * (((0 : Int)) * lambdaV (k + 1))
      generalize (dvdInd i a : Int) = D
      generalize lambdaV (i + 1) = M1
      generalize lambdaV ((i + 1) * (k + 1)) = MP
      rw [E213.Meta.Int213.PolyIntM.mul_zeroZ, E213.Meta.Int213.zero_mul,
          E213.Meta.Int213.zero_mul, E213.Meta.Int213.PolyIntM.mul_zeroZ]
    | inr hk1 =>
      have hia : (i + 1) ∣ a := (dvdInd_eq_one_iff i a).mp hi1
      have hkb : (k + 1) ∣ b := (dvdInd_eq_one_iff k b).mp hk1
      have hcop : gcd213 (i + 1) (k + 1) = 1 := coprime_of_divisors hab hia hkb
      have hmm : lambdaV ((i + 1) * (k + 1)) = lambdaV (i + 1) * lambdaV (k + 1) :=
        lambdaV_mul (Nat.succ_pos i) (Nat.succ_pos k)
      rw [hmm]
      generalize (dvdInd i a : Int) = D1
      generalize (dvdInd k b : Int) = D2
      generalize lambdaV (i + 1) = M1
      generalize lambdaV (k + 1) = M2
      rw [E213.Meta.Int213.mul_mul_mul_comm D1 D2 M1 M2]

/-- ★★ **Multiplicative divisor sum for `λV`** (coprime `a,b > 0`):
    `divisorSumZ (a·b) λV = divisorSumZ a λV · divisorSumZ b λV`. -/
theorem lambdaV_divisorSum_mul {a b : Nat} (hab : gcd213 a b = 1)
    (ha : 0 < a) (hb : 0 < b) :
    divisorSumZ (a * b) lambdaV
      = divisorSumZ a lambdaV * divisorSumZ b lambdaV := by
  rw [divisorSumZ_product_reindex a b hab ha hb lambdaV]
  have hcells : sumZ a (fun i => sumZ b (fun k =>
        (dvdInd i a : Int) * (dvdInd k b : Int) * lambdaV ((i + 1) * (k + 1))))
      = sumZ a (fun i => sumZ b (fun k =>
        ((dvdInd i a : Int) * lambdaV (i + 1)) * ((dvdInd k b : Int) * lambdaV (k + 1)))) :=
    sumZ_congr a _ _ (fun i _ =>
      sumZ_congr b _ _ (fun k _ => lambdaV_cell_factor hab i k))
  rw [hcells]
  have hfactor : sumZ a (fun i => sumZ b (fun k =>
        ((dvdInd i a : Int) * lambdaV (i + 1)) * ((dvdInd k b : Int) * lambdaV (k + 1))))
      = sumZ a (fun i => ((dvdInd i a : Int) * lambdaV (i + 1))
          * sumZ b (fun k => (dvdInd k b : Int) * lambdaV (k + 1))) :=
    sumZ_congr a _ _ (fun i _ =>
      inner_factor ((dvdInd i a : Int) * lambdaV (i + 1)) b
        (fun k => (dvdInd k b : Int) * lambdaV (k + 1)))
  rw [hfactor]
  rw [sumZ_mul_right (sumZ b (fun k => (dvdInd k b : Int) * lambdaV (k + 1))) a
        (fun i => (dvdInd i a : Int) * lambdaV (i + 1))]
  show (sumZ a (fun i => (dvdInd i a : Int) * lambdaV (i + 1)))
      * (sumZ b (fun k => (dvdInd k b : Int) * lambdaV (k + 1)))
    = divisorSumZ a lambdaV * divisorSumZ b lambdaV
  rfl

/-! ## §6 — `λV` on a prime power: `λV(pⁱ) = (−1)ⁱ`

Mirrors `MobiusMultiplicative.muStruct_prime_pow`: in the window `2 .. pⁱ+1` only
the candidate `q = p` is prime and divides `pⁱ`, so the product isolates the single
factor `(−1)^{vp p (pⁱ)} = (−1)ⁱ`. -/

theorem lProd_all_one (n start : Nat) :
    ∀ len, (∀ j, j < len → lFactor (start + j) n = 1) → lProd start n len = 1
  | 0, _ => lProd_zero start n
  | len + 1, hone => by
    rw [lProd_succ, hone len (Nat.lt_succ_self len), E213.Meta.Int213.mul_one]
    exact lProd_all_one n start len (fun j hj => hone j (Nat.lt_succ_of_lt hj))

theorem lProd_isolate (n start off : Nat) :
    ∀ len, off < len →
      (∀ j, j < len → start + j ≠ start + off → lFactor (start + j) n = 1) →
      lProd start n len = lFactor (start + off) n
  | 0, hoff, _ => absurd hoff (Nat.not_lt_zero off)
  | len + 1, hoff, hone => by
    rw [lProd_succ]
    cases Nat.lt_or_ge off len with
    | inl hlt =>
      have hlast : lFactor (start + len) n = 1 :=
        hone len (Nat.lt_succ_self len)
          (fun he => absurd (E213.Tactic.NatHelper.add_left_cancel he)
            (Nat.ne_of_gt hlt))
      rw [hlast, E213.Meta.Int213.mul_one]
      exact lProd_isolate n start off len hlt
        (fun j hj hne => hone j (Nat.lt_succ_of_lt hj) hne)
    | inr hge =>
      have hoffeq : off = len := Nat.le_antisymm (Nat.le_of_lt_succ hoff) hge
      subst hoffeq
      have hprefix : lProd start n off = 1 :=
        lProd_all_one n start off (fun j hj =>
          hone j (Nat.lt_succ_of_lt hj)
            (fun he => absurd (E213.Tactic.NatHelper.add_left_cancel he) (Nat.ne_of_lt hj)))
      rw [hprefix, E213.Meta.Int213.PolyIntM.one_mulZ]

open E213.Lib.Math.NumberTheory.MobiusDivisorSum (prime_ne_not_dvd_pow)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd)

theorem lFactor_pow_ne {p : Nat} (hp : Prime213 p) {q : Nat} (hqp : q ≠ p) (i : Nat) :
    lFactor q (p ^ i) = 1 := by
  cases hqB : primB q with
  | false => exact lFactor_nonprime hqB
  | true =>
    have hqpr : Prime213 q := prime_of_primB hqB
    have hpi_pos : 0 < p ^ i := Nat.pos_pow_of_pos i (Nat.lt_of_lt_of_le (by decide) hp.1)
    rw [lFactor_prime hqB,
        vp_eq_zero_of_not_dvd hqpr hpi_pos (prime_ne_not_dvd_pow hp hqpr hqp i)]
    rfl

theorem lFactor_pow_self {p : Nat} (hp : Prime213 p) (i : Nat) :
    lFactor p (p ^ i) = powInt (-1) i := by
  rw [lFactor_prime (primB_of_prime hp), vp_self_pow hp i]

/-- ★★ **`λV` on a prime power**: `λV(pⁱ) = (−1)ⁱ` for prime `p`. -/
theorem lambdaV_prime_pow {p : Nat} (hp : Prime213 p) (i : Nat) :
    lambdaV (p ^ i) = powInt (-1) i := by
  have hp2 : 2 ≤ p := hp.1
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  cases i with
  | zero =>
    show lambdaV (p ^ 0) = powInt (-1) 0
    rw [Nat.pow_zero, lambdaV_one]; rfl
  | succ i' =>
    have hpi_pos : 0 < p ^ (i' + 1) := Nat.pos_pow_of_pos (i' + 1) hp0
    have hp_le : p ≤ p ^ (i' + 1) := by
      have : p ^ 1 ≤ p ^ (i' + 1) :=
        Nat.pow_le_pow_right hp0 (Nat.succ_le_succ (Nat.zero_le i'))
      rwa [Nat.pow_one] at this
    show lProd 2 (p ^ (i' + 1)) (p ^ (i' + 1)) = powInt (-1) (i' + 1)
    have hoff : p - 2 < p ^ (i' + 1) :=
      Nat.lt_of_lt_of_le (Nat.sub_lt hp0 (by decide)) hp_le
    have hstartoff : 2 + (p - 2) = p := by
      rw [Nat.add_comm]; exact E213.Tactic.NatHelper.sub_add_cancel hp2
    rw [lProd_isolate (p ^ (i' + 1)) 2 (p - 2) (p ^ (i' + 1)) hoff (fun j _ hne => by
        have hjp : 2 + j ≠ p := fun he => hne (by rw [he, hstartoff])
        exact lFactor_pow_ne hp hjp (i' + 1))]
    rw [hstartoff]
    exact lFactor_pow_self hp (i' + 1)

/-! ## §7 — prime-power divisor sum `D(λV)(pᵏ) = Σ_{i=0}^k (−1)ⁱ = [k even]` -/

/-- The alternating sum `Σ_{i=0}^k (−1)ⁱ`. -/
def altSum : Nat → Int
  | 0     => 1
  | k + 1 => altSum k + powInt (-1) (k + 1)

/-- `sumPowZ λV p k = altSum k` (each `λV(pⁱ) = (−1)ⁱ`). -/
theorem sumPowZ_lambdaV_eq_altSum {p : Nat} (hp : Prime213 p) :
    ∀ k, sumPowZ lambdaV p k = altSum k
  | 0 => by
    show lambdaV (p ^ 0) = altSum 0
    rw [lambdaV_prime_pow hp 0]; rfl
  | k + 1 => by
    show sumPowZ lambdaV p k + lambdaV (p ^ (k + 1)) = altSum k + powInt (-1) (k + 1)
    rw [sumPowZ_lambdaV_eq_altSum hp k, lambdaV_prime_pow hp (k + 1)]

/-- `powInt (-1) (k+2) = powInt (-1) k`: shifting by 2 returns the same sign. -/
theorem powInt_neg_one_add_two (k : Nat) : powInt (-1 : Int) (k + 2) = powInt (-1) k := by
  show powInt (-1 : Int) (k + 1) * (-1) = powInt (-1) k
  show (powInt (-1 : Int) k * (-1)) * (-1) = powInt (-1) k
  generalize powInt (-1 : Int) k = x
  ring_intZ

/-- `altSum (k+2) = altSum k`: two more terms `(−1)^{k+1} + (−1)^{k+2}` cancel. -/
theorem altSum_add_two (k : Nat) : altSum (k + 2) = altSum k := by
  show altSum (k + 1) + powInt (-1) (k + 2) = altSum k
  show (altSum k + powInt (-1) (k + 1)) + powInt (-1) (k + 2) = altSum k
  rw [powInt_neg_one_add_two k]
  show (altSum k + powInt (-1) (k + 1)) + powInt (-1) k = altSum k
  show (altSum k + powInt (-1) k * (-1)) + powInt (-1) k = altSum k
  generalize altSum k = A
  generalize powInt (-1 : Int) k = x
  ring_intZ

/-- ★ **Parity value of the alternating sum**: `altSum k = 1` if `k` even, `0` if odd. -/
theorem altSum_parity : ∀ k,
    (k % 2 = 0 ∧ altSum k = 1) ∨ (k % 2 = 1 ∧ altSum k = 0)
  | 0 => Or.inl ⟨rfl, rfl⟩
  | 1 => Or.inr ⟨rfl, by
      show altSum 0 + powInt (-1) 1 = 0
      show (1 : Int) + powInt (-1) 1 = 0
      show (1 : Int) + powInt (-1) 0 * (-1) = 0
      show (1 : Int) + 1 * (-1) = 0
      rw [E213.Meta.Int213.PolyIntM.one_mulZ]
      exact E213.Meta.Int213.add_neg_cancel 1⟩
  | k + 2 => by
    rw [altSum_add_two k]
    rcases altSum_parity k with ⟨he, hv⟩ | ⟨ho, hv⟩
    · have hmod : (k + 2) % 2 = 0 := by
        rw [E213.Meta.Nat.AddMod213.add_mod (by decide) k 2, he]
      exact Or.inl ⟨hmod, hv⟩
    · have hmod : (k + 2) % 2 = 1 := by
        rw [E213.Meta.Nat.AddMod213.add_mod (by decide) k 2, ho]
      exact Or.inr ⟨hmod, hv⟩

/-- ★★ **Prime-power divisor sum of `λV`** equals the alternating sum:
    `divisorSumZ (pᵏ) λV = altSum k`. -/
theorem lambdaV_divisorSum_prime_pow {p : Nat} (hp : Prime213 p) (k : Nat) :
    divisorSumZ (p ^ k) lambdaV = altSum k := by
  rw [divisorSumZ_prime_pow_reindex hp k lambdaV, sumPowZ_lambdaV_eq_altSum hp k]

/-- ★★ **Prime-power square law**: `D(λV)(pᵏ) = 1` iff `pᵏ` is a square (`k` even),
    `= 0` otherwise. -/
theorem lambdaV_divisorSum_prime_pow_isSquare {p : Nat} (hp : Prime213 p) (k : Nat) :
    (IsSquare (p ^ k) ∧ divisorSumZ (p ^ k) lambdaV = 1)
      ∨ (¬ IsSquare (p ^ k) ∧ divisorSumZ (p ^ k) lambdaV = 0) := by
  rw [lambdaV_divisorSum_prime_pow hp k]
  rcases altSum_parity k with ⟨he, hv⟩ | ⟨ho, hv⟩
  · exact Or.inl ⟨(isSquare_prime_pow_iff hp k).mpr he, hv⟩
  · refine Or.inr ⟨fun hsq => ?_, hv⟩
    have := (isSquare_prime_pow_iff hp k).mp hsq
    rw [ho] at this; exact absurd this (by decide)

/-! ## §8 — assembly: `Σ_{d∣n} λV(d) = [n is a perfect square]` (general `n`)

Strong induction with the smallest-prime-power split `n = pᵏ·m`
(`exists_prime_pow_cofactor`): the divisor sum is multiplicative
(`lambdaV_divisorSum_mul`), the prime-power factor is `[k even]`
(`lambdaV_divisorSum_prime_pow_isSquare`), and `IsSquare` splits across coprime
factors (`coprime_isSquare_mul`).  Result phrased as a value/squareness biconditional
(no `Decidable IsSquare` instance needed). -/

/-- `divisorSumZ 1 λV = 1`. -/
theorem lambdaV_divisorSum_one : divisorSumZ 1 lambdaV = 1 := by
  show sumZ 1 (fun j => (dvdInd j 1 : Int) * lambdaV (j + 1)) = 1
  show sumZ 0 (fun j => (dvdInd j 1 : Int) * lambdaV (j + 1))
      + (dvdInd 0 1 : Int) * lambdaV (0 + 1) = 1
  show (0 : Int) + (dvdInd 0 1 : Int) * lambdaV 1 = 1
  have hd : dvdInd 0 1 = 1 := (dvdInd_eq_one_iff 0 1).mpr ⟨1, rfl⟩
  rw [hd, lambdaV_one, E213.Meta.Int213.zero_add, castOne_mul]

/-- One strong-induction step (extracted for clarity). -/
theorem lambdaV_divisor_sum_step (n : Nat)
    (ih : ∀ j, j < n → 0 < j →
      (IsSquare j ∧ divisorSumZ j lambdaV = 1)
        ∨ (¬ IsSquare j ∧ divisorSumZ j lambdaV = 0))
    (hn : 0 < n) :
    (IsSquare n ∧ divisorSumZ n lambdaV = 1)
      ∨ (¬ IsSquare n ∧ divisorSumZ n lambdaV = 0) := by
  cases Nat.lt_or_ge n 2 with
  | inl hlt =>
    have hn1 : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hn
    subst hn1
    exact Or.inl ⟨⟨1, rfl⟩, lambdaV_divisorSum_one⟩
  | inr hge =>
    obtain ⟨p, k, m, hp, hk1, hm0, hmlt, hcop, hnpk⟩ := exists_prime_pow_cofactor hge
    have hpk_pos : 0 < p ^ k :=
      Nat.pos_pow_of_pos k (Nat.lt_of_lt_of_le (by decide) hp.1)
    subst hnpk
    rw [lambdaV_divisorSum_mul hcop hpk_pos hm0]
    have hpp := lambdaV_divisorSum_prime_pow_isSquare hp k
    have hmm := ih m hmlt hm0
    -- IsSquare (p^k·m) ↔ IsSquare (p^k) ∧ IsSquare m (used via .mp/.mpr, no propext rw)
    have hiff := coprime_isSquare_mul hcop
    rcases hpp with ⟨hsqp, hvp⟩ | ⟨hnsqp, hvp⟩
    · rcases hmm with ⟨hsqm, hvm⟩ | ⟨hnsqm, hvm⟩
      · exact Or.inl ⟨hiff.mpr ⟨hsqp, hsqm⟩, by rw [hvp, hvm, E213.Meta.Int213.mul_one]⟩
      · exact Or.inr ⟨fun h => hnsqm (hiff.mp h).2,
          by rw [hvp, hvm, E213.Meta.Int213.PolyIntM.mul_zeroZ]⟩
    · exact Or.inr ⟨fun h => hnsqp (hiff.mp h).1, by rw [hvp, E213.Meta.Int213.zero_mul]⟩

/-- ★★ **Liouville (valuation form) divisor-sum identity — GENERAL `n`**:
    for `n > 0`, `Σ_{d∣n} λV(d) = 1` iff `n` is a perfect square, and `= 0`
    otherwise.  This is the general theorem the corpus only verified as a table
    (`liouville_divisor_sum_table`, `n ≤ 16`). -/
theorem lambdaV_divisor_sum_isSquare (n : Nat) (hn : 0 < n) :
    (IsSquare n ∧ divisorSumZ n lambdaV = 1)
      ∨ (¬ IsSquare n ∧ divisorSumZ n lambdaV = 0) := by
  induction n using Nat.strongRecOn with
  | ind n ih => exact lambdaV_divisor_sum_step n (fun j hj hjpos => ih j hj hjpos) hn

/-- The divisor sum is always `0` or `1`. -/
theorem lambdaV_divisor_sum_zero_or_one (n : Nat) (hn : 0 < n) :
    divisorSumZ n lambdaV = 0 ∨ divisorSumZ n lambdaV = 1 := by
  rcases lambdaV_divisor_sum_isSquare n hn with ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inr h
  · exact Or.inl h

/-- `Σ_{d∣n} λV(d) = 1 ↔ IsSquare n` (general `n > 0`). -/
theorem lambdaV_divisor_sum_eq_one_iff_isSquare (n : Nat) (hn : 0 < n) :
    divisorSumZ n lambdaV = 1 ↔ IsSquare n := by
  constructor
  · intro h
    rcases lambdaV_divisor_sum_isSquare n hn with ⟨hsq, _⟩ | ⟨_, h0⟩
    · exact hsq
    · exfalso; rw [h0] at h; exact absurd h (by decide)
  · intro hsq
    rcases lambdaV_divisor_sum_isSquare n hn with ⟨_, h1⟩ | ⟨hns, _⟩
    · exact h1
    · exact absurd hsq hns

/-! ## §9 — bridge to the corpus trial-division `liouville` (range-verified)

The general bridge `∀ n, λV n = liouville n` requires relating the
product-over-candidate-primes to the magnitude-ordered `liouvilleAux` scan — the
same open `muAux`-style scan-correctness invariant noted in `MobiusMultiplicative`
(frontier `mobius_divisor_sum_general.md`).  These `decide`-checked instances
confirm `λV` reproduces the corpus `liouville` value-for-value. -/

open E213.Lib.Math.NumberTheory.LiouvilleFunction (liouville)

/-- `λV = liouville` on `n = 1 .. 16` (they agree wherever `liouville` is defined;
    `λV 0 = 1` empty product vs `liouville 0 = 0`). -/
theorem lambdaV_eq_liouville_range :
    lambdaV 1 = liouville 1 ∧ lambdaV 2 = liouville 2 ∧ lambdaV 3 = liouville 3 ∧
    lambdaV 4 = liouville 4 ∧ lambdaV 5 = liouville 5 ∧ lambdaV 6 = liouville 6 ∧
    lambdaV 7 = liouville 7 ∧ lambdaV 8 = liouville 8 ∧ lambdaV 9 = liouville 9 ∧
    lambdaV 10 = liouville 10 ∧ lambdaV 11 = liouville 11 ∧ lambdaV 12 = liouville 12 ∧
    lambdaV 13 = liouville 13 ∧ lambdaV 14 = liouville 14 ∧ lambdaV 15 = liouville 15 ∧
    lambdaV 16 = liouville 16 := by decide

/-- Smoke: complete multiplicativity reproduces a non-coprime Liouville value
    `λV(4) = λV(2)·λV(2)`. -/
theorem lambdaV_mul_smoke : lambdaV (2 * 2) = lambdaV 2 * lambdaV 2 :=
  lambdaV_mul (by decide) (by decide)

end E213.Lib.Math.NumberTheory.LiouvilleValuation
