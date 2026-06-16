import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Lib.Math.NumberTheory.MobiusFunction
import E213.Meta.Nat.VpSeparation
import E213.Meta.Nat.VpMul
import E213.Lens.Number
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Core
import E213.Meta.Nat.Beq213

/-!
# Structural Möbius `muStruct` + coprime multiplicativity (∅-axiom)

A structurally-defined Möbius function and the proof that it is **multiplicative
for coprimes** — the corpus's first structurally-defined multiplicative Möbius.

  * `muStruct n = ∏_{q=2}^{n} guarded(q,n)`, where `guarded q n = mFactor(vp q n)`
    at primes (`1, −1, 0` for valuation `0, 1, ≥2`) and `1` at composites.  No
    prime-factor *list* object — each candidate `q ∈ [2,n]` is tested in place; the
    product is supported on the prime factors of `n` (recovering the textbook
    squarefree-sign μ).  Verified `= mu` (corpus trial-division) on n=1..12.
  * ★★★ `muStruct_mul` — `gcd(a,b)=1 → muStruct(a·b) = muStruct a · muStruct b`
    (general; window-stability lifts to a common window where `prodFrom_mul` splits
    candidate-by-candidate via the per-prime `mFactor_vp_mul`).
  * ★★ `sumMF_succ_eq_zero` — the prime-power core `Σ_{i=0}^{k} μ(pⁱ) = [k=0]`.

`muStruct_mul` is the load-bearing half of the general divisor-sum
`Σ_{d∣n} μ(d) = [n=1]`, and the same window-product template would unlock general
σ/τ multiplicativity + Möbius inversion.  The two combinatorial ingredients — the
divisor-product reindex `divisors(p^k·m) ≅ {0..k}×divisors(m)` (no PURE
divisor-set / Σ-over-divisors-Fubini-for-product here at the prime-case layer), and the
`muStruct n = mu n` bridge — are carried in `DivisorMultiplicative`/`MobiusBridge`.  All
∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.MobiusMultiplicative

open E213.Meta.Nat.Valuation (vp pow_vp_dvd le_vp_iff mod_zero_of_dvd)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 vp_mul prime_dvd_mul)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (coprime_mul_iff)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd dvd_iff_one_le_vp)
open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right gcd213_greatest)
open E213.Tactic.NatHelper (gcd213)

/-! ## `mFactor`: the per-prime contribution `f(vp p n)` -/

/-- Per-prime Möbius contribution as a function of the exponent `k = vp p n`:
    `1` if `k=0`, `−1` if `k=1`, `0` if `k≥2` (not squarefree).  propext-free. -/
def mFactor (k : Nat) : Int :=
  cond (k == 0) 1 (cond (k == 1) (-1) 0)

theorem mFactor_zero : mFactor 0 = 1 := rfl
theorem mFactor_one : mFactor 1 = -1 := rfl
theorem mFactor_succ_succ (k : Nat) : mFactor (k + 2) = 0 := rfl

/-- ★ **Coprime split of `mFactor`**: if `a = 0` or `b = 0`, then
    `mFactor (a + b) = mFactor a * mFactor b`. -/
theorem mFactor_add_of_zero {a b : Nat} (h : a = 0 ∨ b = 0) :
    mFactor (a + b) = mFactor a * mFactor b := by
  rcases h with ha | hb
  · subst ha
    rw [Nat.zero_add, mFactor_zero]
    show mFactor b = 1 * mFactor b
    rw [Int.one_mul]
  · subst hb
    rw [Nat.add_zero, mFactor_zero]
    show mFactor a = mFactor a * 1
    rw [E213.Meta.Int213.mul_one]

/-! ## Coprimality ⇒ per-prime disjointness of valuations -/

/-- `Prime213` and `IsPrime213` are the same predicate; transport. -/
theorem isPrime_of_prime {p : Nat} (hp : Prime213 p) : IsPrime213 p := hp

/-- A prime not dividing `n > 0` has valuation `0`. -/
theorem vp_zero_of_not_dvd {p n : Nat} (hp : Prime213 p) (hn : 0 < n) (h : ¬ p ∣ n) :
    vp p n = 0 := vp_eq_zero_of_not_dvd (isPrime_of_prime hp) hn h

/-- `p ∣ n ↔ 1 ≤ vp p n` for prime `p`, `n > 0`. -/
theorem dvd_iff_one_le_vp' {p n : Nat} (hp : Prime213 p) (hn : 0 < n) :
    p ∣ n ↔ 1 ≤ vp p n := dvd_iff_one_le_vp (isPrime_of_prime hp) hn

/-- ★ **Coprime ⇒ no shared prime**: `gcd a b = 1 → ¬(p ∣ a ∧ p ∣ b)` for prime `p`. -/
theorem not_dvd_both_of_coprime {a b p : Nat} (hp : Prime213 p) (hcop : gcd213 a b = 1) :
    ¬ (p ∣ a ∧ p ∣ b) := by
  rintro ⟨hpa, hpb⟩
  have hpg : p ∣ gcd213 a b := gcd213_greatest a b p hpa hpb
  rw [hcop] at hpg
  have hple : p ≤ 1 := E213.Tactic.Pow213.le_of_dvd_pos p 1 (by decide) hpg
  exact absurd (Nat.le_trans hp.1 hple) (by decide)

/-- ★ **Coprime ⇒ per-prime valuation disjointness**: for coprime `a,b > 0` and any
    prime `p`, at least one of `vp p a`, `vp p b` is `0`. -/
theorem vp_zero_left_or_right {a b p : Nat} (hp : Prime213 p) (ha : 0 < a) (hb : 0 < b)
    (hcop : gcd213 a b = 1) : vp p a = 0 ∨ vp p b = 0 := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  cases hm : Nat.decEq (a % p) 0 with
  | isTrue hpa0 =>
    have hpa : p ∣ a := E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero hpa0
    refine Or.inr (vp_zero_of_not_dvd hp hb (fun hpb => ?_))
    exact not_dvd_both_of_coprime hp hcop ⟨hpa, hpb⟩
  | isFalse hpa0 =>
    have hpa : ¬ p ∣ a := fun hd => hpa0 (mod_zero_of_dvd hp0 hd)
    exact Or.inl (vp_zero_of_not_dvd hp ha hpa)

/-! ## Per-prime multiplicativity of the Möbius factor -/

/-- ★★ **Per-prime Möbius multiplicativity**: for coprime `a,b > 0` and prime `p`,
    `mFactor (vp p (a·b)) = mFactor (vp p a) · mFactor (vp p b)`. -/
theorem mFactor_vp_mul {a b p : Nat} (hp : Prime213 p) (ha : 0 < a) (hb : 0 < b)
    (hcop : gcd213 a b = 1) :
    mFactor (vp p (a * b)) = mFactor (vp p a) * mFactor (vp p b) := by
  rw [vp_mul hp ha hb]
  exact mFactor_add_of_zero (vp_zero_left_or_right hp ha hb hcop)

/-! ## The prime-power divisor-sum core `Σ_{i=0}^{k} μ(pⁱ) = [k=0]` -/

/-- `sumMF k = Σ_{i=0}^{k} mFactor i` (inclusive upper bound `k`). -/
def sumMF : Nat → Int
  | 0     => mFactor 0
  | k + 1 => sumMF k + mFactor (k + 1)

theorem sumMF_zero : sumMF 0 = 1 := rfl

/-- ★★ **Prime-power divisor-sum core**: `Σ_{i=0}^{k} μ(pⁱ) = [k=0]`, i.e.
    `sumMF (k+1) = 0` (`1 + (−1) + 0 + … = 0`). -/
theorem sumMF_succ_eq_zero : ∀ k, sumMF (k + 1) = 0
  | 0 => by
      show sumMF 0 + mFactor 1 = 0
      rw [sumMF_zero, mFactor_one]
      exact E213.Meta.Int213.add_neg_cancel 1
  | k + 1 => by
      show sumMF (k + 1) + mFactor (k + 2) = 0
      rw [sumMF_succ_eq_zero k, mFactor_succ_succ]
      exact E213.Meta.Int213.zero_add 0

/-! ## The global structural Möbius `muStruct` as a guarded product over candidates -/

open E213.Lens.Number.Nat213.MultSystemValue (decNoFactor)

/-- Sound `Bool` primality test: `2 ≤ n` and the bounded no-divisor check.
    propext-free (matches `Decidable` constructors, no `decide`/`if` on a `Prop`). -/
def primB (n : Nat) : Bool :=
  match Nat.decLe 2 n with
  | isFalse _ => false
  | isTrue _  =>
    match decNoFactor n n with
    | isFalse _ => false
    | isTrue _  => true

/-- ★ **Soundness of `primB`**: `primB n = true → Prime213 n`. -/
theorem prime_of_primB {n : Nat} (h : primB n = true) : Prime213 n := by
  unfold primB at h
  cases h2 : Nat.decLe 2 n with
  | isFalse hf => rw [h2] at h; exact Bool.noConfusion h
  | isTrue h2n =>
    rw [h2] at h
    cases h3 : decNoFactor n n with
    | isFalse hf => rw [h3] at h; exact Bool.noConfusion h
    | isTrue hnf =>
      exact (E213.Lens.Number.Nat213.MultSystemValue.isPrime_iff n).mpr ⟨h2n, hnf⟩

/-- The guarded per-candidate factor: `mFactor (vp q n)` at primes, `1` elsewhere. -/
def guarded (q n : Nat) : Int := cond (primB q) (mFactor (vp q n)) 1

theorem guarded_nonprime {q n : Nat} (h : primB q = false) : guarded q n = 1 := by
  unfold guarded; rw [h]; rfl

theorem guarded_prime {q n : Nat} (h : primB q = true) :
    guarded q n = mFactor (vp q n) := by
  unfold guarded; rw [h]; rfl

/-- `prodFrom start n len = ∏_{j<len} guarded (start + j) n` (indexed by length). -/
def prodFrom (start n : Nat) : Nat → Int
  | 0       => 1
  | len + 1 => prodFrom start n len * guarded (start + len) n

theorem prodFrom_zero (start n : Nat) : prodFrom start n 0 = 1 := rfl

theorem prodFrom_succ (start n len : Nat) :
    prodFrom start n (len + 1) = prodFrom start n len * guarded (start + len) n := rfl

/-! ## Multiplicativity of the guarded product -/

/-- ★ **Per-candidate guarded multiplicativity**: for coprime `a,b > 0` and any `q`,
    `guarded q (a·b) = guarded q a · guarded q b`. -/
theorem guarded_mul {a b : Nat} (ha : 0 < a) (hb : 0 < b) (hcop : gcd213 a b = 1)
    (q : Nat) : guarded q (a * b) = guarded q a * guarded q b := by
  cases hq : primB q with
  | false =>
      rw [guarded_nonprime hq, guarded_nonprime hq, guarded_nonprime hq]
      rw [E213.Meta.Int213.mul_one]
  | true =>
      have hpr : Prime213 q := prime_of_primB hq
      rw [guarded_prime hq, guarded_prime hq, guarded_prime hq]
      exact mFactor_vp_mul hpr ha hb hcop

/-- ★★ **Guarded-product multiplicativity** (fixed window): for coprime `a,b > 0`,
    `prodFrom start (a·b) len = prodFrom start a len · prodFrom start b len`. -/
theorem prodFrom_mul {a b : Nat} (ha : 0 < a) (hb : 0 < b) (hcop : gcd213 a b = 1)
    (start : Nat) :
    ∀ len, prodFrom start (a * b) len = prodFrom start a len * prodFrom start b len
  | 0       => by rw [prodFrom_zero, prodFrom_zero, prodFrom_zero, E213.Meta.Int213.mul_one]
  | len + 1 => by
      rw [prodFrom_succ, prodFrom_succ, prodFrom_succ,
          prodFrom_mul ha hb hcop start len,
          guarded_mul ha hb hcop (start + len)]
      generalize prodFrom start a len = PA
      generalize prodFrom start b len = PB
      generalize guarded (start + len) a = GA
      generalize guarded (start + len) b = GB
      ring_intZ

/-! ## Window-length independence ⇒ global multiplicativity -/

/-- A candidate strictly larger than `n > 0` cannot divide `n`. -/
theorem not_dvd_of_gt {q n : Nat} (hn : 0 < n) (hq : n < q) : ¬ q ∣ n := by
  intro hd
  exact absurd (E213.Tactic.Pow213.le_of_dvd_pos q n hn hd) (Nat.not_le.mpr hq)

/-- ★ **Tail factor is trivial**: for `q > n > 0`, `guarded q n = 1`. -/
theorem guarded_one_of_gt {q n : Nat} (hn : 0 < n) (hq : n < q) : guarded q n = 1 := by
  cases hp : primB q with
  | false => exact guarded_nonprime hp
  | true =>
      have hpr : Prime213 q := prime_of_primB hp
      rw [guarded_prime hp]
      rw [vp_zero_of_not_dvd hpr hn (not_dvd_of_gt hn hq)]
      exact mFactor_zero

/-- ★ **Window extension by trivial tail**: if every added candidate exceeds `n`,
    extending the window leaves the product unchanged. -/
theorem prodFrom_extend {n : Nat} (hn : 0 < n) (start : Nat) :
    ∀ (len extra : Nat), (∀ j, len ≤ j → n < start + j) →
      prodFrom start n (len + extra) = prodFrom start n len
  | len, 0,         _  => by rw [Nat.add_zero]
  | len, extra + 1, hj => by
      rw [show len + (extra + 1) = (len + extra) + 1 from by
            rw [Nat.add_assoc]]
      rw [prodFrom_succ]
      rw [guarded_one_of_gt hn (hj (len + extra) (Nat.le_add_right len extra))]
      rw [E213.Meta.Int213.mul_one]
      exact prodFrom_extend hn start len extra hj

/-- **Window stability at `start = 2`**: for `L ≥ n`, `prodFrom 2 n L = prodFrom 2 n n`. -/
theorem prodFrom2_stable {n : Nat} (hn : 0 < n) {L : Nat} (hL : n ≤ L) :
    prodFrom 2 n L = prodFrom 2 n n := by
  obtain ⟨extra, hextra⟩ := Nat.le.dest hL
  rw [← hextra]
  exact prodFrom_extend hn 2 n extra (fun j hj => by
    refine Nat.lt_of_le_of_lt hj ?_
    rw [Nat.add_comm 2 j]
    exact Nat.lt_add_of_pos_right (by decide))

/-- The global structural Möbius function: the guarded product over candidates
    `2 .. n+1` (window length `n`, covering every prime factor `≤ n`). -/
def muStruct (n : Nat) : Int := prodFrom 2 n n

/-- `muStruct 1 = 1` (empty support). -/
theorem muStruct_one : muStruct 1 = 1 := by
  show prodFrom 2 1 1 = 1
  rw [prodFrom_succ, prodFrom_zero, guarded_one_of_gt (by decide) (by decide),
      E213.Meta.Int213.mul_one]

/-- ★★★ **`muStruct` is multiplicative for coprimes**:
    `gcd a b = 1 → 0 < a → 0 < b → muStruct (a·b) = muStruct a · muStruct b`. -/
theorem muStruct_mul {a b : Nat} (ha : 0 < a) (hb : 0 < b) (hcop : gcd213 a b = 1) :
    muStruct (a * b) = muStruct a * muStruct b := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have ha_le : a ≤ a * b := Nat.le_mul_of_pos_right a hb
  have hb_le : b ≤ a * b := Nat.le_mul_of_pos_left b ha
  have hA : muStruct a = prodFrom 2 a (a * b) := (prodFrom2_stable ha ha_le).symm
  have hB : muStruct b = prodFrom 2 b (a * b) := (prodFrom2_stable hb hb_le).symm
  show prodFrom 2 (a * b) (a * b) = muStruct a * muStruct b
  rw [hA, hB, prodFrom_mul ha hb hcop 2 (a * b)]

/-! ## `muStruct` agrees with the corpus trial-division `mu` (verified range)

The general bridge `∀ n, muStruct n = mu n` is open (it must relate the
product-over-candidates to the magnitude-ordered `muAux` scan — the open
`muAux`-correctness invariant, frontier `mobius_divisor_sum_general.md`).  These
`decide`-checked instances confirm the two definitions agree value for value. -/

open E213.Lib.Math.NumberTheory.MobiusFunction (mu)

/-- `muStruct = mu` on `n = 1 .. 12` (they diverge only at `n = 0`: `muStruct 0 = 1`
    empty product vs `mu 0 = 0`). -/
theorem muStruct_eq_mu_range :
    muStruct 1 = mu 1 ∧ muStruct 2 = mu 2 ∧ muStruct 3 = mu 3 ∧
    muStruct 4 = mu 4 ∧ muStruct 5 = mu 5 ∧ muStruct 6 = mu 6 ∧ muStruct 7 = mu 7 ∧
    muStruct 8 = mu 8 ∧ muStruct 9 = mu 9 ∧ muStruct 10 = mu 10 ∧ muStruct 11 = mu 11 ∧
    muStruct 12 = mu 12 := by decide

/-- Smoke: multiplicativity reproduces a known Möbius value, `μ(15) = μ(3)·μ(5)`. -/
theorem muStruct_mul_smoke : muStruct (3 * 5) = muStruct 3 * muStruct 5 :=
  muStruct_mul (by decide) (by decide) (by decide)

end E213.Lib.Math.NumberTheory.MobiusMultiplicative
