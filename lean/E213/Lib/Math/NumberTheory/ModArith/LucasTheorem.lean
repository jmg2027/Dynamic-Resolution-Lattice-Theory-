import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChoosePrime
import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.Valuation
import E213.Meta.Tactic.Pow213

/-!
# Lucas' theorem — core: prime divides interior binomial-row entries (`freshman_binom`)

Genuinely new piece (vs corpus): the corpus `UniversalFLT` / `ChoosePrime`
prove `p ∣ choose p i` only under the **gcd-encoded** primality hypothesis
(`∀ m, 0 < m < p → (modBezout m p).1 = 1`) or by supplying an explicit
`ModInverse` witness.  Here we derive it from the **abstract `Prime213`
predicate** (`PrimeValuation`) directly, via Euclid's lemma — no inverse
witness, no gcd-encoding.

Chain (`freshman_binom`, `0 < i < p`, write `i = k+1`):
  1. `key_mul_choose_mod`:  `((k+1)·choose p (k+1)) % p = 0`  (from
     `choose_succ_mul`: `(k+1)·choose p (k+1) = p·choose (p-1) k`).
  2. ⇒ `p ∣ (k+1)·choose p (k+1)`.
  3. `prime_dvd_mul` (Euclid):  `p ∣ (k+1) ∨ p ∣ choose p (k+1)`.
  4. `p ∤ (k+1)` since `0 < k+1 < p` (`le_of_dvd_pos` would give `p ≤ k+1`).
  5. ⇒ `p ∣ choose p (k+1)`, i.e. `(choose p (k+1)) % p = 0`.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.LucasTheorem

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_succ_mul)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChoosePrime (key_mul_choose_mod)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 prime_dvd_mul)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Meta.Nat.Valuation (mod_zero_of_dvd)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- A prime does not divide a positive number strictly below it:
    `p ∣ m`, `0 < m`, `m < p` is impossible (`le_of_dvd_pos` gives `p ≤ m`). -/
theorem prime_not_dvd_pos_lt {p m : Nat} (hm : 0 < m) (hlt : m < p)
    (h : p ∣ m) : False :=
  Nat.not_le_of_gt hlt (le_of_dvd_pos p m hm h)

/-- ★★ **`freshman_binom`** (abstract-prime form): for a `Prime213 p` and
    `0 < i < p`, the prime divides the interior binomial-row entry:
    `(choose p i) % p = 0`, i.e. `p ∣ choose p i`.

    PURE.  From `key_mul_choose_mod` + Euclid's lemma `prime_dvd_mul`,
    using `p ∤ i` (since `0 < i < p`). -/
theorem freshman_binom {p i : Nat} (hp : Prime213 p)
    (hi0 : 0 < i) (hip : i < p) :
    (choose p i) % p = 0 := by
  -- write i = k + 1
  match i, hi0 with
  | k + 1, _ =>
    have hp1 : 1 ≤ p := Nat.le_trans (by decide) hp.1
    -- step 1+2: p ∣ (k+1) * choose p (k+1)
    have hmod : ((k + 1) * choose p (k + 1)) % p = 0 := key_mul_choose_mod p k hp1
    have hdvd : p ∣ (k + 1) * choose p (k + 1) := dvd_of_mod_eq_zero hmod
    -- step 3: Euclid
    rcases prime_dvd_mul hp hdvd with hk | hc
    · -- p ∣ (k+1), but 0 < k+1 < p — contradiction
      exact absurd (prime_not_dvd_pos_lt (Nat.succ_pos k) hip hk) (fun f => f)
    · -- p ∣ choose p (k+1) ⇒ mod = 0
      exact mod_zero_of_dvd (Nat.lt_of_lt_of_le (by decide) hp.1) hc

/-- ★★ **`p ∣ choose p i`** divisibility form (companion to `freshman_binom`). -/
theorem prime_dvd_choose {p i : Nat} (hp : Prime213 p)
    (hi0 : 0 < i) (hip : i < p) :
    p ∣ choose p i :=
  dvd_of_mod_eq_zero (freshman_binom hp hi0 hip)

/-! ## Per-prime smoke tests (decidable `Prime213` witnesses) -/

/-- A divisor that is `0` is impossible for a positive `n`: `d ∣ n`, `0 < n`,
    `d = 0` ⇒ `n = 0`.  Pure (no `Decidable (·∣·)`). -/
theorem ne_zero_of_dvd_pos {d n : Nat} (hn : 0 < n) (h : d ∣ n) : d ≠ 0 := by
  intro hd0
  rcases h with ⟨c, hc⟩
  rw [hd0, Nat.zero_mul] at hc
  exact absurd (hc ▸ hn) (Nat.lt_irrefl 0)

/-! `Prime213` witnesses for concrete `p`: from `2 ≤ p` and ruling out each
    candidate divisor `d` with `0 < d ≤ p`, `d ∉ {1,p}`, discharged inline
    per prime below on closed Nat numerals (pure). -/

/-- `Prime213 5` — divisors `2,3,4` ruled out via `5 % d ≠ 0` (pure decEq). -/
theorem prime5 : Prime213 5 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have hle : d ≤ 5 := le_of_dvd_pos d 5 (by decide) hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_pos (by decide) hd
  have hmod : (5 % d) = 0 := mod_zero_of_dvd (Nat.zero_lt_of_ne_zero hd0) hd
  match d, hle with
  | 0, _ => exact absurd rfl hd0
  | 1, _ => exact Or.inl rfl
  | 2, _ => exact absurd hmod (by decide)
  | 3, _ => exact absurd hmod (by decide)
  | 4, _ => exact absurd hmod (by decide)
  | 5, _ => exact Or.inr rfl

/-- Smoke: `choose 5 2 = 10`, `10 % 5 = 0` — via the abstract-prime path. -/
theorem freshman_5_2 : (choose 5 2) % 5 = 0 :=
  freshman_binom prime5 (by decide) (by decide)

theorem freshman_5_3 : (choose 5 3) % 5 = 0 :=
  freshman_binom prime5 (by decide) (by decide)

/-- `Prime213 7` — divisors `2..6` ruled out via `7 % d ≠ 0` (pure decEq,
    no `decide` on `∣`). -/
theorem prime7 : Prime213 7 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have hle : d ≤ 7 := le_of_dvd_pos d 7 (by decide) hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_pos (by decide) hd
  have hmod : (7 % d) = 0 := mod_zero_of_dvd (Nat.zero_lt_of_ne_zero hd0) hd
  match d, hle with
  | 0, _ => exact absurd rfl hd0
  | 1, _ => exact Or.inl rfl
  | 2, _ => exact absurd hmod (by decide)
  | 3, _ => exact absurd hmod (by decide)
  | 4, _ => exact absurd hmod (by decide)
  | 5, _ => exact absurd hmod (by decide)
  | 6, _ => exact absurd hmod (by decide)
  | 7, _ => exact Or.inr rfl

theorem freshman_7_3 : (choose 7 3) % 7 = 0 :=
  freshman_binom prime7 (by decide) (by decide)

/-! ## Lucas digit-step recurrence (verified table)

`lucasStep p n k r s` is the digit-recurrence step of Lucas' theorem:
  `choose (p*n + r) (p*k + s) ≡ choose n k · choose r s  (mod p)`
for low digits `0 ≤ r, s < p`.  The abstract form for all `n k r s`
needs **Vandermonde's identity**
  `choose (m+n) j = Σ_i choose m i · choose n (j-i)`
(absent from the corpus `Binomial.lean`, which has Pascal / symmetry /
`choose_succ_mul` only) plus the mod-p collapse of its cross terms via
`freshman_binom`.  That is the multi-session remainder.  Each concrete
instance below is closed by `decide` (closed Nat arithmetic), pinning the
target and confirming no counterexample across p = 2,3,5,7. -/

/-- The Lucas digit-step congruence as a `Prop` (uniform statement).
    `abbrev` so `decide` unfolds it to the underlying decidable `Nat` equality. -/
abbrev lucasStep (p n k r s : Nat) : Prop :=
  (choose (p * n + r) (p * k + s)) % p
    = ((choose n k) * (choose r s)) % p

/-- p=2, n=3,k=2,r=0,s=0:  choose 6 4 ≡ choose 3 2 · choose 0 0  (mod 2). -/
theorem lucas_step_2 : lucasStep 2 3 2 0 0 := by decide

/-- p=2, n=2,k=1,r=1,s=1:  choose 5 3 ≡ choose 2 1 · choose 1 1  (mod 2). -/
theorem lucas_step_2b : lucasStep 2 2 1 1 1 := by decide

/-- p=3, n=2,k=1,r=1,s=2:  choose 7 5 ≡ choose 2 1 · choose 1 2  (mod 3). -/
theorem lucas_step_3 : lucasStep 3 2 1 1 2 := by decide

/-- p=3, n=3,k=2,r=2,s=1:  choose 11 7 ≡ choose 3 2 · choose 2 1  (mod 3). -/
theorem lucas_step_3b : lucasStep 3 3 2 2 1 := by decide

/-- p=5, n=2,k=1,r=3,s=2:  choose 13 7 ≡ choose 2 1 · choose 3 2  (mod 5). -/
theorem lucas_step_5 : lucasStep 5 2 1 3 2 := by decide

/-- p=7, n=2,k=1,r=4,s=3:  choose 18 10 ≡ choose 2 1 · choose 4 3  (mod 7). -/
theorem lucas_step_7 : lucasStep 7 2 1 4 3 := by decide

/-! ## Full two-digit Lucas congruence instances

For `n = p·n₁ + n₀`, `k = p·k₁ + k₀` (single low digits `n₀,k₀ < p`),
Lucas reads `choose n k ≡ choose n₁ k₁ · choose n₀ k₀ (mod p)`. -/

/-- Full Lucas, p=3, n=7=(2,1)₃, k=5=(1,2)₃. -/
theorem lucas_full_3 :
    (choose 7 5) % 3 = ((choose 2 1) * (choose 1 2)) % 3 := by decide

/-- Full Lucas, p=5, n=13=(2,3)₅, k=7=(1,2)₅. -/
theorem lucas_full_5 :
    (choose 13 7) % 5 = ((choose 2 1) * (choose 3 2)) % 5 := by decide

/-- Full Lucas, p=2, n=6, k=4 two-digit block. -/
theorem lucas_full_2 :
    (choose 6 4) % 2 = ((choose 3 2) * (choose 0 0)) % 2 := by decide

end E213.Lib.Math.NumberTheory.ModArith.LucasTheorem
