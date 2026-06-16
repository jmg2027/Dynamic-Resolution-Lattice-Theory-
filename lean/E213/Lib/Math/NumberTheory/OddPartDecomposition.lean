import E213.Lib.Math.NumberTheory.PerfectNumbers
import E213.Lib.Math.NumberTheory.SigmaParity
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213

/-!
# 2-adic odd-part decomposition + σ-parity reduction to the odd part (∅-axiom)

Provides the 2-adic odd-part decomposition `n = 2^a · odd` (the first crux of the
σ-parity programme, closed in `SigmaParityComplete`).

We define, **subtraction-free** and **reducible** (fuel + `Nat.strongRecOn`
fuel-irrelevance, the `Josephus.lean` template):

  * `stripTwo : Nat → Nat → Nat × Nat` — strip factors of `2` from `n` while even,
    fuel-bounded.  `v2 n := (stripTwo (n+1) n).1`, `oddPart n := (stripTwo (n+1) n).2`.

★★★ `decomp        : 0 < n → n = 2^(v2 n) * oddPart n`
★★★ `oddPart_odd   : 0 < n → oddPart n % 2 = 1`
    `oddPart_pos    : 0 < n → 0 < oddPart n`
★★  `sigma_decomp  : 0 < n → sigma n = sigma (2^(v2 n)) * sigma (oddPart n)`
★★★ `sigma_odd_iff_oddPart : 0 < n → (sigma n % 2 = 1 ↔ sigma (oddPart n) % 2 = 1)`
    — `σ(2^a)` is ALWAYS odd, so the 2-part drops out of σ's parity entirely.

The σ-split uses the corpus σ-framework exactly as `PerfectNumbers.euclid_perfect`:
`gcd(2^a, oddPart n) = 1` (oddPart is odd ⇒ `2 ∤ oddPart`, `coprime_pow_left`), then
`sigma_mul`.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.OddPartDecomposition

open E213.Lib.Math.NumberTheory.SumOfDivisors (sigma)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative (sigma_mul)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 prime_coprime_of_not_dvd)
open E213.Lib.Math.NumberTheory.FactorialLcmDvd (prime2)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (coprime_pow_left)
open E213.Lib.Math.NumberTheory.SigmaParity (sigma_two_pow_odd)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.NatDiv213
  (add_div_right_pos mul_div_cancel_left_pure mul_mod_self_pure div_le_self_pos
   div_lt_of_lt_mul)
open E213.Meta.Nat.AddMod213 (mod_two_zero_or_one mod_mod div_add_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)

/-! ## §1 — the fuel-based 2-stripping function -/

/-- `stripTwo fuel n` strips factors of `2` off `n` while it is even, returning
    `(count, oddpart)`.  Fuel-bounded; for `fuel ≥ n` it is exact.  The even branch
    recurses on `n/2` (`< n` for `n > 0`).  Mirrors `Josephus.jos0F`'s reducible
    `(n+2)%2` parity split. -/
def stripTwo : Nat → Nat → Nat × Nat
  | 0,     n         => (0, n)
  | _ + 1, 0         => (0, 0)
  | f + 1, (n + 1)   =>
      match (n + 1) % 2 with
      | 0     => let p := stripTwo f ((n + 1) / 2); (p.1 + 1, p.2)
      | _ + 1 => (0, n + 1)

/-- `v2 n` = the 2-adic valuation of `n` (largest `a` with `2^a ∣ n`). -/
def v2 (n : Nat) : Nat := (stripTwo (n + 1) n).1

/-- `oddPart n` = `n / 2^(v2 n)` — the odd part of `n` (`= n` itself for `n` odd). -/
def oddPart (n : Nat) : Nat := (stripTwo (n + 1) n).2

/-! ## §2 — fuel irrelevance (the `Josephus.jos0F_eq` pattern) -/

/-- `n/2 < n` for `n > 0` (here in the form `(n+1)/2 < n+1`): from `n+1 < 2·(n+1)`. -/
theorem half_lt (n : Nat) : (n + 1) / 2 < n + 1 := by
  apply div_lt_of_lt_mul
  -- n+1 < 2 * (n+1)
  rw [Nat.two_mul]
  exact Nat.lt_add_of_pos_left (Nat.succ_pos n)

/-- Fuel irrelevance: `stripTwo` is independent of fuel once `fuel ≥ n`. -/
theorem stripTwo_fuel_eq : ∀ n f g, n ≤ f → n ≤ g → stripTwo f n = stripTwo g n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f g hf hg
    match n, f, g, hf, hg with
    | 0,     f,     g,     _,  _  => cases f <;> cases g <;> rfl
    | n + 1, f + 1, g + 1, hf, hg =>
      have hhalf_lt : (n + 1) / 2 < n + 1 := half_lt n
      have hhf : (n + 1) / 2 ≤ f :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hhalf_lt hf)
      have hhg : (n + 1) / 2 ≤ g :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hhalf_lt hg)
      have hrec : stripTwo f ((n + 1) / 2) = stripTwo g ((n + 1) / 2) :=
        ih ((n + 1) / 2) hhalf_lt f g hhf hhg
      show (match (n + 1) % 2 with
            | 0     => let p := stripTwo f ((n + 1) / 2); (p.1 + 1, p.2)
            | _ + 1 => (0, n + 1))
         = (match (n + 1) % 2 with
            | 0     => let p := stripTwo g ((n + 1) / 2); (p.1 + 1, p.2)
            | _ + 1 => (0, n + 1))
      cases (n + 1) % 2 with
      | zero   => rw [hrec]
      | succ m => rfl

/-- `stripTwo f n = stripTwo (n+1) n` whenever `fuel ≥ n` — normalises any sufficient
    fuel to the canonical `n+1` used by `v2` / `oddPart`. -/
theorem stripTwo_canon (f n : Nat) (h : n ≤ f) : stripTwo f n = stripTwo (n + 1) n :=
  stripTwo_fuel_eq n f (n + 1) h (Nat.le_succ n)

/-! ## §3 — the defining recurrences for `v2` / `oddPart` -/

/-- Odd `n` (`n % 2 = 1`): `stripTwo (f+1) n = (0, n)` for any fuel — no factor of 2. -/
theorem stripTwo_odd {n : Nat} (hodd : n % 2 = 1) (f : Nat) :
    stripTwo (f + 1) n = (0, n) := by
  -- n ≠ 0 since n % 2 = 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    cases n with
    | zero => exact absurd hodd (by decide)
    | succ k => exact ⟨k, rfl⟩
  show (match (m + 1) % 2 with
        | 0     => let p := stripTwo f ((m + 1) / 2); (p.1 + 1, p.2)
        | _ + 1 => (0, m + 1)) = (0, m + 1)
  rw [hodd]

/-- Even positive `n = 2*k` (`k > 0`): the recurrence
    `stripTwo (fuel) (2k) = ((stripTwo' (k)).1 + 1, (stripTwo' (k)).2)`, where the
    inner strip is on `k` with canonical fuel.  Stated at the canonical fuel `2k+1`. -/
theorem stripTwo_two_mul {f k : Nat} (hk : 0 < k) (hfuel : 2 * k ≤ f + 1) :
    stripTwo (f + 1) (2 * k)
      = ((stripTwo (k + 1) k).1 + 1, (stripTwo (k + 1) k).2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  -- The second argument `2*(j+1)` has the `m+1` shape `((2*j+1)+1)`.
  have hn : 2 * (j + 1) = (2 * j + 1) + 1 := by ring_nat
  have heven : ((2 * j + 1) + 1) % 2 = 0 := by rw [← hn]; exact mul_mod_self_pure 2 (j + 1)
  have hhalf : ((2 * j + 1) + 1) / 2 = j + 1 := by
    rw [← hn]; exact mul_div_cancel_left_pure 2 (j + 1) (by decide)
  rw [hn]
  -- now `stripTwo (f+1) ((2*j+1)+1)` unfolds by the `(f+1, n+1)` clause
  show (match ((2 * j + 1) + 1) % 2 with
        | 0     => let p := stripTwo f (((2 * j + 1) + 1) / 2); (p.1 + 1, p.2)
        | _ + 1 => (0, (2 * j + 1) + 1))
      = ((stripTwo (j + 1 + 1) (j + 1)).1 + 1, (stripTwo (j + 1 + 1) (j + 1)).2)
  rw [heven, hhalf]
  -- inner: stripTwo f (j+1) ; normalise fuel to (j+1)+1
  have hfle : j + 1 ≤ f := by
    -- 2*(j+1) ≤ f+1 ⇒ j+1 ≤ f  (since j+1 ≤ 2*(j+1)-1 = 2*j+1 ≤ f)
    have h1 : (2 * j + 1) + 1 ≤ f + 1 := hn ▸ hfuel
    have h2 : 2 * j + 1 ≤ f := Nat.le_of_succ_le_succ h1
    have hj : j ≤ 2 * j := by rw [Nat.two_mul]; exact Nat.le_add_left j j
    exact Nat.le_trans (Nat.succ_le_succ hj) h2
  rw [stripTwo_canon f (j + 1) hfle]

/-! ## §4 — ★★★ the decomposition `n = 2^(v2 n) · oddPart n` and `oddPart` odd -/

/-- Joint statement carried by strong induction (halving): for `0 < n`,
    `n = 2^(v2 n) · oddPart n` AND `oddPart n % 2 = 1`. -/
theorem decomp_and_odd : ∀ n, 0 < n →
    n = 2 ^ v2 n * oddPart n ∧ oddPart n % 2 = 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    rcases mod_two_zero_or_one n with heven | hodd
    · -- n even, n = 2*k with k > 0
      obtain ⟨k, hk2⟩ : ∃ k, n = 2 * k := ⟨n / 2, by
        have hdm : 2 * (n / 2) + n % 2 = n := div_add_mod n 2
        rw [heven, Nat.add_zero] at hdm
        exact hdm.symm⟩
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · rw [hk0, Nat.mul_zero] at hk2; exact absurd (hk2 ▸ hn) (by decide)
        · exact hk0
      have hklt : k < n := by
        rw [hk2]; rw [Nat.two_mul]
        exact Nat.lt_add_of_pos_left hkpos
      obtain ⟨ihdec, ihodd⟩ := ih k hklt hkpos
      -- unfold v2/oddPart of n = 2*k via the recurrence (fuel f = n, n = 2k)
      have hstrip : stripTwo (n + 1) n
          = ((stripTwo (k + 1) k).1 + 1, (stripTwo (k + 1) k).2) := by
        rw [hk2]
        exact stripTwo_two_mul hkpos (f := 2 * k) (Nat.le_succ (2 * k))
      have hv2 : v2 n = v2 k + 1 := by
        show (stripTwo (n + 1) n).1 = (stripTwo (k + 1) k).1 + 1
        rw [hstrip]
      have hop : oddPart n = oddPart k := by
        show (stripTwo (n + 1) n).2 = (stripTwo (k + 1) k).2
        rw [hstrip]
      refine ⟨?_, ?_⟩
      · -- n = 2^(v2 k + 1) * oddPart k = 2 * (2^(v2 k) * oddPart k) = 2*k
        rw [hv2, hop, hk2]
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ v2 k) 2, E213.Tactic.NatHelper.mul_assoc]
        rw [← ihdec]
      · rw [hop]; exact ihodd
    · -- n odd: v2 n = 0, oddPart n = n
      have hn1 : ∃ m, n = m + 1 := by
        cases n with
        | zero => exact absurd hn (by decide)
        | succ k => exact ⟨k, rfl⟩
      obtain ⟨m, rfl⟩ := hn1
      have hstrip : stripTwo (m + 1 + 1) (m + 1) = (0, m + 1) := stripTwo_odd hodd (m + 1)
      have hv2 : v2 (m + 1) = 0 := by
        show (stripTwo (m + 1 + 1) (m + 1)).1 = 0; rw [hstrip]
      have hop : oddPart (m + 1) = m + 1 := by
        show (stripTwo (m + 1 + 1) (m + 1)).2 = m + 1; rw [hstrip]
      refine ⟨?_, ?_⟩
      · rw [hv2, hop]; show m + 1 = 1 * (m + 1); rw [Nat.one_mul]
      · rw [hop]; exact hodd

/-- ★★★ **2-adic odd-part decomposition**: `n = 2^(v2 n) · oddPart n` for `0 < n`. -/
theorem decomp {n : Nat} (hn : 0 < n) : n = 2 ^ v2 n * oddPart n :=
  (decomp_and_odd n hn).1

/-- ★★★ **The odd part is odd**: `oddPart n % 2 = 1` for `0 < n`. -/
theorem oddPart_odd {n : Nat} (hn : 0 < n) : oddPart n % 2 = 1 :=
  (decomp_and_odd n hn).2

/-- ★★★ **The odd part is positive**: from `n = 2^a · oddPart n` and `0 < n`. -/
theorem oddPart_pos {n : Nat} (hn : 0 < n) : 0 < oddPart n := by
  rcases Nat.eq_zero_or_pos (oddPart n) with h0 | hpos
  · exfalso
    have := decomp hn
    rw [h0, Nat.mul_zero] at this
    exact absurd (this ▸ hn) (by decide)
  · exact hpos

/-! ## §5 — coprimality `gcd(2^(v2 n), oddPart n) = 1` -/

/-- `2 ∤ oddPart n` since `oddPart n` is odd (`oddPart n % 2 = 1`). -/
theorem two_not_dvd_oddPart {n : Nat} (hn : 0 < n) : ¬ (2 : Nat) ∣ oddPart n := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have : oddPart n % 2 = 0 := by rw [hc]; exact mul_mod_self_pure 2 c
  rw [oddPart_odd hn] at this
  exact absurd this (by decide)

/-- `gcd(2^(v2 n), oddPart n) = 1` — power-of-2 coprime to the odd part. -/
theorem coprime_two_pow_oddPart {n : Nat} (hn : 0 < n) :
    gcd213 (2 ^ v2 n) (oddPart n) = 1 := by
  have h2 : gcd213 2 (oddPart n) = 1 :=
    prime_coprime_of_not_dvd prime2 (two_not_dvd_oddPart hn)
  exact coprime_pow_left h2 (v2 n)

/-! ## §6 — ★★ the σ 2-part split and ★★★ parity reduction -/

/-- ★★ **σ 2-part split**: `σ(n) = σ(2^(v2 n)) · σ(oddPart n)`.
    `gcd(2^(v2 n), oddPart n) = 1` ⇒ `sigma_mul` (corpus). -/
theorem sigma_decomp {n : Nat} (hn : 0 < n) :
    sigma n = sigma (2 ^ v2 n) * sigma (oddPart n) := by
  have hcop : gcd213 (2 ^ v2 n) (oddPart n) = 1 := coprime_two_pow_oddPart hn
  have hpos : 0 < 2 ^ v2 n := Nat.pos_pow_of_pos (v2 n) (by decide)
  have hopos : 0 < oddPart n := oddPart_pos hn
  have hsm : sigma (2 ^ v2 n * oddPart n) = sigma (2 ^ v2 n) * sigma (oddPart n) :=
    sigma_mul hcop hpos hopos
  -- rewrite the `n` inside `sigma n` via the decomposition
  calc sigma n = sigma (2 ^ v2 n * oddPart n) := by rw [← decomp hn]
    _ = sigma (2 ^ v2 n) * sigma (oddPart n) := hsm

/-- ★★★ **σ-parity reduces to the odd part**:
    `σ(n) % 2 = 1 ↔ σ(oddPart n) % 2 = 1` (for `0 < n`).

    `σ(2^(v2 n))` is ALWAYS odd (`sigma_two_pow_odd`), so it does not affect the
    parity of `σ(n) = σ(2^(v2 n)) · σ(oddPart n)`.  This removes the 2-part entirely
    from the σ-parity problem — a genuine step toward the frontier's general ⟺. -/
theorem sigma_odd_iff_oddPart {n : Nat} (hn : 0 < n) :
    sigma n % 2 = 1 ↔ sigma (oddPart n) % 2 = 1 := by
  have hsplit : sigma n = sigma (2 ^ v2 n) * sigma (oddPart n) := sigma_decomp hn
  have h2odd : sigma (2 ^ v2 n) % 2 = 1 := sigma_two_pow_odd (v2 n)
  -- (a*b) % 2 = (a%2 * b%2) % 2 = (1 * (b%2)) % 2 = (b%2) % 2 = b%2
  rw [hsplit]
  rw [mul_mod_pure, h2odd, Nat.one_mul, mod_mod]

/-! ## §7 — smoke tests (closed numerics, axiom-clean `decide`) -/

/-- `v2` table: `v2 12 = 2` (12 = 2²·3), `v2 40 = 3` (40 = 2³·5), `v2 9 = 0`,
    `v2 8 = 3`, `v2 6 = 1`, `v2 1 = 0`, `v2 24 = 3`. -/
theorem v2_table :
    v2 12 = 2 ∧ v2 40 = 3 ∧ v2 9 = 0 ∧ v2 8 = 3 ∧ v2 6 = 1
    ∧ v2 1 = 0 ∧ v2 24 = 3 ∧ v2 5 = 0 := by decide

/-- `oddPart` table: `oddPart 12 = 3`, `oddPart 40 = 5`, `oddPart 9 = 9`,
    `oddPart 8 = 1`, `oddPart 6 = 3`, `oddPart 1 = 1`, `oddPart 24 = 3`. -/
theorem oddPart_table :
    oddPart 12 = 3 ∧ oddPart 40 = 5 ∧ oddPart 9 = 9 ∧ oddPart 8 = 1
    ∧ oddPart 6 = 3 ∧ oddPart 1 = 1 ∧ oddPart 24 = 3 ∧ oddPart 5 = 5 := by decide

/-- Decomposition smoke (closed): `n = 2^(v2 n) * oddPart n` for `n = 12, 40, 24`. -/
theorem decomp_smoke :
    12 = 2 ^ v2 12 * oddPart 12 ∧ 40 = 2 ^ v2 40 * oddPart 40
    ∧ 24 = 2 ^ v2 24 * oddPart 24 := by decide

set_option maxRecDepth 4000 in
/-- σ-decomp smoke (closed): `σ(n) = σ(2^(v2 n)) · σ(oddPart n)` for `n = 12, 40`. -/
theorem sigma_decomp_smoke :
    sigma 12 = sigma (2 ^ v2 12) * sigma (oddPart 12)
    ∧ sigma 40 = sigma (2 ^ v2 40) * sigma (oddPart 40) := by decide

end E213.Lib.Math.NumberTheory.OddPartDecomposition
