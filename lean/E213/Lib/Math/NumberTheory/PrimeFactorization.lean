import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Meta.Nat.VpSeparation
import E213.Meta.Nat.NatDiv213

/-!
# Fundamental Theorem of Arithmetic — existence (∅-axiom, constructive)

**Every `n > 1` is a product of primes** — with the *recursive factorization*
as the explicit witness.

## The forcing (vein-B)

Classically "every `n > 1` factors into primes" is a **least-counterexample**
existence proof (well-ordering + LEM: a *minimal* non-factorable `n` is
composite, `n = a·b` with both smaller, both factor by minimality →
contradiction).  With no LEM / well-ordering available as a proof device, the
existence becomes the **factorization algorithm** `factorize`: recursively pull
out the smallest prime factor and recurse on the quotient.  `factorize_prod`
certifies it.  **The FTA-existence IS the factorization algorithm — the witness
is *computed*, not *extracted from a minimal counterexample*.**
-/

namespace E213.Lib.Math.NumberTheory.PrimeFactorization

open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Meta.Nat.Valuation (mod_zero_of_dvd)
open E213.Meta.Nat.NatRing213 (nat_mul_lt_mul_right nat_mul_assoc)

/-! ## §0 — local list product (PURE; avoid core `List.prod` axiom risk) -/

/-- Product of a `Nat` list (`prodL [] = 1`, `prodL (p::L) = p * prodL L`). -/
def prodL : List Nat → Nat
  | []        => 1
  | p :: rest => p * prodL rest

theorem prodL_cons (p : Nat) (L : List Nat) : prodL (p :: L) = p * prodL L := rfl

/-! ## §1 — `n ∣ n` is found in range; the `≤`/dvd helpers -/

/-- `a ∣ b`, `0 < b` ⟹ `a ≤ b`.  (Local, ∅-axiom.) -/
theorem le_of_dvd_pos {a b : Nat} (hb : 0 < b) (h : a ∣ b) : a ≤ b := by
  obtain ⟨c, hc⟩ := h
  rcases Nat.eq_zero_or_pos c with hc0 | hcp
  · exfalso; rw [hc0, Nat.mul_zero] at hc; rw [hc] at hb; exact Nat.lt_irrefl 0 hb
  · calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * c := Nat.mul_le_mul_left a hcp
      _ = b := hc.symm

/-! ## §2 — smallest factor `≥ k` of `n` (computable, fuel-bounded)

`leastFactorFrom fuel k n` searches upward from `k` for the smallest `d ≥ k`
dividing `n`.  Divisibility tested by the reducible `n % k` match. -/

/-- Smallest `d ≥ k` dividing `n`, fuel-bounded.  Falls back to `n` if fuel runs
    out (never the operative case: callers supply ample fuel, and `n ∣ n`). -/
def leastFactorFrom : Nat → Nat → Nat → Nat
  | 0,     _, n => n
  | f + 1, k, n =>
    match n % k with
    | 0     => k
    | _ + 1 => leastFactorFrom f (k + 1) n

/-- `minFac n` = the smallest factor `≥ 2` of `n` (fuel = `n`, ample). -/
def minFac (n : Nat) : Nat := leastFactorFrom n 2 n

/-- **Spec of the search**, carrying the invariant "no `d` with `2 ≤ d < k`
    divides `n`".  Returns: result divides `n`, is `≥ k`, `≤ n`, and is minimal
    among factors `≥ 2` (any `2 ≤ e < result` does not divide `n`).  Fuel must
    span `[k, n]`: `n ≤ k + fuel`. -/
theorem leastFactorFrom_spec :
    ∀ (fuel k n : Nat), 2 ≤ n → 2 ≤ k → n ≤ k + fuel →
      (∀ d, 2 ≤ d → d < k → ¬ d ∣ n) →
      (2 ≤ leastFactorFrom fuel k n
        ∧ leastFactorFrom fuel k n ∣ n
        ∧ leastFactorFrom fuel k n ≤ n
        ∧ ∀ e, 2 ≤ e → e < leastFactorFrom fuel k n → ¬ e ∣ n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k n hn hk hfuel hbelow
    -- fuel = 0 ⇒ result = n; with no factor < k, n itself is least factor ≥ 2.
    show (2 ≤ n ∧ n ∣ n ∧ n ≤ n ∧ ∀ e, 2 ≤ e → e < n → ¬ e ∣ n)
    have hkn : n ≤ k := by rw [Nat.add_zero] at hfuel; exact hfuel
    have hpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
    refine ⟨hn, ⟨1, (Nat.mul_one n).symm⟩, Nat.le_refl n, ?_⟩
    intro e he2 helt
    exact hbelow e he2 (Nat.lt_of_lt_of_le helt hkn)
  | succ f ih =>
    intro k n hn hk hfuel hbelow
    have hpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
    show (2 ≤ (match n % k with | 0 => k | _ + 1 => leastFactorFrom f (k + 1) n)
        ∧ (match n % k with | 0 => k | _ + 1 => leastFactorFrom f (k + 1) n) ∣ n
        ∧ (match n % k with | 0 => k | _ + 1 => leastFactorFrom f (k + 1) n) ≤ n
        ∧ ∀ e, 2 ≤ e → e < (match n % k with | 0 => k | _ + 1 => leastFactorFrom f (k + 1) n) → ¬ e ∣ n)
    rcases Nat.eq_zero_or_pos (n % k) with hmod | hmod
    · -- k ∣ n: result = k
      have hdvd : k ∣ n := dvd_of_mod_eq_zero hmod
      have hbr : (match n % k with | 0 => k | _ + 1 => leastFactorFrom f (k + 1) n) = k := by
        rw [hmod]
      rw [hbr]
      refine ⟨hk, hdvd, le_of_dvd_pos hpos hdvd, ?_⟩
      intro e he2 helt
      exact hbelow e he2 helt
    · -- k ∤ n: recurse at k+1
      have hmodne : n % k ≠ 0 := fun h => Nat.lt_irrefl 0 (h ▸ hmod)
      have hkndvd : ¬ k ∣ n := fun hd =>
        hmodne (mod_zero_of_dvd (Nat.lt_of_lt_of_le (by decide) hk) hd)
      have hbr : (match n % k with | 0 => k | _ + 1 => leastFactorFrom f (k + 1) n)
                  = leastFactorFrom f (k + 1) n := by
        cases hh : n % k with
        | zero => exact absurd hh hmodne
        | succ m => rfl
      rw [hbr]
      have hfuel' : n ≤ (k + 1) + f := by
        have : k + (f + 1) = (k + 1) + f := by
          rw [Nat.add_succ, Nat.succ_add]
        rw [this] at hfuel; exact hfuel
      have hk1 : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
      have hbelow' : ∀ d, 2 ≤ d → d < k + 1 → ¬ d ∣ n := by
        intro d hd2 hdlt
        rcases Nat.lt_or_ge d k with hdk | hdk
        · exact hbelow d hd2 hdk
        · have : d = k := Nat.le_antisymm (Nat.le_of_lt_succ hdlt) hdk
          rw [this]; exact hkndvd
      obtain ⟨hge, hdvd, hle, hmin⟩ := ih (k + 1) n hn hk1 hfuel' hbelow'
      exact ⟨hge, hdvd, hle, hmin⟩

/-! ## §3 — `minFac` is a prime divisor

`minFac n` (`= leastFactorFrom n 2 n`) is `≥ 2`, divides `n`, and is **minimal**
among factors `≥ 2`.  A minimal factor `≥ 2` is **prime**: if `minFac = a·b` with
`1 < a < minFac` then `a` is a smaller factor `≥ 2` of `n` (transitivity),
contradicting minimality. -/

/-- `minFac n` spec for `n ≥ 2`. -/
theorem minFac_spec {n : Nat} (hn : 2 ≤ n) :
    2 ≤ minFac n ∧ minFac n ∣ n ∧ minFac n ≤ n
      ∧ ∀ e, 2 ≤ e → e < minFac n → ¬ e ∣ n := by
  have hfuel : n ≤ 2 + n := Nat.le_trans (Nat.le_add_left n 2) (Nat.le_refl _)
  exact leastFactorFrom_spec n 2 n hn (Nat.le_refl 2) hfuel
    (fun d hd2 hlt => absurd hlt (Nat.not_lt_of_le hd2))

/-- The minimal factor `≥ 2` of `n` is **prime**. -/
theorem minFac_prime {n : Nat} (hn : 2 ≤ n) : Prime213 (minFac n) := by
  obtain ⟨hge, hdvd, _hle, hmin⟩ := minFac_spec hn
  refine ⟨hge, ?_⟩
  intro d hdm
  -- d ∣ minFac n.  Show d = 1 ∨ d = minFac n.
  have hmpos : 0 < minFac n := Nat.lt_of_lt_of_le (by decide) hge
  obtain ⟨c, hc⟩ := hdm           -- minFac n = d * c
  -- d ≤ minFac n
  have hdle : d ≤ minFac n := le_of_dvd_pos hmpos ⟨c, hc⟩
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · -- d < 2: d = 0 or d = 1
    rcases Nat.lt_or_ge d 1 with hd0 | hd1
    · -- d = 0 ⇒ minFac n = 0, contra
      exfalso
      have : d = 0 := Nat.le_antisymm (Nat.le_of_lt_succ hd0) (Nat.zero_le d)
      rw [this, Nat.zero_mul] at hc
      exact Nat.lt_irrefl 0 (hc ▸ hmpos)
    · -- d = 1
      exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hd2) hd1)
  · -- d ≥ 2: then d ∣ n (d ∣ minFac ∣ n) and minimality forces d = minFac n
    obtain ⟨q, hq⟩ := hdvd          -- n = minFac n * q
    have hdn : d ∣ n := ⟨c * q, by
      calc n = minFac n * q := hq
        _ = (d * c) * q := by rw [hc]
        _ = d * (c * q) := nat_mul_assoc d c q⟩
    rcases Nat.lt_or_ge d (minFac n) with hdlt | hdge
    · exact absurd hdn (hmin d hd2 hdlt)
    · exact Or.inr (Nat.le_antisymm hdle hdge)

/-- `minFac n * (n / minFac n) = n` and `n / minFac n < n` for `n ≥ 2`. -/
theorem minFac_div {n : Nat} (hn : 2 ≤ n) :
    minFac n * (n / minFac n) = n ∧ n / minFac n < n := by
  obtain ⟨hge, hdvd, _hle, _hmin⟩ := minFac_spec hn
  -- generalize `minFac n` to `p` so rewrites on `n` don't touch the divisor
  have key : ∀ p, 2 ≤ p → p ∣ n → p * (n / p) = n ∧ n / p < n := by
    intro p hp hpd
    have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp
    obtain ⟨c, hc⟩ := hpd            -- n = p * c
    have hdivc : n / p = c := by rw [hc]; exact mul_div_cancel_left_pure p c hppos
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with hc0 | hcp
      · exfalso; rw [hc0, Nat.mul_zero] at hc; rw [hc] at hn; exact absurd hn (by decide)
      · exact hcp
    refine ⟨?_, ?_⟩
    · rw [hdivc]; exact hc.symm
    · rw [hdivc, hc]
      have h2p : 1 < p := Nat.lt_of_lt_of_le (by decide) hp
      have hlt : 1 * c < p * c := nat_mul_lt_mul_right hcpos h2p
      rwa [Nat.one_mul] at hlt
  exact key (minFac n) hge hdvd

/-! ## §4 — the factorization algorithm (computable, fuel-bounded) -/

/-- `factorizeF fuel n`: if `n ≥ 2`, prepend `minFac n` and recurse on `n / minFac n`;
    else `[]`.  `factorize n := factorizeF n n`. -/
def factorizeF : Nat → Nat → List Nat
  | 0,     _ => []
  | f + 1, n =>
    if h : 2 ≤ n then
      minFac n :: factorizeF f (n / minFac n)
    else
      []

/-- User-facing factorization: `factorize n := factorizeF n n`. -/
def factorize (n : Nat) : List Nat := factorizeF n n

/-! ## §5 — the witness theorems

By strong induction on `n` (the quotient `n / minFac n < n` is the decreasing
measure), with ample fuel `n ≤ f` so the `dite` unfolds. -/

/-- ★★★ **The product of the factorization is `n`** (`factorizeF` form, any fuel
    `≥ n` and `0 < n`).  `prodL (factorizeF f n) = n`. -/
theorem factorizeF_prod : ∀ (n f : Nat), 0 < n → n ≤ f → prodL (factorizeF f n) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f hn hnf
    match f, hnf with
    | 0, hnf =>
      -- n ≤ 0 with 0 < n: impossible
      exact absurd (Nat.le_antisymm hnf (Nat.zero_le n) ▸ hn) (by decide)
    | f + 1, hnf =>
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · -- n = 1 (n ≥ 1): factorizeF (f+1) 1 = [] (2 ≤ 1 false), prodL [] = 1 = n
        have hn1 : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hn
        show prodL (if h : 2 ≤ n then minFac n :: factorizeF f (n / minFac n) else []) = n
        rw [dif_neg (by rw [hn1]; decide), hn1]; rfl
      · -- n ≥ 2: prodL (minFac n :: factorizeF f (n / minFac n)) = minFac n * prodL (...)
        obtain ⟨hprod, hqlt⟩ := minFac_div hge
        have hqpos : 0 < n / minFac n := by
          rcases Nat.eq_zero_or_pos (n / minFac n) with h0 | hp
          · exfalso; rw [h0, Nat.mul_zero] at hprod
            rw [← hprod] at hge; exact absurd hge (by decide)
          · exact hp
        have hqf : n / minFac n ≤ f :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hqlt hnf)
        have hrec : prodL (factorizeF f (n / minFac n)) = n / minFac n :=
          ih (n / minFac n) hqlt f hqpos hqf
        show prodL (if h : 2 ≤ n then minFac n :: factorizeF f (n / minFac n) else []) = n
        rw [dif_pos hge, prodL_cons, hrec, hprod]

/-- ★★★ **The product of `factorize n` is `n`** (the witness). -/
theorem factorize_prod (n : Nat) (hn : 0 < n) : prodL (factorize n) = n :=
  factorizeF_prod n n hn (Nat.le_refl n)

/-- ★★★ **Every entry of the factorization is prime** (`factorizeF` form). -/
theorem factorizeF_all_prime : ∀ (n f : Nat), n ≤ f →
    ∀ p, p ∈ factorizeF f n → Prime213 p := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f hnf
    match f, hnf with
    | 0, hnf =>
      -- n ≤ 0 ⇒ n = 0 ⇒ factorizeF 0 0 = []
      intro p hp
      have hn0 : n = 0 := Nat.le_antisymm hnf (Nat.zero_le n)
      rw [hn0] at hp
      exact absurd hp (List.not_mem_nil p)
    | f + 1, hnf =>
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · -- factorizeF (f+1) n = [] : no members
        intro p hp
        have : factorizeF (f + 1) n = [] := by
          show (if h : 2 ≤ n then minFac n :: factorizeF f (n / minFac n) else []) = []
          exact dif_neg (Nat.not_le_of_lt hlt)
        rw [this] at hp
        exact absurd hp (List.not_mem_nil p)
      · intro p hp
        have hmem : p ∈ minFac n :: factorizeF f (n / minFac n) := by
          have heq : factorizeF (f + 1) n = minFac n :: factorizeF f (n / minFac n) := by
            show (if h : 2 ≤ n then minFac n :: factorizeF f (n / minFac n) else []) = _
            exact dif_pos hge
          rw [heq] at hp; exact hp
        cases hmem with
        | head _ =>
          -- p = minFac n : prime
          exact minFac_prime hge
        | tail _ htail =>
          -- p ∈ tail : recurse on n / minFac n
          obtain ⟨_hprod, hqlt⟩ := minFac_div hge
          have hqf : n / minFac n ≤ f :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hqlt hnf)
          exact ih (n / minFac n) hqlt f hqf p htail

/-- ★★★ **Every entry of `factorize n` is prime** (for `n ≥ 2`). -/
theorem factorize_all_prime (n : Nat) (hn : 1 < n) :
    ∀ p, p ∈ factorize n → Prime213 p :=
  factorizeF_all_prime n n (Nat.le_refl n)

/-! ## §6 — packaged FTA-existence -/

/-- ★★ **`n` is a product of primes** (`n ≥ 2`): the witness is `factorize n`. -/
theorem exists_prime_factorization (n : Nat) (hn : 1 < n) :
    ∃ L, (∀ p, p ∈ L → Prime213 p) ∧ prodL L = n :=
  ⟨factorize n, factorize_all_prime n hn,
    factorize_prod n (Nat.lt_of_lt_of_le (by decide) hn)⟩

/-! ## §7 — concrete smokes -/

example : factorize 12 = [2, 2, 3] := by decide
example : factorize 30 = [2, 3, 5] := by decide
example : factorize 17 = [17] := by decide
example : factorize 1 = [] := by decide
example : prodL (factorize 12) = 12 := by decide
example : (∀ p, p ∈ factorize 12 → 2 ≤ p) := by decide

end E213.Lib.Math.NumberTheory.PrimeFactorization
