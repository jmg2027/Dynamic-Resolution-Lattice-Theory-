import E213.Lib.Math.NumberTheory.PisanoPeriod

/-!
# Minimal Pisano period is well-defined (∅-axiom)

The Pisano period property is a DECIDABLE 2-residue check: `p` is a period iff the
seed state `(fib 0, fib 1) = (0,1)` returns at `p`, i.e. `fib p % m = 0` and
`fib (p+1) % m = 1 % m`.  Equivalently the whole sequence is `p`-periodic
(`isPeriod_iff_forall`).  Decidability + the pigeonhole period bound make the
**least** period well-defined by a fuel-bounded scan (`exists_minimal_period`).
-/

namespace E213.Lib.Math.NumberTheory.PisanoPeriodMinimal

open E213.Lib.Math.NumberTheory.PisanoPeriod
open E213.Tactic.NatHelper (add_sub_of_le)

/-- `p` is a period for `fib mod m`: the seed state `(0,1)` returns at `p`. -/
def isPeriod (m p : Nat) : Prop := fib p % m = 0 ∧ fib (p + 1) % m = 1 % m

/-- `isPeriod` is decidable (two residue equalities). -/
instance (m p : Nat) : Decidable (isPeriod m p) := by
  unfold isPeriod
  exact inferInstanceAs (Decidable (_ ∧ _))

/-! ## §1 — the period property is the seed-return check -/

/-- **`isPeriod m p ↔ ∀ n, fib (n+p) % m = fib n % m`** for `0 < m`.
    Forward: the `(0,1)` seed returns at `p` ⟹ the whole sequence is `p`-periodic
    (forward propagation from the anchor `a = 0`).  Backward: instantiate at
    `n = 0` (`fib 0 = 0`) and `n = 1` (`fib 1 = 1`). -/
theorem isPeriod_iff_forall {m : Nat} (hm : 0 < m) (p : Nat) :
    isPeriod m p ↔ ∀ n, fib (n + p) % m = fib n % m := by
  constructor
  · -- forward: seed returns ⟹ p-periodic
    intro ⟨h0, h1⟩
    -- anchor hypotheses at a = 0
    have ha : fib (0 + p) % m = fib 0 % m := by
      have e : (0 : Nat) + p = p := Nat.zero_add p
      rw [e]
      -- fib p % m = 0 = fib 0 % m   (fib 0 = 0)
      show fib p % m = fib 0 % m
      rw [h0]; rfl
    have ha1 : fib (0 + 1 + p) % m = fib (0 + 1) % m := by
      -- 0+1 = 1 ; fib 1 = 1 ; goal fib (1+p) % m = 1 % m
      have e : (0 : Nat) + 1 = 1 := rfl
      rw [e]
      show fib (1 + p) % m = fib 1 % m
      -- fib 1 = 1, so fib 1 % m = 1 % m
      have e2 : (1 : Nat) + p = p + 1 := Nat.add_comm 1 p
      rw [e2]
      -- goal: fib (p+1) % m = fib 1 % m ; fib 1 = 1
      show fib (p + 1) % m = fib 1 % m
      rw [h1]; rfl
    intro n
    -- forward extension from anchor 0 covers all n (= 0 + n)
    have hgen := extend_forward (m := m) (p := p)
      (fun b h h' => step_shift b h h') 0 ha ha1 n
    have e : (0 : Nat) + n = n := Nat.zero_add n
    rw [e] at hgen
    exact hgen
  · -- backward: instantiate ∀ at 0 and 1
    intro h
    constructor
    · -- fib p % m = 0
      have h0 := h 0
      have e : (0 : Nat) + p = p := Nat.zero_add p
      rw [e] at h0
      -- h0 : fib p % m = fib 0 % m ; fib 0 = 0
      have : fib 0 % m = 0 := rfl
      rw [this] at h0
      exact h0
    · -- fib (p+1) % m = 1 % m
      have h1 := h 1
      -- h1 : fib (1 + p) % m = fib 1 % m
      have e : (1 : Nat) + p = p + 1 := Nat.add_comm 1 p
      rw [e] at h1
      have : fib 1 % m = 1 % m := rfl
      rw [this] at h1
      exact h1

/-! ## §2 — a period exists (from `pisano_period`) -/

/-- **A positive period exists.**  Immediate from `pisano_period` + the backward
    direction of `isPeriod_iff_forall`. -/
theorem period_returns {m : Nat} (hm : 0 < m) : ∃ p, 0 < p ∧ isPeriod m p := by
  obtain ⟨p, hp, hper⟩ := pisano_period hm
  exact ⟨p, hp, (isPeriod_iff_forall hm p).mpr hper⟩

/-! ## §3 — the LEAST period (fuel-bounded scan)

Adapts the corpus's `leastFactorFrom` idiom (`PrimeFactorization`).  A Bool test
`isPeriodB` makes the search `match` reduce; the scan returns the smallest
`p ≥ k` with the test true, carrying the invariant "no `1 ≤ q < k` is a period".
-/

/-- Bool form of the period test (clean `match` for the scan).  Uses `Nat.beq`
    and `Bool.and` directly so the iff stays syntactic. -/
def isPeriodB (m p : Nat) : Bool :=
  Bool.and (Nat.beq (fib p % m) 0) (Nat.beq (fib (p + 1) % m) (1 % m))

/-- Pure `&&`-split: `Bool.and a b = true → a = true ∧ b = true` (case analysis,
    no `propext`). -/
theorem and_true_split {a b : Bool} (h : Bool.and a b = true) : a = true ∧ b = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true =>
    cases b with
    | false => exact Bool.noConfusion h
    | true => exact ⟨rfl, rfl⟩

/-- Pure `&&`-combine. -/
theorem and_true_intro {a b : Bool} (ha : a = true) (hb : b = true) : Bool.and a b = true := by
  rw [ha, hb]; rfl

/-- Pure `Nat.beq` reflexivity (induction; `Nat.beq_refl` carries `propext`). -/
theorem beq_refl_pure : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_refl_pure n

/-- `isPeriodB m p = true ↔ isPeriod m p`. -/
theorem isPeriodB_iff (m p : Nat) : isPeriodB m p = true ↔ isPeriod m p := by
  unfold isPeriodB isPeriod
  constructor
  · intro h
    have hb := and_true_split h
    exact ⟨Nat.eq_of_beq_eq_true hb.1, Nat.eq_of_beq_eq_true hb.2⟩
  · intro ⟨h0, h1⟩
    apply and_true_intro
    · rw [h0]; exact beq_refl_pure 0
    · rw [h1]; exact beq_refl_pure (1 % m)

/-- Smallest `p ≥ k` with `isPeriodB m p`, fuel-bounded.  Falls back to `k` if
    fuel runs out (never the operative case: callers supply ample fuel and a
    known period in range). -/
def leastPeriodFrom : Nat → Nat → Nat → Nat
  | 0,     k, _ => k
  | f + 1, k, m =>
    match isPeriodB m k with
    | true  => k
    | false => leastPeriodFrom f (k + 1) m

/-- **Spec of the scan.**  Given a known period `P` with `k ≤ P ≤ k + fuel` and
    the invariant "no `1 ≤ q < k` is a period", the result is a period `≥ k` that
    is minimal among positive periods.  (`P` guarantees the search succeeds
    within fuel, so the fallback branch is never the minimal-claim case.) -/
theorem leastPeriodFrom_spec {m : Nat} (hm : 0 < m) :
    ∀ (fuel k P : Nat), 0 < k → isPeriod m P → k ≤ P → P ≤ k + fuel →
      (∀ q, 0 < q → q < k → ¬ isPeriod m q) →
      (0 < leastPeriodFrom fuel k m
        ∧ isPeriod m (leastPeriodFrom fuel k m)
        ∧ ∀ q, 0 < q → isPeriod m q → leastPeriodFrom fuel k m ≤ q) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k P hk hP hkP hfuel hbelow
    -- fuel = 0 ⇒ result = k.  P ≤ k (from hfuel) and k ≤ P ⟹ P = k, so k is a period.
    show (0 < k ∧ isPeriod m k ∧ ∀ q, 0 < q → isPeriod m q → k ≤ q)
    have hPk : P ≤ k := by rw [Nat.add_zero] at hfuel; exact hfuel
    have heq : k = P := Nat.le_antisymm hkP hPk
    have hperk : isPeriod m k := by rw [heq]; exact hP
    refine ⟨hk, hperk, ?_⟩
    intro q hq hperq
    -- minimality: any positive period q has k ≤ q (else q < k, contra hbelow)
    rcases Nat.lt_or_ge q k with hqk | hqk
    · exact absurd hperq (hbelow q hq hqk)
    · exact hqk
  | succ f ih =>
    intro k P hk hP hkP hfuel hbelow
    show (0 < (match isPeriodB m k with | true => k | false => leastPeriodFrom f (k + 1) m)
        ∧ isPeriod m (match isPeriodB m k with | true => k | false => leastPeriodFrom f (k + 1) m)
        ∧ ∀ q, 0 < q → isPeriod m q →
            (match isPeriodB m k with | true => k | false => leastPeriodFrom f (k + 1) m) ≤ q)
    have hcases : isPeriodB m k = true ∨ isPeriodB m k = false := by
      cases isPeriodB m k with
      | true => exact Or.inl rfl
      | false => exact Or.inr rfl
    rcases hcases with htest | htest
    · -- k is a period: result = k
      have hbr : (match isPeriodB m k with | true => k | false => leastPeriodFrom f (k + 1) m)
                  = k := by rw [htest]
      rw [hbr]
      have hperk : isPeriod m k := (isPeriodB_iff m k).mp htest
      refine ⟨hk, hperk, ?_⟩
      intro q hq hperq
      rcases Nat.lt_or_ge q k with hqk | hqk
      · exact absurd hperq (hbelow q hq hqk)
      · exact hqk
    · -- k is not a period: recurse at k+1
      have hbr : (match isPeriodB m k with | true => k | false => leastPeriodFrom f (k + 1) m)
                  = leastPeriodFrom f (k + 1) m := by rw [htest]
      rw [hbr]
      have hknotper : ¬ isPeriod m k := by
        intro hper
        have : isPeriodB m k = true := (isPeriodB_iff m k).mpr hper
        rw [htest] at this; exact Bool.noConfusion this
      -- P ≠ k (k not a period, P is) ⟹ k < P ⟹ k+1 ≤ P
      have hkltP : k < P := by
        rcases Nat.lt_or_ge k P with h | h
        · exact h
        · exact absurd (Nat.le_antisymm hkP h ▸ hP) hknotper
      have hk1P : k + 1 ≤ P := Nat.succ_le_of_lt hkltP
      have hfuel' : P ≤ (k + 1) + f := by
        have e : k + (f + 1) = (k + 1) + f := by rw [Nat.add_succ, Nat.succ_add]
        rw [e] at hfuel; exact hfuel
      have hk1 : 0 < k + 1 := Nat.succ_pos k
      have hbelow' : ∀ q, 0 < q → q < k + 1 → ¬ isPeriod m q := by
        intro q hq hqlt
        rcases Nat.lt_or_ge q k with hqk | hqk
        · exact hbelow q hq hqk
        · have : q = k := Nat.le_antisymm (Nat.le_of_lt_succ hqlt) hqk
          rw [this]; exact hknotper
      exact ih (k + 1) P hk1 hP hk1P hfuel' hbelow'

/-- **★ The minimal Pisano period is well-defined.**  There is a least positive
    period: a `p > 0` with `isPeriod m p` such that every positive period `q`
    satisfies `p ≤ q`.  Existence of *some* period (`period_returns`) bounds the
    fuel; `isPeriod` decidable ⟹ minimize by the bounded scan. -/
theorem exists_minimal_period {m : Nat} (hm : 0 < m) :
    ∃ p, 0 < p ∧ isPeriod m p ∧ ∀ q, 0 < q → isPeriod m q → p ≤ q := by
  obtain ⟨P, hP, hperP⟩ := period_returns hm
  -- scan from k = 1 with fuel = P (1 ≤ P ≤ 1 + P), no positive period below 1.
  have hk : 0 < 1 := Nat.one_pos
  have h1P : 1 ≤ P := hP
  have hfuel : P ≤ 1 + P := Nat.le_add_left P 1
  have hbelow : ∀ q, 0 < q → q < 1 → ¬ isPeriod m q := by
    intro q hq hq1
    exact absurd hq1 (Nat.not_lt_of_le hq)
  obtain ⟨hpos, hper, hmin⟩ := leastPeriodFrom_spec hm P 1 P hk hperP h1P hfuel hbelow
  exact ⟨leastPeriodFrom P 1 m, hpos, hper, hmin⟩

/-! ## §4 — every period is a multiple of the minimal period (★ stretch) -/

/-- A period `p` may be applied any number of times: `fib (n + k·p) % m = fib n % m`.
    Induction on `k` from the single-shift periodicity (`isPeriod_iff_forall`). -/
theorem period_iter {m : Nat} (hm : 0 < m) {p : Nat} (hper : isPeriod m p) :
    ∀ k n, fib (n + k * p) % m = fib n % m := by
  have hshift := (isPeriod_iff_forall hm p).mp hper
  intro k
  induction k with
  | zero =>
    intro n
    have e : n + 0 * p = n := by rw [Nat.zero_mul, Nat.add_zero]
    rw [e]
  | succ k ih =>
    intro n
    -- n + (k+1)·p = (n + k·p) + p
    have e : n + (k + 1) * p = (n + k * p) + p := by
      rw [Nat.succ_mul, ← Nat.add_assoc]
    rw [e]
    -- fib ((n + k·p) + p) % m = fib (n + k·p) % m = fib n % m
    rw [hshift (n + k * p)]
    exact ih n

/-- **Periods are closed under `%`**: if `p` and `q` are periods with `0 < p`,
    then `q % p` is a period.  `q = p·(q/p) + q%p`, and the `p`-shift applied
    `q/p` times is identity, so `fib (n+q)%m = fib (n + q%p)%m`; combined with
    `q` periodic gives `q%p` periodic. -/
theorem isPeriod_mod {m : Nat} (hm : 0 < m) {p q : Nat}
    (hp : isPeriod m p) (hq : isPeriod m q) (hppos : 0 < p) : isPeriod m (q % p) := by
  apply (isPeriod_iff_forall hm (q % p)).mpr
  have hqshift := (isPeriod_iff_forall hm q).mp hq
  intro n
  -- q = p·(q/p) + q%p
  have hdm : p * (q / p) + q % p = q := E213.Meta.Nat.AddMod213.div_add_mod q p
  -- fib (n + q%p + p·(q/p)) % m = fib (n + q%p) % m   (apply period p, q/p times)
  have hiter := period_iter hm hp (q / p) (n + q % p)
  -- rearrange n + q%p + (q/p)·p = n + q   (note period_iter uses k·p = (q/p)·p)
  have erearr : n + q % p + (q / p) * p = n + q := by
    have ecomm : (q / p) * p = p * (q / p) := Nat.mul_comm (q / p) p
    rw [ecomm, Nat.add_assoc, Nat.add_comm (q % p) (p * (q / p)), hdm]
  rw [erearr] at hiter
  -- hiter : fib (n + q) % m = fib (n + q%p) % m
  -- hqshift n : fib (n + q) % m = fib n % m
  -- ⟹ fib (n + q%p) % m = fib n % m
  rw [← hiter]; exact hqshift n

/-- **★ Every period is a multiple of the minimal period.**  If `p` is the least
    positive period and `q` any positive period, then `p ∣ q`.  Otherwise `q % p`
    is a positive period strictly below `p` (`isPeriod_mod` + `Nat.mod_lt`),
    contradicting minimality of `p`. -/
theorem period_dvd_of_minimal {m : Nat} (hm : 0 < m) {p q : Nat}
    (hppos : 0 < p) (hpper : isPeriod m p)
    (hmin : ∀ r, 0 < r → isPeriod m r → p ≤ r)
    (hqper : isPeriod m q) : p ∣ q := by
  -- q % p is a period; if it were positive it would be < p, contradicting minimality.
  have hmodper : isPeriod m (q % p) := isPeriod_mod hm hpper hqper hppos
  have hmodlt : q % p < p := Nat.mod_lt q hppos
  -- q % p = 0
  have hmod0 : q % p = 0 := by
    rcases Nat.eq_zero_or_pos (q % p) with h0 | hpos
    · exact h0
    · exact absurd (hmin (q % p) hpos hmodper) (Nat.not_le_of_lt hmodlt)
  exact E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero hmod0

/-! ## §5 — smoke tests (closed numerals) -/

-- π(2) = 3 : isPeriod 2 3 holds, and 1,2 are not periods.
example : isPeriod 2 3 := by decide
example : ¬ isPeriod 2 1 := by decide
example : ¬ isPeriod 2 2 := by decide

-- π(3) = 8.
example : isPeriod 3 8 := by decide
example : ∀ q, q < 8 → 0 < q → ¬ isPeriod 3 q := by decide

-- π(5) = 20.
example : isPeriod 5 20 := by decide
example : ∀ q, q < 20 → 0 < q → ¬ isPeriod 5 q := by decide

end E213.Lib.Math.NumberTheory.PisanoPeriodMinimal
