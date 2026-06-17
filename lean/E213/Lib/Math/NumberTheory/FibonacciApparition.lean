import E213.Lib.Math.NumberTheory.PisanoPeriodMinimal
import E213.Lib.Math.Combinatorics.FibonacciGcd
import E213.Meta.Tactic.Pow213
import E213.Meta.Nat.Valuation

/-!
# The Fibonacci rank of apparition α(m) (∅-axiom)

For `m ≥ 1` the **rank of apparition** α(m) is the least `k > 0` with `m ∣ fib k`.
Built on:
  * `PisanoPeriodMinimal.period_returns` — a positive Pisano period exists, giving
    a positive zero (`fib p % m = 0`);
  * the `leastPeriodFrom` bounded-least-witness idiom, re-instantiated here as
    `leastApparitionFrom`;
  * `FibonacciDivisibility.fib_dvd_fib_mul` (`fib m ∣ fib (m*n)`) for direction A;
  * `FibonacciGcd.fib_gcd` (`gcd(Fₐ,F_b) = F_gcd(a,b)`) for direction B (the prize).

Two module-local `fib`s exist (`PisanoPeriod.fib`, `FibonacciDivisibility.fib`);
they are the same two-step recurrence.  We standardize on `FibonacciDivisibility.fib`
(items 3,4 need it) and bridge the Pisano result via `fibP_eq_fib`.
-/

namespace E213.Lib.Math.NumberTheory.FibonacciApparition

open E213.Lib.Math.Combinatorics.FibonacciDivisibility (fib fib_rec fib_dvd_fib_mul)
open E213.Lib.Math.Combinatorics.FibonacciGcd (fib_gcd)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Meta.Nat.Valuation (mod_zero_of_dvd)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right gcd213_greatest)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (dvd_trans_213)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Lib.Math.Combinatorics.Pigeonhole (exists_collision_lt)
open E213.Meta.Nat.EncodePair213 (encode_div encode_mod)
open E213.Tactic.NatHelper (add_sub_of_le sub_pos_of_lt)
open E213.Lib.Math.NumberTheory.PisanoPeriod
  (stateVal stateVal_lt extend_forward extend_back step_shift)

/-! ## Bridge: the two `fib` definitions agree -/

/-- `PisanoPeriod.fib = FibonacciDivisibility.fib` (same two-step recurrence). -/
theorem fibP_eq_fib :
    ∀ n, E213.Lib.Math.NumberTheory.PisanoPeriod.fib n = fib n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
      have e1 : E213.Lib.Math.NumberTheory.PisanoPeriod.fib (k + 2)
              = E213.Lib.Math.NumberTheory.PisanoPeriod.fib k
                + E213.Lib.Math.NumberTheory.PisanoPeriod.fib (k + 1) := rfl
      have e2 : fib (k + 2) = fib k + fib (k + 1) := fib_rec k
      rw [e1, e2,
          ih k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k)
                  (Nat.le_succ_of_le (Nat.le_refl _))),
          ih (k + 1) (Nat.lt_succ_self (k + 1))]

/-! ## §1 — a *bounded* positive zero exists (`≤ m*m`)

A bounded Pisano period is reconstructed from the pigeonhole collision on
consecutive-pair states (the gap of two indices `< m*m+1` is `≤ m*m`), so that
the apparition can be defined with a concrete (provable) fuel `m*m`.  Reuses the
exported `stateVal`, `extend_forward`, `extend_back`, `step_shift` machinery.
All identities are stated in `PisanoPeriod.fib` (written `fibP`) and bridged. -/

/-- Local alias for the Pisano-side `fib` (definitionally `fib` via `fibP_eq_fib`). -/
abbrev fibP := E213.Lib.Math.NumberTheory.PisanoPeriod.fib

/-- A bounded collision: distinct indices `i, j ≤ m*m` agreeing on the
    consecutive-pair state.  (Same construction as `state_collision`, but the
    `Fin (m*m+1)` bound on the indices is retained.) -/
theorem bounded_collision {m : Nat} (hm : 0 < m) :
    ∃ i j : Nat, i ≤ m * m ∧ j ≤ m * m ∧ i ≠ j ∧
      fibP i % m = fibP j % m ∧ fibP (i + 1) % m = fibP (j + 1) % m := by
  let g : Fin (m * m + 1) → Fin (m * m) :=
    fun k => ⟨stateVal m k.val, stateVal_lt hm k.val⟩
  have hlt : m * m < m * m + 1 := Nat.lt_succ_self _
  obtain ⟨i, j, hij, hg⟩ := exists_collision_lt hlt g
  have hval : stateVal m i.val = stateVal m j.val := congrArg Fin.val hg
  have hbi : fibP (i.val + 1) % m < m := Nat.mod_lt _ hm
  have hbj : fibP (j.val + 1) % m < m := Nat.mod_lt _ hm
  have hdiv : fibP i.val % m = fibP j.val % m := by
    have li : stateVal m i.val / m = fibP i.val % m :=
      encode_div hm (fibP i.val % m) (fibP (i.val + 1) % m) hbi
    have lj : stateVal m j.val / m = fibP j.val % m :=
      encode_div hm (fibP j.val % m) (fibP (j.val + 1) % m) hbj
    rw [← li, ← lj, hval]
  have hmod : fibP (i.val + 1) % m = fibP (j.val + 1) % m := by
    have li : stateVal m i.val % m = fibP (i.val + 1) % m :=
      encode_mod hm (fibP i.val % m) (fibP (i.val + 1) % m) hbi
    have lj : stateVal m j.val % m = fibP (j.val + 1) % m :=
      encode_mod hm (fibP j.val % m) (fibP (j.val + 1) % m) hbj
    rw [← li, ← lj, hval]
  refine ⟨i.val, j.val, Nat.le_of_lt_succ i.isLt, Nat.le_of_lt_succ j.isLt, ?_, hdiv, hmod⟩
  intro h; exact hij (Fin.ext h)

/-- A bounded positive period: `0 < p ≤ m*m` with `fibP (n+p) % m = fibP n % m`
    for every `n`.  Anchor = smaller colliding index, `p` = the gap (`≤ m*m`). -/
theorem bounded_period {m : Nat} (hm : 0 < m) :
    ∃ p, 0 < p ∧ p ≤ m * m ∧ ∀ n, fibP (n + p) % m = fibP n % m := by
  obtain ⟨i, j, hi, hj, hij, hdi, hmi⟩ := bounded_collision hm
  -- Build a positive period `p = |i - j| ≤ m*m` with anchor `a = min i j`.
  rcases Nat.lt_or_ge i j with hlt | hge
  · refine ⟨j - i, sub_pos_of_lt hlt, Nat.le_trans (Nat.sub_le j i) hj, ?_⟩
    have ha : fibP (i + (j - i)) % m = fibP i % m := by
      have hp : i + (j - i) = j := add_sub_of_le (Nat.le_of_lt hlt)
      rw [hp]; exact hdi.symm
    have ha1 : fibP (i + 1 + (j - i)) % m = fibP (i + 1) % m := by
      have e : i + 1 + (j - i) = j + 1 := by
        rw [Nat.add_right_comm, add_sub_of_le (Nat.le_of_lt hlt)]
      rw [e]; exact hmi.symm
    intro n
    rcases Nat.lt_or_ge n i with hni | hni
    · exact extend_back hm i ha ha1 (i - n) n (add_sub_of_le (Nat.le_of_lt hni))
    · have ht : i + (n - i) = n := add_sub_of_le hni
      have hgen := extend_forward (m := m) (p := j - i)
        (fun b h h1 => step_shift b h h1) i ha ha1 (n - i)
      rw [ht] at hgen; exact hgen
  · have hlt : j < i := Nat.lt_of_le_of_ne hge (fun e => hij e.symm)
    refine ⟨i - j, sub_pos_of_lt hlt, Nat.le_trans (Nat.sub_le i j) hi, ?_⟩
    have ha : fibP (j + (i - j)) % m = fibP j % m := by
      have hp : j + (i - j) = i := add_sub_of_le (Nat.le_of_lt hlt)
      rw [hp]; exact hdi
    have ha1 : fibP (j + 1 + (i - j)) % m = fibP (j + 1) % m := by
      have e : j + 1 + (i - j) = i + 1 := by
        rw [Nat.add_right_comm, add_sub_of_le (Nat.le_of_lt hlt)]
      rw [e]; exact hmi
    intro n
    rcases Nat.lt_or_ge n j with hnj | hnj
    · exact extend_back hm j ha ha1 (j - n) n (add_sub_of_le (Nat.le_of_lt hnj))
    · have ht : j + (n - j) = n := add_sub_of_le hnj
      have hgen := extend_forward (m := m) (p := i - j)
        (fun b h h1 => step_shift b h h1) j ha ha1 (n - j)
      rw [ht] at hgen; exact hgen

/-- **A bounded positive zero exists.**  Setting `n = 0` in the bounded period:
    `fibP (0+p) % m = fibP 0 % m = 0`, so `m ∣ fib p` with `0 < p ≤ m*m`. -/
theorem exists_apparition_le {m : Nat} (hm : 0 < m) :
    ∃ k, 0 < k ∧ k ≤ m * m ∧ m ∣ fib k := by
  obtain ⟨p, hp, hple, hper⟩ := bounded_period hm
  refine ⟨p, hp, hple, ?_⟩
  have h := hper 0
  -- h : fibP (0 + p) % m = fibP 0 % m
  have e0 : (0 : Nat) + p = p := Nat.zero_add p
  rw [e0] at h
  -- fibP 0 = 0
  have hz : fibP 0 % m = 0 := rfl
  rw [hz] at h
  -- h : fibP p % m = 0 ; bridge fibP p = fib p
  have h' : fib p % m = 0 := (fibP_eq_fib p) ▸ h
  exact dvd_of_mod_eq_zero h'

/-- **A positive zero exists** (existence form, item 1). -/
theorem exists_apparition {m : Nat} (hm : 0 < m) : ∃ k, 0 < k ∧ m ∣ fib k := by
  obtain ⟨k, hk, _, hd⟩ := exists_apparition_le hm
  exact ⟨k, hk, hd⟩

/-! ## §2 — the least zero: the rank of apparition

Re-instantiates `leastPeriodFrom`'s bounded-least-witness idiom with the test
`m ∣ fib k` (decided as `fib k % m = 0`). -/

/-- Bool test: `m ∣ fib k`, decided on the residue. -/
def isZeroB (m k : Nat) : Bool := Nat.beq (fib k % m) 0

/-- `Nat.beq` reflexivity, ∅-axiom (core carries propext). -/
theorem beq_refl_pure : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_refl_pure n

theorem isZeroB_iff {m : Nat} (hm : 0 < m) (k : Nat) : isZeroB m k = true ↔ m ∣ fib k := by
  unfold isZeroB
  constructor
  · intro h
    exact dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h)
  · intro h
    rw [mod_zero_of_dvd hm h]; exact beq_refl_pure 0

/-- Smallest `k ≥ start` with `isZeroB m k`, fuel-bounded.  Mirrors
    `PisanoPeriodMinimal.leastPeriodFrom`. -/
def leastApparitionFrom : Nat → Nat → Nat → Nat
  | 0,     k, _ => k
  | f + 1, k, m =>
    match isZeroB m k with
    | true  => k
    | false => leastApparitionFrom f (k + 1) m

/-- **Spec of the scan** (copied structure from `leastPeriodFrom_spec`). -/
theorem leastApparitionFrom_spec {m : Nat} (hm : 0 < m) :
    ∀ (fuel k P : Nat), 0 < k → m ∣ fib P → k ≤ P → P ≤ k + fuel →
      (∀ q, 0 < q → q < k → ¬ m ∣ fib q) →
      (0 < leastApparitionFrom fuel k m
        ∧ m ∣ fib (leastApparitionFrom fuel k m)
        ∧ ∀ q, 0 < q → m ∣ fib q → leastApparitionFrom fuel k m ≤ q) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k P hk hP hkP hfuel hbelow
    show (0 < k ∧ m ∣ fib k ∧ ∀ q, 0 < q → m ∣ fib q → k ≤ q)
    have hPk : P ≤ k := by rw [Nat.add_zero] at hfuel; exact hfuel
    have heq : k = P := Nat.le_antisymm hkP hPk
    have hperk : m ∣ fib k := by rw [heq]; exact hP
    refine ⟨hk, hperk, ?_⟩
    intro q hq hperq
    rcases Nat.lt_or_ge q k with hqk | hqk
    · exact absurd hperq (hbelow q hq hqk)
    · exact hqk
  | succ f ih =>
    intro k P hk hP hkP hfuel hbelow
    show (0 < (match isZeroB m k with | true => k | false => leastApparitionFrom f (k + 1) m)
        ∧ m ∣ fib (match isZeroB m k with | true => k | false => leastApparitionFrom f (k + 1) m)
        ∧ ∀ q, 0 < q → m ∣ fib q →
            (match isZeroB m k with | true => k | false => leastApparitionFrom f (k + 1) m) ≤ q)
    have hcases : isZeroB m k = true ∨ isZeroB m k = false := by
      cases isZeroB m k with
      | true => exact Or.inl rfl
      | false => exact Or.inr rfl
    rcases hcases with htest | htest
    · have hbr : (match isZeroB m k with | true => k | false => leastApparitionFrom f (k + 1) m)
                  = k := by rw [htest]
      rw [hbr]
      have hperk : m ∣ fib k := (isZeroB_iff hm k).mp htest
      refine ⟨hk, hperk, ?_⟩
      intro q hq hperq
      rcases Nat.lt_or_ge q k with hqk | hqk
      · exact absurd hperq (hbelow q hq hqk)
      · exact hqk
    · have hbr : (match isZeroB m k with | true => k | false => leastApparitionFrom f (k + 1) m)
                  = leastApparitionFrom f (k + 1) m := by rw [htest]
      rw [hbr]
      have hknotper : ¬ m ∣ fib k := by
        intro hper
        have : isZeroB m k = true := (isZeroB_iff hm k).mpr hper
        rw [htest] at this; exact Bool.noConfusion this
      have hkltP : k < P := by
        rcases Nat.lt_or_ge k P with h | h
        · exact h
        · exact absurd (Nat.le_antisymm hkP h ▸ hP) hknotper
      have hk1P : k + 1 ≤ P := Nat.succ_le_of_lt hkltP
      have hfuel' : P ≤ (k + 1) + f := by
        have e : k + (f + 1) = (k + 1) + f := by rw [Nat.add_succ, Nat.succ_add]
        rw [e] at hfuel; exact hfuel
      have hk1 : 0 < k + 1 := Nat.succ_pos k
      have hbelow' : ∀ q, 0 < q → q < k + 1 → ¬ m ∣ fib q := by
        intro q hq hqlt
        rcases Nat.lt_or_ge q k with hqk | hqk
        · exact hbelow q hq hqk
        · have : q = k := Nat.le_antisymm (Nat.le_of_lt_succ hqlt) hqk
          rw [this]; exact hknotper
      exact ih (k + 1) P hk1 hP hk1P hfuel' hbelow'

/-- **The rank of apparition** α(m): the least positive `k` with `m ∣ fib k`.
    Fuel `m*m` suffices: a positive zero `≤ m*m` exists (`exists_apparition_le`),
    so the scan from `k = 1` finds it within `m*m` steps. -/
def apparition (m : Nat) : Nat := leastApparitionFrom (m * m) 1 m

/-- **α(m) is well-defined**: positive, a zero, and the least positive zero. -/
theorem apparition_spec {m : Nat} (hm : 0 < m) :
    0 < apparition m
      ∧ m ∣ fib (apparition m)
      ∧ ∀ q, 0 < q → m ∣ fib q → apparition m ≤ q := by
  obtain ⟨P, hPpos, hPle, hPd⟩ := exists_apparition_le hm
  have hk : 0 < 1 := Nat.one_pos
  have h1P : 1 ≤ P := hPpos
  have hfuel : P ≤ 1 + m * m := Nat.le_trans hPle (Nat.le_add_left (m * m) 1)
  have hbelow : ∀ q, 0 < q → q < 1 → ¬ m ∣ fib q := by
    intro q hq hq1; exact absurd hq1 (Nat.not_lt_of_le hq)
  exact leastApparitionFrom_spec hm (m * m) 1 P hk hPd h1P hfuel hbelow

theorem apparition_pos {m : Nat} (hm : 0 < m) : 0 < apparition m :=
  (apparition_spec hm).1

theorem dvd_fib_apparition {m : Nat} (hm : 0 < m) : m ∣ fib (apparition m) :=
  (apparition_spec hm).2.1

theorem apparition_least {m : Nat} (hm : 0 < m) :
    ∀ q, 0 < q → m ∣ fib q → apparition m ≤ q :=
  (apparition_spec hm).2.2

/-! ## §3 — Direction A: multiples of α are zeros -/

/-- **Direction A** — `apparition m ∣ n → m ∣ fib n`.  Write `n = α·k`; then
    `fib α ∣ fib (α·k) = fib n` (`fib_dvd_fib_mul`), and `m ∣ fib α`
    (`dvd_fib_apparition`), so `m ∣ fib n` by transitivity. -/
theorem dvd_fib_of_apparition_dvd {m n : Nat} (hm : 0 < m)
    (h : apparition m ∣ n) : m ∣ fib n := by
  obtain ⟨k, hk⟩ := h
  -- fib α ∣ fib (α·k)
  have hdiv : fib (apparition m) ∣ fib (apparition m * k) := fib_dvd_fib_mul (apparition m) k
  -- rewrite the index back to n
  rw [← hk] at hdiv
  exact dvd_trans_213 (dvd_fib_apparition hm) hdiv

/-! ## §4 — Direction B (★ the prize): every zero is a multiple of α -/

/-- **Direction B** — `m ∣ fib n → apparition m ∣ n`.

    For `n = 0`, `α ∣ 0` trivially.  For `n > 0`: `m ∣ fib n` and
    `m ∣ fib α`, so `m ∣ gcd(fib n, fib α) = fib (gcd n α)` (`fib_gcd`).
    `gcd n α` is a positive index (since `n > 0`) dividing both `n` and `α`,
    so by minimality of `α` (`apparition_least`), `α ≤ gcd n α`; and
    `gcd n α ∣ α` with `α > 0` gives `gcd n α ≤ α`.  Hence `gcd n α = α`,
    so `α = gcd n α ∣ n`. -/
theorem apparition_dvd_of_dvd_fib {m n : Nat} (hm : 0 < m)
    (h : m ∣ fib n) : apparition m ∣ n := by
  cases Nat.eq_zero_or_pos n with
  | inl hn0 =>
    -- n = 0 : α ∣ 0
    rw [hn0]; exact ⟨0, (Nat.mul_zero _).symm⟩
  | inr hnpos =>
    have hαpos : 0 < apparition m := apparition_pos hm
    -- m divides gcd(fib n, fib α)
    have hg : m ∣ gcd213 (fib n) (fib (apparition m)) :=
      gcd213_greatest (fib n) (fib (apparition m)) m h (dvd_fib_apparition hm)
    -- gcd(fib n, fib α) = fib (gcd n α)
    have hfg : gcd213 (fib n) (fib (apparition m)) = fib (gcd213 n (apparition m)) :=
      fib_gcd n (apparition m)
    have hmg : m ∣ fib (gcd213 n (apparition m)) := hfg ▸ hg
    -- gcd n α divides both n and α
    have hdn : gcd213 n (apparition m) ∣ n := gcd213_dvd_left n (apparition m)
    have hdα : gcd213 n (apparition m) ∣ apparition m := gcd213_dvd_right n (apparition m)
    -- gcd n α is positive (it divides n > 0)
    have hgpos : 0 < gcd213 n (apparition m) := by
      rcases Nat.eq_zero_or_pos (gcd213 n (apparition m)) with hz | hp
      · -- 0 ∣ n ⟹ n = 0, contradiction
        exfalso
        obtain ⟨c, hc⟩ := hdn
        rw [hz, Nat.zero_mul] at hc
        exact absurd hc (Nat.not_eq_zero_of_lt hnpos)
      · exact hp
    -- minimality: α ≤ gcd n α
    have hle1 : apparition m ≤ gcd213 n (apparition m) :=
      apparition_least hm (gcd213 n (apparition m)) hgpos hmg
    -- gcd n α ≤ α  (divides α > 0)
    have hle2 : gcd213 n (apparition m) ≤ apparition m :=
      le_of_dvd_pos _ _ hαpos hdα
    -- so gcd n α = α
    have heq : gcd213 n (apparition m) = apparition m := Nat.le_antisymm hle2 hle1
    -- α = gcd n α ∣ n
    rw [← heq]; exact hdn

/-! ## §5 — the biconditional + smoke tests -/

/-- **`m ∣ fib n ↔ apparition m ∣ n`** — zeros are exactly the multiples of α. -/
theorem dvd_fib_iff {m : Nat} (hm : 0 < m) (n : Nat) :
    m ∣ fib n ↔ apparition m ∣ n :=
  ⟨apparition_dvd_of_dvd_fib hm, dvd_fib_of_apparition_dvd hm⟩

-- Smoke: α(2)=3, α(3)=4, α(5)=5.
-- fib: 0,1,1,2,3,5,8,...  fib 3 = 2 (so α(2)=3); fib 4 = 3 (α(3)=4); fib 5 = 5 (α(5)=5).
example : apparition 2 = 3 := by decide
example : apparition 3 = 4 := by decide
example : apparition 5 = 5 := by decide

#print axioms exists_apparition
#print axioms apparition_spec
#print axioms dvd_fib_of_apparition_dvd
#print axioms apparition_dvd_of_dvd_fib
#print axioms dvd_fib_iff

end E213.Lib.Math.NumberTheory.FibonacciApparition
