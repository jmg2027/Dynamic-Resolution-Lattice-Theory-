import E213.Lib.Math.Cauchy.ZeroRunNonHolonomic
import E213.Lib.Math.Cauchy.NonHolonomicWitness

/-!
# A bounded, genuinely non-holonomic witness — the indicator of the powers of two

The indicator `χ n = 1` if `n` is a power of two, else `0`, is **bounded** (values in `{0,1}`)
yet **non-holonomic**: the gaps between consecutive powers of two grow without bound, so `χ`
has arbitrarily long zero-runs at arbitrarily large positions, and it has infinitely many `1`s.
By `ZeroRunNonHolonomic.zero_run_not_homogRec` it then satisfies no homogeneous finite-window
recurrence with eventually-nonzero leading coefficient — it is not P-recursive.

This is the second ∅-axiom non-holonomicity certificate in the corpus, on an axis **orthogonal**
to `NonHolonomicWitness`: that one is unbounded (growth, Klazar); this one is bounded
(zero-runs, homogeneity).  Non-holonomicity is detected both by growing too fast and by being
too sparse.
-/

namespace E213.Lib.Math.Cauchy.ZeroRunNonHolonomicWitness

open E213.Lib.Math.Cauchy.ZeroRunNonHolonomic (HomogRec zero_run_not_homogRec)
open E213.Lib.Math.Cauchy.NonHolonomicWitness (one_le_pow)

/-! ## §1 — elementary powers-of-two arithmetic -/

/-- `n < 2ⁿ`. -/
theorem lt_two_pow (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_two]
    have h1 : 1 ≤ 2 ^ n := one_le_pow 2 n (by decide)
    have h3 : 2 ^ n < 2 ^ n + 2 ^ n := Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le (by decide) h1)
    exact Nat.lt_of_le_of_lt ih h3

/-- `2^(j+1) = 2^j + 2^j`. -/
theorem two_pow_succ (j : Nat) : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by
  rw [Nat.pow_succ, Nat.mul_two]

/-- `2 ≤ 2^(j+1)`. -/
theorem two_le_two_pow_succ (j : Nat) : 2 ≤ 2 ^ (j + 1) := by
  rw [two_pow_succ]
  exact Nat.add_le_add (one_le_pow 2 j (by decide)) (one_le_pow 2 j (by decide))

/-- `2^(j+1) / 2 = 2^j`. -/
theorem two_pow_succ_div_two (j : Nat) : 2 ^ (j + 1) / 2 = 2 ^ j := by
  rw [Nat.pow_succ]
  exact E213.Meta.Nat.NatDiv213.mul_div_self_pure (2 ^ j) 2 (by decide)

/-- `2^(j+1) % 2 = 0`. -/
theorem two_pow_succ_mod_two (j : Nat) : 2 ^ (j + 1) % 2 = 0 := by
  rw [Nat.pow_succ, Nat.mul_comm]
  exact E213.Tactic.NatHelper.mul_mod_right 2 (2 ^ j)

/-- `2^a < 2^b ⟹ a < b` (contrapositive of monotonicity). -/
theorem pow2_lt_imp {a b : Nat} (h : 2 ^ a < 2 ^ b) : a < b := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact hlt
  · exact absurd (Nat.pow_le_pow_right (by decide) hge) (Nat.not_le_of_gt h)

/-! ## §2 — the power-of-two indicator -/

/-- Fuel-driven power-of-two test (structural recursion on fuel, `Prop`-`if`). -/
def pow2aux : Nat → Nat → Bool
  | 0,     n => decide (n = 1)
  | (f+1), n =>
      if n = 1 then true
      else if (n % 2 = 0 ∧ n ≠ 0) then pow2aux f (n / 2)
      else false

/-- The power-of-two indicator. -/
def isPow2 (n : Nat) : Bool := pow2aux n n

/-- The integer witness `χ`: `1` on powers of two, `0` elsewhere. -/
def chi (n : Nat) : Int := if isPow2 n then 1 else 0

theorem chi_one_of {n : Nat} (h : isPow2 n = true) : chi n = 1 := by
  unfold chi; rw [h]; exact if_pos rfl
theorem chi_zero_of {n : Nat} (h : isPow2 n = false) : chi n = 0 := by
  unfold chi; rw [h]; exact if_neg (by decide)

/-- `pow2aux f (2^j) = true` whenever the fuel exceeds `j`. -/
theorem pow2aux_pow : ∀ j f, j < f → pow2aux f (2 ^ j) = true := by
  intro j
  induction j with
  | zero =>
    intro f hf
    cases f with
    | zero => exact absurd hf (Nat.lt_irrefl 0)
    | succ f => show (if (2 ^ 0) = 1 then true else _) = true; rw [if_pos (by decide)]
  | succ j ih =>
    intro f hf
    cases f with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ f =>
      have hjf : j < f := Nat.lt_of_succ_lt_succ hf
      show (if (2 ^ (j+1)) = 1 then true
            else if (2 ^ (j+1) % 2 = 0 ∧ 2 ^ (j+1) ≠ 0) then pow2aux f (2 ^ (j+1) / 2)
            else false) = true
      rw [if_neg (by
            intro h; exact absurd (h ▸ two_le_two_pow_succ j) (by decide)),
          if_pos ⟨two_pow_succ_mod_two j, by
            intro h; exact absurd (h ▸ two_le_two_pow_succ j) (by decide)⟩,
          two_pow_succ_div_two j]
      exact ih f hjf

/-- `χ (2^j) = 1`. -/
theorem chi_pow (j : Nat) : chi (2 ^ j) = 1 :=
  chi_one_of (pow2aux_pow j (2 ^ j) (lt_two_pow j))

/-- `pow2aux f n = true ⟹ n` is a power of two. -/
theorem pow2aux_true_imp : ∀ f n, pow2aux f n = true → ∃ j, 2 ^ j = n := by
  intro f
  induction f with
  | zero =>
    intro n h
    have : n = 1 := of_decide_eq_true h
    exact ⟨0, by rw [this]⟩
  | succ f ih =>
    intro n h
    unfold pow2aux at h
    split at h
    · next h1 => exact ⟨0, by rw [h1]⟩
    · split at h
      · next h2 =>
          obtain ⟨j', hj'⟩ := ih (n / 2) h
          refine ⟨j' + 1, ?_⟩
          have hdm := E213.Meta.Nat.AddMod213.div_add_mod n 2
          rw [h2.1, Nat.add_zero, Nat.two_mul] at hdm
          -- hdm : n / 2 + n / 2 = n
          rw [two_pow_succ, hj']; exact hdm
      · exact absurd h (by decide)

/-- `χ m = 0` for `m` strictly between consecutive powers of two. -/
theorem chi_zero_between {j m : Nat} (hlo : 2 ^ j < m) (hhi : m < 2 ^ (j + 1)) : chi m = 0 := by
  have hfalse : isPow2 m = false := by
    cases hb : isPow2 m with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨j', hj'⟩ := pow2aux_true_imp m m hb
      rw [← hj'] at hlo hhi
      have h1 : j < j' := pow2_lt_imp hlo
      have h2 : j' < j + 1 := pow2_lt_imp hhi
      exact absurd (Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ h2)) (Nat.lt_irrefl j)
  exact chi_zero_of hfalse

/-! ## §3 — `χ` inhabits the zero-run criterion, hence is non-holonomic -/

/-- **Arbitrarily long zero-runs at arbitrarily large positions.** -/
theorem chi_runs : ∀ k R₀, ∃ N, R₀ ≤ N ∧ ∀ i, i < k → chi (N + i) = 0 := by
  intro k R₀
  -- choose j = R₀ + k, so 2^j > R₀ and 2^j > k
  have hbig : R₀ + k < 2 ^ (R₀ + k) := lt_two_pow (R₀ + k)
  refine ⟨2 ^ (R₀ + k) + 1, ?_, ?_⟩
  · -- R₀ ≤ 2^(R₀+k) + 1
    have : R₀ ≤ R₀ + k := Nat.le_add_right R₀ k
    exact Nat.le_trans this (Nat.le_trans (Nat.le_of_lt hbig) (Nat.le_succ _))
  · intro i hi
    have hk : k < 2 ^ (R₀ + k) :=
      Nat.lt_of_le_of_lt (Nat.le_add_left k R₀) hbig
    apply chi_zero_between (j := R₀ + k)
    · -- 2^(R₀+k) < 2^(R₀+k)+1+i
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ i)
    · -- 2^(R₀+k)+1+i < 2^(R₀+k+1) = 2^(R₀+k)+2^(R₀+k)
      rw [Nat.add_assoc, two_pow_succ]
      apply Nat.add_lt_add_left
      -- 1 + i < 2^(R₀+k)  (since 1+i = i+1 ≤ k < 2^(R₀+k))
      have h1i : 1 + i ≤ k :=
        Nat.le_trans (Nat.le_of_eq (Nat.add_comm 1 i)) (Nat.succ_le_of_lt hi)
      exact Nat.lt_of_le_of_lt h1i hk

/-- **Infinitely many nonzero terms** (the powers of two). -/
theorem chi_inf : ∀ M, ∃ m, M ≤ m ∧ chi m ≠ 0 := by
  intro M
  refine ⟨2 ^ M, Nat.le_of_lt (lt_two_pow M), ?_⟩
  rw [chi_pow M]; decide

/-- ★★★ **The powers-of-two indicator is non-holonomic** — bounded, yet satisfies no
    homogeneous finite-window recurrence with eventually-nonzero leading coefficient.  The
    growth-free, sparse companion to `NonHolonomicWitness.superFact_nonHolonomic`. -/
theorem chi_nonHolonomic : ¬ HomogRec chi :=
  zero_run_not_homogRec chi chi_runs chi_inf

/-- **Non-holonomic, yet every value is computable.**  `χ` satisfies no finite recurrence
    (`chi_nonHolonomic`), but it is a total function whose every value is a decidable `0`/`1`
    (produced by `isPow2`).  Non-holonomic ≠ non-computable: a real's values/digits can be
    generated by a *pointing* (an algorithm) even when no finite recurrence governs them —
    which is exactly how the digits `3.141592…` of the (conjecturally non-holonomic-CF) π are
    obtained, through a computable pointing other than its continued fraction.  The pointing
    approaches; it never equals (`FlatOntologyClosure.object1_not_surjective`). -/
theorem chi_values : ∀ n, chi n = 0 ∨ chi n = 1 := by
  intro n
  cases h : isPow2 n with
  | true => exact Or.inr (chi_one_of h)
  | false => exact Or.inl (chi_zero_of h)

open E213.Lib.Math.Cauchy.ZeroRunNonHolonomic (AutoRec two_continuations_not_autoRec)

/-- ★★★ **`χ` is generated by no autonomous finite-window machine.**  An all-zero length-`k`
    window is continued in `χ` once by `0` (mid zero-run) and once by `1` (just before a power
    of two), for every `k` — two outputs from one "state", which no deterministic time-invariant
    finite-state machine can produce.  This is the FSM reading of non-holonomicity: `χ` needs
    unbounded memory; the powers-of-two trace escapes every finite-state machine (the
    continued-fraction-scale shadow of `CoResidue.spineL_escapes`). -/
theorem chi_not_autoRec : ¬ AutoRec chi := by
  apply two_continuations_not_autoRec chi
  intro k
  obtain ⟨N, _, hNrun⟩ := chi_runs (k + 1) 0
  have hkle : k ≤ 2 ^ (k + 2) :=
    Nat.le_of_lt (Nat.lt_of_lt_of_le (lt_two_pow k)
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right k 2)))
  have hk1 : k < 2 ^ (k + 1) :=
    Nat.lt_of_lt_of_le (lt_two_pow k) (Nat.pow_le_pow_right (by decide) (Nat.le_succ k))
  have e1 : 2 ^ (k + 2) - k = 2 ^ (k + 1) + (2 ^ (k + 1) - k) := by
    rw [two_pow_succ (k + 1)]
    exact E213.Tactic.NatHelper.add_sub_assoc (2 ^ (k + 1)) (Nat.le_of_lt hk1)
  refine ⟨N, 2 ^ (k + 2) - k, 0, 1, by decide, ?_, ?_, ?_, ?_⟩
  · exact fun i hi => hNrun i (Nat.lt_trans hi (Nat.lt_succ_self k))
  · exact hNrun k (Nat.lt_succ_self k)
  · intro i hi
    apply chi_zero_between (j := k + 1)
    · -- 2^(k+1) < (2^(k+2)-k) + i
      have hlolt : 2 ^ (k + 1) < 2 ^ (k + 2) - k := by
        rw [e1]; exact Nat.lt_add_of_pos_right (E213.Tactic.NatHelper.sub_pos_of_lt hk1)
      exact Nat.lt_of_lt_of_le hlolt (Nat.le_add_right _ i)
    · -- (2^(k+2)-k) + i < 2^(k+1+1) = 2^(k+2)
      calc 2 ^ (k + 2) - k + i
          < 2 ^ (k + 2) - k + k := Nat.add_lt_add_left hi _
        _ = 2 ^ (k + 2) := E213.Tactic.NatHelper.sub_add_cancel hkle
  · -- χ(N'+k) = χ(2^(k+2)) = 1
    rw [E213.Tactic.NatHelper.sub_add_cancel hkle]; exact chi_pow (k + 2)

end E213.Lib.Math.Cauchy.ZeroRunNonHolonomicWitness
