import E213.Lib.Math.Cauchy.MorseHedlund
import E213.Lib.Math.Cauchy.ZeroRunNonHolonomicWitness
import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper

/-!
# Thue–Morse is aperiodic — a genuinely dense witness for the Morse–Hedlund route

`MorseHedlund.aperiodic_not_autoRec` rejects *any* bounded aperiodic `Bool`-sequence from the
autonomous finite-state machine class.  The powers-of-two indicator inhabits it but has long
runs.  **Thue–Morse** is the canonical *dense* witness — run-length `≤ 2` — and this file proves
its aperiodicity ∅-axiom by the self-similar descent on the period.

`tm` is defined by the Thue–Morse recurrence (`tm(2n)=tm(n)`, `tm(2n+1)=¬tm(n)`) via
**fuel-structural** recursion (well-founded recursion would leak `propext`), with a
fuel-irrelevance lemma making the canonical fuel `= n`.
-/

namespace E213.Lib.Math.Cauchy.ThueMorseAperiodic

open E213.Lib.Math.Cauchy.MorseHedlund (EvPeriodic aperiodic_not_autoRec b2n)
open E213.Lib.Math.Cauchy.ZeroRunNonHolonomic (AutoRec)
open E213.Lib.Math.Cauchy.ZeroRunNonHolonomicWitness
  (isPow2 pow2aux_pow pow2aux_true_imp lt_two_pow)

/-- Fuel-structural Thue–Morse kernel. -/
def tmF : Nat → Nat → Bool
  | 0,     _     => false
  | _,     0     => false
  | (f+1), (n+1) =>
      if (n + 1) % 2 = 0 then tmF f ((n + 1) / 2) else !tmF f ((n + 1) / 2)

/-- Thue–Morse: `tm n = tmF n n` (fuel = value is always enough). -/
def tm (n : Nat) : Bool := tmF n n

/-- **Fuel irrelevance**: any fuel `≥ n` gives the canonical value. -/
theorem tmF_canon : ∀ T n f, n < T → n ≤ f → tmF f n = tmF n n := by
  intro T
  induction T with
  | zero => intro n f h _; exact absurd h (Nat.not_lt_zero n)
  | succ T ih =>
    intro n f hnT hnf
    cases n with
    | zero => cases f <;> rfl
    | succ m =>
      cases f with
      | zero => exact absurd hnf (Nat.not_succ_le_zero m)
      | succ f' =>
        have hd : (m + 1) / 2 < m + 1 := by
          apply E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul
          rw [Nat.two_mul]; exact Nat.lt_add_of_pos_left (Nat.succ_pos m)
        have hdT : (m + 1) / 2 < T := Nat.lt_of_lt_of_le hd (Nat.le_of_lt_succ hnT)
        have hf' : (m + 1) / 2 ≤ f' := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hd hnf)
        have hm' : (m + 1) / 2 ≤ m := Nat.le_of_lt_succ hd
        have hrec : tmF f' ((m + 1) / 2) = tmF m ((m + 1) / 2) := by
          rw [ih ((m + 1) / 2) f' hdT hf', ih ((m + 1) / 2) m hdT hm']
        show (if (m + 1) % 2 = 0 then tmF f' ((m + 1) / 2) else !tmF f' ((m + 1) / 2))
            = (if (m + 1) % 2 = 0 then tmF m ((m + 1) / 2) else !tmF m ((m + 1) / 2))
        rw [hrec]

/-- `tmF f n = tm n` for `n ≤ f`. -/
theorem tmF_eq_tm (n f : Nat) (h : n ≤ f) : tmF f n = tm n :=
  tmF_canon (n + 1) n f (Nat.lt_succ_self n) h

/-- `tm(2n) = tm(n)`. -/
theorem tm_even (n : Nat) : tm (2 * n) = tm n := by
  cases n with
  | zero => rfl
  | succ m =>
    have key : 2 * (m + 1) = (2 * m + 1) + 1 := by rw [Nat.mul_succ]
    have hmod : ((2 * m + 1) + 1) % 2 = 0 := by
      rw [← key]; exact E213.Tactic.NatHelper.mul_mod_right 2 (m + 1)
    have hdiv : ((2 * m + 1) + 1) / 2 = m + 1 := by
      rw [← key, Nat.mul_comm]
      exact E213.Meta.Nat.NatDiv213.mul_div_self_pure (m + 1) 2 (by decide)
    have hle : m + 1 ≤ 2 * m + 1 := by
      rw [Nat.two_mul]; exact Nat.succ_le_succ (Nat.le_add_left m m)
    show tmF (2 * (m + 1)) (2 * (m + 1)) = tm (m + 1)
    rw [key]
    show (if ((2 * m + 1) + 1) % 2 = 0 then tmF (2 * m + 1) (((2 * m + 1) + 1) / 2)
          else !tmF (2 * m + 1) (((2 * m + 1) + 1) / 2)) = tm (m + 1)
    rw [if_pos hmod, hdiv, tmF_eq_tm (m + 1) (2 * m + 1) hle]

/-- `tm(2n+1) = ¬tm(n)`. -/
theorem tm_odd (n : Nat) : tm (2 * n + 1) = !tm n := by
  have hmod : (2 * n + 1) % 2 = 1 := by
    rw [Nat.add_comm, Nat.mul_comm]
    exact E213.Tactic.NatHelper.add_mul_mod_self_pure 1 2 n
  have hdiv : (2 * n + 1) / 2 = n := by
    rw [Nat.add_comm, E213.Meta.Nat.NatDiv213.add_mul_div_left_pure 1 2 n (by decide)]
    exact Nat.zero_add n
  have hle : n ≤ 2 * n := by rw [Nat.two_mul]; exact Nat.le_add_left n n
  show tmF (2 * n + 1) (2 * n + 1) = !tm n
  show (if (2 * n + 1) % 2 = 0 then tmF (2 * n) ((2 * n + 1) / 2)
        else !tmF (2 * n) ((2 * n + 1) / 2)) = !tm n
  rw [if_neg (by rw [hmod]; decide), hdiv, tmF_eq_tm n (2 * n) hle]

/-- `tm` is not constant: consecutive `(2n, 2n+1)` always differ. -/
theorem tm_pair_differ (n : Nat) : tm (2 * n + 1) ≠ tm (2 * n) := by
  rw [tm_odd, tm_even]; cases tm n <;> decide

/-- A `Bool` never equals its own negation. -/
theorem bool_ne_not (b : Bool) : b ≠ !b := by cases b <;> decide

/-- ★ **Run-length `≤ 2`**: Thue–Morse has *no three consecutive equal values*.  This is what
    makes it the genuinely-*dense* witness — the sparse `zero_run_not_homogRec` route (needing
    arbitrarily long constant runs) provably cannot catch it, so it is caught *only* by the dense
    Morse–Hedlund route.  In any length-`3` window an adjacent differing pair already sits: at an
    even start `(2k, 2k+1) = (tm k, ¬tm k)`; at an odd start the next pair
    `(2(k+1), 2(k+1)+1) = (tm(k+1), ¬tm(k+1))`. -/
theorem tm_run_le_two (n : Nat) (h1 : tm n = tm (n + 1)) (h2 : tm (n + 1) = tm (n + 2)) :
    False := by
  have hdm : 2 * (n / 2) + n % 2 = n := E213.Meta.Nat.AddMod213.div_add_mod n 2
  rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one n with he | ho
  · -- even start: positions n, n+1 are 2k, 2k+1 — they already differ
    have e0 : 2 * (n / 2) = n := by rw [he, Nat.add_zero] at hdm; exact hdm
    have e1 : 2 * (n / 2) + 1 = n + 1 := by rw [e0]
    have ht0 : tm n = tm (n / 2) := (congrArg tm e0.symm).trans (tm_even (n / 2))
    have ht1 : tm (n + 1) = !tm (n / 2) := (congrArg tm e1.symm).trans (tm_odd (n / 2))
    rw [ht0, ht1] at h1
    exact bool_ne_not (tm (n / 2)) h1
  · -- odd start: positions n+1, n+2 are 2(k+1), 2(k+1)+1 — they already differ
    have e0 : 2 * (n / 2) + 1 = n := by rw [ho] at hdm; exact hdm
    have e1 : 2 * (n / 2 + 1) = n + 1 := by rw [Nat.mul_succ]; exact congrArg (· + 1) e0
    have e2 : 2 * (n / 2 + 1) + 1 = n + 2 := congrArg (· + 1) e1
    have ht1 : tm (n + 1) = tm (n / 2 + 1) := (congrArg tm e1.symm).trans (tm_even (n / 2 + 1))
    have ht2 : tm (n + 2) = !tm (n / 2 + 1) := (congrArg tm e2.symm).trans (tm_odd (n / 2 + 1))
    rw [ht1, ht2] at h2
    exact bool_ne_not (tm (n / 2 + 1)) h2

/-! ## The self-similar descent on the period -/

/-- An even period `2q` descends to period `q` (via `tm(2m)=tm(m)`). -/
theorem even_descent (N q : Nat) (hper : ∀ n, N ≤ n → tm (n + 2 * q) = tm n) :
    ∀ m, N ≤ m → tm (m + q) = tm m := by
  intro m hm
  have h2m : N ≤ 2 * m := Nat.le_trans hm (Nat.le_mul_of_pos_left m (by decide))
  have hp := hper (2 * m) h2m
  have e1 : 2 * m + 2 * q = 2 * (m + q) := by rw [Nat.mul_add]
  rw [e1, tm_even (m + q), tm_even m] at hp
  exact hp

/-- An odd period `2r+1` descends to period `2r` (via `tm(2m)=tm(m)`, `tm(2m+1)=¬tm(m)`). -/
theorem odd_descent (N r : Nat) (hper : ∀ n, N ≤ n → tm (n + (2 * r + 1)) = tm n) :
    ∀ m, N ≤ m → tm (m + 2 * r) = tm m := by
  have step : ∀ m, N ≤ m → tm (m + r) = !(tm m) := by
    intro m hm
    have h2m : N ≤ 2 * m := Nat.le_trans hm (Nat.le_mul_of_pos_left m (by decide))
    have hp := hper (2 * m) h2m
    have e1 : 2 * m + (2 * r + 1) = 2 * (m + r) + 1 := by rw [← Nat.add_assoc, ← Nat.mul_add]
    rw [e1, tm_odd (m + r), tm_even m] at hp
    cases hmr : tm (m + r) <;> cases hmm : tm m <;>
      (rw [hmr, hmm] at hp; first | rfl | exact absurd hp (by decide))
  intro m hm
  have e2 : m + 2 * r = (m + r) + r := by rw [Nat.two_mul, ← Nat.add_assoc]
  rw [e2, step (m + r) (Nat.le_trans hm (Nat.le_add_right m r)), step m hm]
  exact Bool.not_not (tm m)

/-- ★★★ **Thue–Morse is not eventually periodic.**  Strong induction on the period: an even
    period halves (`even_descent`), an odd period drops by one to an even one (`odd_descent`), and
    period `1` contradicts `tm_pair_differ` (consecutive `2n, 2n+1` always differ). -/
theorem tm_not_evPeriodic : ¬ EvPeriodic tm := by
  rintro ⟨p, hpos, N, hper⟩
  suffices H : ∀ T p, p < T → 1 ≤ p → ∀ N,
      (∀ n, N ≤ n → tm (n + p) = tm n) → False by
    exact H (p + 1) p (Nat.lt_succ_self p) hpos N hper
  intro T
  induction T with
  | zero => intro p hp _ _ _; exact absurd hp (Nat.not_lt_zero p)
  | succ T ih =>
    intro p hpT hpos N hper
    have hpT' : p ≤ T := Nat.le_of_lt_succ hpT
    rcases Nat.lt_or_ge p 2 with hlt2 | hge2
    · have hp1 : p = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hlt2) hpos
      subst hp1
      exact tm_pair_differ N (hper (2 * N) (Nat.le_mul_of_pos_left N (by decide)))
    · have hdm : 2 * (p / 2) + p % 2 = p := E213.Meta.Nat.AddMod213.div_add_mod p 2
      rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one p with hev | hod
      · -- even: p = 2·(p/2)
        rw [hev, Nat.add_zero] at hdm
        have hq1 : 1 ≤ p / 2 :=
          Nat.le_of_mul_le_mul_left (by rw [Nat.mul_one, hdm]; exact hge2) (by decide)
        have hqltp : p / 2 < p :=
          E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul
            (by rw [E213.Tactic.NatHelper.two_mul]; exact Nat.lt_add_of_pos_left hpos)
        have hper' : ∀ n, N ≤ n → tm (n + 2 * (p / 2)) = tm n := by
          intro n hn; rw [hdm]; exact hper n hn
        exact ih (p / 2) (Nat.lt_of_lt_of_le hqltp hpT') hq1 N (even_descent N (p / 2) hper')
      · -- odd: p = 2·(p/2)+1
        rw [hod] at hdm
        have hr1 : 1 ≤ p / 2 := by
          rcases Nat.eq_zero_or_pos (p / 2) with h0 | h
          · exfalso; rw [h0, Nat.mul_zero, Nat.zero_add] at hdm
            rw [← hdm] at hge2; exact absurd hge2 (by decide)
          · exact h
        have h2r1 : 1 ≤ 2 * (p / 2) := Nat.le_trans hr1 (Nat.le_mul_of_pos_left (p / 2) (by decide))
        have h2rltp : 2 * (p / 2) < p :=
          Nat.lt_of_lt_of_eq (Nat.lt_succ_self (2 * (p / 2))) hdm
        have hper' : ∀ n, N ≤ n → tm (n + (2 * (p / 2) + 1)) = tm n := by
          intro n hn; rw [hdm]; exact hper n hn
        exact ih (2 * (p / 2)) (Nat.lt_of_lt_of_le h2rltp hpT') h2r1 N (odd_descent N (p / 2) hper')

/-- ★★★ **Thue–Morse is generated by no autonomous finite-state machine** — the canonical
    *dense* witness (run-length `≤ 2`, no long runs) for the Morse–Hedlund route. -/
theorem tm_morse_not_autoRec : ¬ AutoRec (fun n => ((b2n (tm n) : Nat) : Int)) :=
  aperiodic_not_autoRec tm tm_not_evPeriodic

/-! ## The automatic structure: `tm n = popcount(n) mod 2`

Thue–Morse escapes the *term-window* machine `AutoRec` (above) yet it is the prototypical
**digit-automatic** sequence: a fixed finite automaton reading the base-`2` digits of the index
emits `tm n`.  Concretely `tm n` is the parity of the binary digit-sum (`popcount`).  This is the
exact place where the two finite-state notions diverge — finite memory *in the digits of the
index* (automatic) versus finite memory *in the previous terms* (window-recurrence): Thue–Morse
has the first and lacks the second.  Aperiodic-but-automatic is the Cobham/Christol boundary
beyond which a sequence is non-holonomic. -/

/-- Fuel-structural binary digit-sum (`popcount`). -/
def s2F : Nat → Nat → Nat
  | 0,     _     => 0
  | _,     0     => 0
  | (f+1), (n+1) => (n + 1) % 2 + s2F f ((n + 1) / 2)

/-- Binary digit-sum: `s2 n = s2F n n`. -/
def s2 (n : Nat) : Nat := s2F n n

/-- **Fuel irrelevance** for `s2F` (mirrors `tmF_canon`). -/
theorem s2F_canon : ∀ T n f, n < T → n ≤ f → s2F f n = s2F n n := by
  intro T
  induction T with
  | zero => intro n f h _; exact absurd h (Nat.not_lt_zero n)
  | succ T ih =>
    intro n f hnT hnf
    cases n with
    | zero => cases f <;> rfl
    | succ m =>
      cases f with
      | zero => exact absurd hnf (Nat.not_succ_le_zero m)
      | succ f' =>
        have hd : (m + 1) / 2 < m + 1 := by
          apply E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul
          rw [Nat.two_mul]; exact Nat.lt_add_of_pos_left (Nat.succ_pos m)
        have hdT : (m + 1) / 2 < T := Nat.lt_of_lt_of_le hd (Nat.le_of_lt_succ hnT)
        have hf' : (m + 1) / 2 ≤ f' := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hd hnf)
        have hm' : (m + 1) / 2 ≤ m := Nat.le_of_lt_succ hd
        show (m + 1) % 2 + s2F f' ((m + 1) / 2) = (m + 1) % 2 + s2F m ((m + 1) / 2)
        rw [ih ((m + 1) / 2) f' hdT hf', ih ((m + 1) / 2) m hdT hm']

/-- `s2F f n = s2 n` for `n ≤ f`. -/
theorem s2F_eq_s2 (n f : Nat) (h : n ≤ f) : s2F f n = s2 n :=
  s2F_canon (n + 1) n f (Nat.lt_succ_self n) h

/-- `popcount(2n) = popcount(n)` (a low zero bit adds nothing). -/
theorem s2_even (n : Nat) : s2 (2 * n) = s2 n := by
  cases n with
  | zero => rfl
  | succ m =>
    have key : 2 * (m + 1) = (2 * m + 1) + 1 := by rw [Nat.mul_succ]
    have hmod : ((2 * m + 1) + 1) % 2 = 0 := by
      rw [← key]; exact E213.Tactic.NatHelper.mul_mod_right 2 (m + 1)
    have hdiv : ((2 * m + 1) + 1) / 2 = m + 1 := by
      rw [← key, Nat.mul_comm]
      exact E213.Meta.Nat.NatDiv213.mul_div_self_pure (m + 1) 2 (by decide)
    have hle : m + 1 ≤ 2 * m + 1 := by
      rw [Nat.two_mul]; exact Nat.succ_le_succ (Nat.le_add_left m m)
    show s2F (2 * (m + 1)) (2 * (m + 1)) = s2 (m + 1)
    rw [key]
    show ((2 * m + 1) + 1) % 2 + s2F (2 * m + 1) (((2 * m + 1) + 1) / 2) = s2 (m + 1)
    rw [hmod, hdiv, Nat.zero_add, s2F_eq_s2 (m + 1) (2 * m + 1) hle]

/-- `popcount(2n+1) = popcount(n) + 1` (a low one bit adds one). -/
theorem s2_odd (n : Nat) : s2 (2 * n + 1) = s2 n + 1 := by
  have hmod : (2 * n + 1) % 2 = 1 := by
    rw [Nat.add_comm, Nat.mul_comm]
    exact E213.Tactic.NatHelper.add_mul_mod_self_pure 1 2 n
  have hdiv : (2 * n + 1) / 2 = n := by
    rw [Nat.add_comm, E213.Meta.Nat.NatDiv213.add_mul_div_left_pure 1 2 n (by decide)]
    exact Nat.zero_add n
  have hle : n ≤ 2 * n := by rw [Nat.two_mul]; exact Nat.le_add_left n n
  show s2F (2 * n + 1) (2 * n + 1) = s2 n + 1
  show (2 * n + 1) % 2 + s2F (2 * n) ((2 * n + 1) / 2) = s2 n + 1
  rw [hmod, hdiv, s2F_eq_s2 n (2 * n) hle, Nat.add_comm]

/-- Parity flips under successor: `((k+1) mod 2 = 1) ↔ ¬(k mod 2 = 1)`, as a `Bool` identity. -/
theorem succ_parity (k : Nat) :
    decide ((k + 1) % 2 = 1) = !decide (k % 2 = 1) := by
  rw [E213.Meta.Nat.AddMod213.add_mod_gen k 1 2]
  rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one k with h | h <;> rw [h] <;> decide

/-- ★★★ **Thue–Morse is `2`-automatic**: `tm n` is the parity of the binary digit-sum
    (`popcount`) of `n`.  A finite automaton reading the base-`2` digits of the index emits the
    sequence — finite memory *in the digits*, the companion to the term-window escape
    `tm_morse_not_autoRec`.  Proven by strong induction matching `tm`'s `even/odd` recurrence
    against `s2`'s. -/
theorem tm_eq_popParity : ∀ n, tm n = decide (s2 n % 2 = 1) := by
  suffices H : ∀ T n, n < T → tm n = decide (s2 n % 2 = 1) by
    intro n; exact H (n + 1) n (Nat.lt_succ_self n)
  intro T
  induction T with
  | zero => intro n h; exact absurd h (Nat.not_lt_zero n)
  | succ T ih =>
    intro n hnT
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; decide
    · have hdm : 2 * (n / 2) + n % 2 = n := E213.Meta.Nat.AddMod213.div_add_mod n 2
      have hhalf : n / 2 < n :=
        E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul
          (by rw [E213.Tactic.NatHelper.two_mul]; exact Nat.lt_add_of_pos_left hnpos)
      have hh : n / 2 < T := Nat.lt_of_lt_of_le hhalf (Nat.le_of_lt_succ hnT)
      rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one n with he | ho
      · have e : 2 * (n / 2) = n := by rw [he, Nat.add_zero] at hdm; exact hdm
        have htm : tm n = tm (n / 2) := (congrArg tm e.symm).trans (tm_even (n / 2))
        have hs2 : s2 n = s2 (n / 2) := (congrArg s2 e.symm).trans (s2_even (n / 2))
        rw [htm, hs2]; exact ih (n / 2) hh
      · have e : 2 * (n / 2) + 1 = n := by rw [ho] at hdm; exact hdm
        have htm : tm n = !tm (n / 2) := (congrArg tm e.symm).trans (tm_odd (n / 2))
        have hs2 : s2 n = s2 (n / 2) + 1 := (congrArg s2 e.symm).trans (s2_odd (n / 2))
        rw [htm, hs2, ih (n / 2) hh]
        exact (succ_parity (s2 (n / 2))).symm

/-! ## The digit counter escapes monotonicity

The `{0,1}` *output* `tm` is bounded, but the digit counter `s2` (`popcount`) read off the same
automaton is **unbounded** — and it returns to its minimum value `1` at every power of two.  So
`s2` is *not eventually monotone*, hence cannot be a positive-finite-difference-depth sequence
(an integer sequence of finite Δ-depth is eventually a polynomial in `n`, so eventually monotone):
the automatic sequence's natural counter sits **outside the finite-depth generating ring**
(`FiniteDepthAlgebra` / `NewtonGregory`), even though its bounded readout `tm` is the dense
non-holonomic witness.  Two subtraction-free families pin both halves: `ones k` (`k` binary ones,
`s2 = k`) and `pw2 k` (`2^k`, `s2 = 1`). -/

/-- The number with `k` binary ones (`2^k - 1`), built without subtraction. -/
def ones : Nat → Nat
  | 0     => 0
  | (k+1) => 2 * ones k + 1

/-- The power of two `2^k`, built without `Nat.pow`. -/
def pw2 : Nat → Nat
  | 0     => 1
  | (k+1) => 2 * pw2 k

/-- `popcount(ones k) = k`: the `k`-ones number has digit-sum `k`. -/
theorem s2_ones (k : Nat) : s2 (ones k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show s2 (2 * ones k + 1) = k + 1
    rw [s2_odd, ih]

/-- `popcount(2^k) = 1`: a power of two has a single binary one. -/
theorem s2_pw2 (k : Nat) : s2 (pw2 k) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show s2 (2 * pw2 k) = 1
    rw [s2_even, ih]

/-- `ones` dominates its index (`k ≤ ones k`). -/
theorem ones_ge (k : Nat) : k ≤ ones k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    show k + 1 ≤ 2 * ones k + 1
    apply Nat.succ_le_succ
    exact Nat.le_trans ih (Nat.le_mul_of_pos_left (ones k) (by decide))

/-- `pw2` strictly dominates its index (`k < pw2 k`). -/
theorem pw2_gt (k : Nat) : k < pw2 k := by
  induction k with
  | zero => exact Nat.lt_succ_self 0
  | succ k ih =>
    show k + 1 < 2 * pw2 k
    have h1 : pw2 k + pw2 k = 2 * pw2 k := (E213.Tactic.NatHelper.two_mul (pw2 k)).symm
    have hpos : 1 ≤ pw2 k := Nat.le_trans (Nat.zero_lt_succ k) ih
    calc k + 1 ≤ pw2 k := ih
      _ < pw2 k + pw2 k := Nat.lt_add_of_pos_right hpos
      _ = 2 * pw2 k := h1

/-- **`popcount` is unbounded.**  For every bound `B`, `ones (B+1)` has digit-sum `B+1 > B`. -/
theorem s2_unbounded (B : Nat) : ∃ n, B < s2 n :=
  ⟨ones (B + 1), by rw [s2_ones]; exact Nat.lt_succ_self B⟩

/-- ★★★ **The digit counter is not eventually monotone.**  Past every threshold `N` there is a
    pair `m ≤ n` with `s2 n < s2 m`: take `m = ones (N+2)` (`s2 m = N+2`, and `m ≥ N`) and
    `n = pw2 m` (`s2 n = 1`, and `n > m`).  A finite-Δ-depth integer sequence is eventually
    monotone, so `s2` has **no** finite difference-depth — the automatic counter escapes the
    generating ring while its bounded readout `tm` is the dense non-holonomic witness. -/
theorem s2_not_eventually_monotone :
    ¬ ∃ N, ∀ m n, N ≤ m → m ≤ n → s2 m ≤ s2 n := by
  rintro ⟨N, hmono⟩
  have hNm : N ≤ ones (N + 2) := Nat.le_trans (Nat.le_add_right N 2) (ones_ge (N + 2))
  have hmn : ones (N + 2) ≤ pw2 (ones (N + 2)) := Nat.le_of_lt (pw2_gt (ones (N + 2)))
  have hle := hmono (ones (N + 2)) (pw2 (ones (N + 2))) hNm hmn
  rw [s2_ones, s2_pw2] at hle
  -- hle : N + 2 ≤ 1, but 2 ≤ N + 2
  exact absurd (Nat.le_trans (Nat.le_add_left 2 N) hle) (by decide)

/-! ## The two witnesses are one automaton: `isPow2 n = (s2 n == 1)`

The sparse witness `χ`/`isPow2` (powers of two) and the dense witness `tm` (Thue–Morse) are the
**same** `2`-automatic digit-sum `s2 = popcount`, read through different output functions:
`tm n = (s2 n % 2 == 1)` (`tm_eq_popParity`) and `isPow2 n = (s2 n == 1)` (`isPow2_eq_s2_one`,
since a power of two has exactly one binary `1`).  Both are digit-automatic; their differing
holonomic status (sparse `χ` escapes *both* machine classes, dense `tm` only the autonomous one)
is a property of the *output map*, not of automaticity. -/

/-- `popcount(2^j) = 1`. -/
theorem s2_two_pow (j : Nat) : s2 (2 ^ j) = 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2, s2_even, ih]

/-- `popcount n = 0 ⟹ n = 0`. -/
theorem s2_eq_zero_imp : ∀ n, s2 n = 0 → n = 0 := by
  suffices H : ∀ T n, n < T → s2 n = 0 → n = 0 by
    intro n; exact H (n + 1) n (Nat.lt_succ_self n)
  intro T
  induction T with
  | zero => intro n h _; exact absurd h (Nat.not_lt_zero n)
  | succ T ih =>
    intro n hnT hs
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · exact hn0
    · have hdm : 2 * (n / 2) + n % 2 = n := E213.Meta.Nat.AddMod213.div_add_mod n 2
      have hhalf : n / 2 < n :=
        E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul
          (by rw [E213.Tactic.NatHelper.two_mul]; exact Nat.lt_add_of_pos_left hnpos)
      have hh : n / 2 < T := Nat.lt_of_lt_of_le hhalf (Nat.le_of_lt_succ hnT)
      rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one n with he | ho
      · have e : 2 * (n / 2) = n := by rw [he, Nat.add_zero] at hdm; exact hdm
        have hs2 : s2 (n / 2) = 0 := by
          have hcong : s2 n = s2 (n / 2) := (congrArg s2 e.symm).trans (s2_even (n / 2))
          rw [← hcong]; exact hs
        have hz : n / 2 = 0 := ih (n / 2) hh hs2
        exact e.symm.trans (show 2 * (n / 2) = 0 by rw [hz, Nat.mul_zero])
      · have e : 2 * (n / 2) + 1 = n := by rw [ho] at hdm; exact hdm
        have hs2 : s2 n = s2 (n / 2) + 1 := (congrArg s2 e.symm).trans (s2_odd (n / 2))
        rw [hs2] at hs
        exact Nat.noConfusion hs

/-- `popcount n = 1 ⟹ n` is a power of two. -/
theorem s2_eq_one_imp : ∀ n, s2 n = 1 → ∃ j, 2 ^ j = n := by
  suffices H : ∀ T n, n < T → s2 n = 1 → ∃ j, 2 ^ j = n by
    intro n; exact H (n + 1) n (Nat.lt_succ_self n)
  intro T
  induction T with
  | zero => intro n h _; exact absurd h (Nat.not_lt_zero n)
  | succ T ih =>
    intro n hnT hs
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0] at hs; exact absurd hs (by decide)
    · have hdm : 2 * (n / 2) + n % 2 = n := E213.Meta.Nat.AddMod213.div_add_mod n 2
      have hhalf : n / 2 < n :=
        E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul
          (by rw [E213.Tactic.NatHelper.two_mul]; exact Nat.lt_add_of_pos_left hnpos)
      have hh : n / 2 < T := Nat.lt_of_lt_of_le hhalf (Nat.le_of_lt_succ hnT)
      rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one n with he | ho
      · have e : 2 * (n / 2) = n := by rw [he, Nat.add_zero] at hdm; exact hdm
        have hs2 : s2 (n / 2) = 1 := by
          have hcong : s2 n = s2 (n / 2) := (congrArg s2 e.symm).trans (s2_even (n / 2))
          rw [← hcong]; exact hs
        obtain ⟨j, hj⟩ := ih (n / 2) hh hs2
        refine ⟨j + 1, ?_⟩
        rw [Nat.pow_succ, Nat.mul_comm, hj]; exact e
      · have e : 2 * (n / 2) + 1 = n := by rw [ho] at hdm; exact hdm
        have hs2 : s2 n = s2 (n / 2) + 1 := (congrArg s2 e.symm).trans (s2_odd (n / 2))
        rw [hs2] at hs
        have hz : n / 2 = 0 := s2_eq_zero_imp (n / 2) (Nat.succ.inj hs)
        have hn1 : n = 1 := e.symm.trans (by rw [hz, Nat.mul_zero])
        exact ⟨0, by rw [Nat.pow_zero, hn1]⟩

/-- `isPow2 n = true ↔ n` is a power of two. -/
theorem isPow2_true_iff (n : Nat) : isPow2 n = true ↔ ∃ j, 2 ^ j = n := by
  constructor
  · intro h; exact pow2aux_true_imp n n h
  · rintro ⟨j, hj⟩
    show E213.Lib.Math.Cauchy.ZeroRunNonHolonomicWitness.pow2aux n n = true
    rw [← hj]; exact pow2aux_pow j (2 ^ j) (lt_two_pow j)

/-- `popcount n = 1 ↔ n` is a power of two. -/
theorem s2_eq_one_iff (n : Nat) : s2 n = 1 ↔ ∃ j, 2 ^ j = n := by
  constructor
  · exact s2_eq_one_imp n
  · rintro ⟨j, hj⟩; rw [← hj]; exact s2_two_pow j

/-- ★★★ **The sparse and dense witnesses are one automaton.**  `isPow2` (powers of two, the
    sparse `χ`) and `tm` (Thue–Morse, dense) are the same `2`-automatic digit-sum `s2` read
    through different output maps: `isPow2 n = (s2 n == 1)`, `tm n = (s2 n % 2 == 1)`.  The
    differing holonomic status is in the output function, not the automaticity. -/
theorem isPow2_eq_s2_one (n : Nat) : isPow2 n = decide (s2 n = 1) := by
  have hiff : isPow2 n = true ↔ s2 n = 1 :=
    (isPow2_true_iff n).trans (s2_eq_one_iff n).symm
  cases hp : isPow2 n with
  | true =>
    have h1 : s2 n = 1 := hiff.mp hp
    rw [h1]; rfl
  | false =>
    cases hd : decide (s2 n = 1) with
    | false => rfl
    | true =>
      have h1 : s2 n = 1 := of_decide_eq_true hd
      have hpt := hiff.mpr h1
      rw [hp] at hpt
      exact absurd hpt (by decide)

/-! ## Dyadic self-similarity: the second half is the complement

The structural heart of automaticity: on `[2^k, 2^{k+1})` Thue–Morse is the **bitwise complement**
of `[0, 2^k)`.  The extra high bit `2^k` is disjoint from `n < 2^k`, so it adds exactly one to the
digit-sum, flipping the parity: `tm(2^k + n) = ¬tm(n)`.  This is the self-similar fold that makes
the sequence a fixed point of the doubling substitution. -/

/-- `popcount(2^k + n) = popcount(n) + 1` for `n < 2^k` (the high bit is disjoint from `n`). -/
theorem s2_add_pow : ∀ k n, n < 2 ^ k → s2 (2 ^ k + n) = s2 n + 1 := by
  intro k
  induction k with
  | zero =>
    intro n hn
    cases n with
    | zero => rfl
    | succ m => exact absurd (Nat.le_of_lt_succ hn) (Nat.not_succ_le_zero m)
  | succ k ih =>
    intro n hn
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hq : n / 2 < 2 ^ k :=
      E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul (by rw [← h2]; exact hn)
    have hdm : 2 * (n / 2) + n % 2 = n := E213.Meta.Nat.AddMod213.div_add_mod n 2
    rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one n with he | ho
    · have en : 2 * (n / 2) = n := by rw [he, Nat.add_zero] at hdm; exact hdm
      have ekey : 2 * (2 ^ k + n / 2) = 2 ^ (k + 1) + n := by
        rw [Nat.mul_add, en, ← h2]
      have hsn : s2 n = s2 (n / 2) := (congrArg s2 en.symm).trans (s2_even (n / 2))
      rw [← ekey, s2_even, ih (n / 2) hq, hsn]
    · have en : 2 * (n / 2) + 1 = n := by rw [ho] at hdm; exact hdm
      have ekey : 2 * (2 ^ k + n / 2) + 1 = 2 ^ (k + 1) + n := by
        rw [Nat.mul_add, Nat.add_assoc, en, ← h2]
      have hsn : s2 n = s2 (n / 2) + 1 := (congrArg s2 en.symm).trans (s2_odd (n / 2))
      rw [← ekey, s2_odd, ih (n / 2) hq, hsn]

/-- ★★★ **Dyadic self-similarity / complement fold.**  On `[2^k, 2^{k+1})` Thue–Morse is the
    bitwise complement of `[0, 2^k)`: `tm(2^k + n) = ¬tm(n)` for `n < 2^k`.  The high bit flips the
    digit-sum parity (`s2_add_pow` + `succ_parity`). -/
theorem tm_shift_pow (k n : Nat) (h : n < 2 ^ k) : tm (2 ^ k + n) = !tm n := by
  rw [tm_eq_popParity (2 ^ k + n), tm_eq_popParity n, s2_add_pow k n h, succ_parity]

/-! ## A concrete bounded aperiodic continued fraction

The dense witness, realised as an actual **continued fraction**.  Mapping the `{0,1}` output to
`{1,2}` (a valid partial quotient is `≥ 1`) gives `tmCF`, the partial-quotient sequence of a real
number whose continued fraction is **bounded** (`1 ≤ aₙ ≤ 2`), **dense** (run-length `≤ 2`,
`tm_run_le_two`), **aperiodic** (`tm_not_evPeriodic`), and generated by **no** autonomous
finite-state machine (`tmCF_not_autoRec`).  This is the marathon's subject — a continued fraction
on the dense non-holonomic axis — made concrete (the *autonomous* escape; its `HomogRec` status,
like π's, is the open core). -/

/-- A constant shift cannot create or destroy an autonomous finite-state machine: if `a + c` is
    `AutoRec`, so is `a` (compose the window-rule with the shift). -/
theorem autoRec_shift {a : Nat → Int} {c : Int}
    (h : AutoRec (fun n => a n + c)) : AutoRec a := by
  obtain ⟨k, F, hdep, hrec⟩ := h
  refine ⟨k, fun w => F (fun i => w i + c) - c, ?_, ?_⟩
  · intro w w' hww'
    have hF : F (fun i => w i + c) = F (fun i => w' i + c) :=
      hdep _ _ (fun i hi => by rw [hww' i hi])
    show F (fun i => w i + c) - c = F (fun i => w' i + c) - c
    rw [hF]
  · intro n
    show a (n + k) = F (fun i => a (n + i) + c) - c
    have hr : a (n + k) + c = F (fun i => a (n + i) + c) := hrec n
    rw [← hr, Int.sub_eq_add_neg, E213.Meta.Int213.add_assoc,
      E213.Meta.Int213.add_neg_cancel, Int.add_zero]

/-- The `{1,2}`-valued Thue–Morse partial-quotient sequence. -/
def tmCF (n : Nat) : Int := ((b2n (tm n) : Nat) : Int) + 1

/-- `tmCF` is a valid bounded partial quotient: `tmCF n ∈ {1, 2}`. -/
theorem tmCF_mem (n : Nat) : tmCF n = 1 ∨ tmCF n = 2 := by
  show ((b2n (tm n) : Nat) : Int) + 1 = 1 ∨ ((b2n (tm n) : Nat) : Int) + 1 = 2
  cases tm n <;> decide

/-- Every partial quotient is `≥ 1` — a genuine continued fraction. -/
theorem tmCF_ge_one (n : Nat) : (1 : Int) ≤ tmCF n := by
  rcases tmCF_mem n with h | h <;> rw [h] <;> decide

/-- ★★★ **The Thue–Morse continued fraction escapes every autonomous finite-state machine.**  A
    concrete real number whose continued fraction is bounded (`1 ≤ aₙ ≤ 2`), dense (no long runs),
    aperiodic, and generated by no `AutoRec` — the dense non-holonomic witness as an actual CF. -/
theorem tmCF_not_autoRec : ¬ AutoRec tmCF := by
  intro h
  have h' : AutoRec (fun n => ((b2n (tm n) : Nat) : Int) + 1) := h
  exact tm_morse_not_autoRec (autoRec_shift h')

end E213.Lib.Math.Cauchy.ThueMorseAperiodic
