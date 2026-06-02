import E213.Lib.Math.Cauchy.MorseHedlund
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

end E213.Lib.Math.Cauchy.ThueMorseAperiodic
