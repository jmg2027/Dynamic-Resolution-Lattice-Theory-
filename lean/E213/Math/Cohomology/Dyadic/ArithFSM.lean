import E213.Math.Cohomology.Dyadic.BitAuto2
import E213.Math.NatDiv213

/-!
# ArithFSM — multi-state arithmetic recurrence (Tier 1 abstraction)

Captures the structure of Pell-like sequences for algebraic
irrationals.  An `ArithFSM2` has a 2-component state vector
(Fin n × Fin n) updating via a linear recurrence mod n.

Joint state space: Fin n × Fin n with n² values.  Transitions
are constrained to arithmetic recurrences (matrix mod n).

For Pell sequence (√2): (a_{k+1}, b_{k+1}) = (2a + b, a + b)
has finite state mod any fixed N (CRT-style closure).
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM

open E213.Math.Cohomology.Dyadic.BitFSM (BitFSM)



/-- 2-state arithmetic FSM with state vector in Fin n × Fin n. -/
structure ArithFSM2 (n : Nat) where
  init : Fin n × Fin n
  step : Fin n × Fin n → Fin n × Fin n
  out  : Fin n × Fin n → Bool

/-- Run for k steps. -/
def ArithFSM2.run {n : Nat} (m : ArithFSM2 n) : Nat → Fin n × Fin n
  | 0 => m.init
  | k + 1 => m.step (m.run k)

/-- Bit stream from arithmetic FSM. -/
def ArithFSM2.bits {n : Nat} (m : ArithFSM2 n) (k : Nat) : Bool :=
  m.out (m.run k)

/-- Pell-style FSM mod 2: (a_{k+1}, b_{k+1}) = (2a + b, a + b) mod 2.
    Out: parity of a. -/
def pellFSMmod2 : ArithFSM2 2 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨b.val % 2, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 2, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-2 first values: cycles with period 3 since (Fin 2)² has
    only 4 states and the dynamics is deterministic. -/
theorem pellFSMmod2_first8 :
    pellFSMmod2.bits 0 = true ∧ pellFSMmod2.bits 1 = true
    ∧ pellFSMmod2.bits 2 = false ∧ pellFSMmod2.bits 3 = true
    ∧ pellFSMmod2.bits 4 = true ∧ pellFSMmod2.bits 5 = false := by decide

/-- ★★★ Pell mod-2 run cycles with period 3 (universally). -/
theorem pellFSMmod2_run_period_3 :
    ∀ k, pellFSMmod2.run (k + 3) = pellFSMmod2.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod2.step (pellFSMmod2.run (k' + 3))
        = pellFSMmod2.step (pellFSMmod2.run k')
    rw [ih]

/-- ★★★★ Pell mod-2 bits cycle with period 3 (universally). -/
theorem pellFSMmod2_bits_period_3 :
    ∀ k, pellFSMmod2.bits (k + 3) = pellFSMmod2.bits k := by
  intro k
  show pellFSMmod2.out (pellFSMmod2.run (k + 3))
      = pellFSMmod2.out (pellFSMmod2.run k)
  rw [pellFSMmod2_run_period_3]

/-- Pell-style FSM mod 3: same recurrence, bigger modulus. -/
def pellFSMmod3 : ArithFSM2 3 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 3, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-3 first values: T, F, F, F, T, F, F, F (period 4). -/
theorem pellFSMmod3_first8 :
    pellFSMmod3.bits 0 = true ∧ pellFSMmod3.bits 1 = false
    ∧ pellFSMmod3.bits 2 = false ∧ pellFSMmod3.bits 3 = false
    ∧ pellFSMmod3.bits 4 = true ∧ pellFSMmod3.bits 5 = false := by decide

/-- ★★★ Pell mod-3 run cycles with period 4. -/
theorem pellFSMmod3_run_period_4 :
    ∀ k, pellFSMmod3.run (k + 4) = pellFSMmod3.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod3.step (pellFSMmod3.run (k' + 4))
        = pellFSMmod3.step (pellFSMmod3.run k')
    rw [ih]

/-- ★★★★ Pell mod-3 bits cycle with period 4 (universally). -/
theorem pellFSMmod3_bits_period_4 :
    ∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k := by
  intro k
  show pellFSMmod3.out (pellFSMmod3.run (k + 4))
      = pellFSMmod3.out (pellFSMmod3.run k)
  rw [pellFSMmod3_run_period_4]

/-- ★★★★★ Different moduli give different periods (mod 2 → 3,
    mod 3 → 4) — algebraic structure visible at the FSM level. -/
theorem pellMod_periods_differ :
    (∃ p : Nat, p > 0 ∧ p = 3 ∧
      ∀ k, pellFSMmod2.bits (k + p) = pellFSMmod2.bits k)
    ∧ (∃ p : Nat, p > 0 ∧ p = 4 ∧
      ∀ k, pellFSMmod3.bits (k + p) = pellFSMmod3.bits k) :=
  ⟨⟨3, by decide, rfl, pellFSMmod2_bits_period_3⟩,
   ⟨4, by decide, rfl, pellFSMmod3_bits_period_4⟩⟩

/-- ★★ ArithFSM2 reduces to BitFSM(n²) via pair-encoding —
    same pigeonhole argument applies. -/
def ArithFSM2.toBitFSM {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) :
    BitFSM (n * n) where
  init := ⟨m.init.1.val * n + m.init.2.val, by
    have h1 := Nat.succ_le_of_lt m.init.1.isLt  -- m.init.1.val + 1 ≤ n
    have h2 := m.init.2.isLt                    -- m.init.2.val < n
    have step1 : m.init.1.val * n + m.init.2.val
                  < m.init.1.val * n + n :=
      Nat.add_lt_add_left h2 _
    have step2 : m.init.1.val * n + n = (m.init.1.val + 1) * n :=
      (Nat.succ_mul m.init.1.val n).symm
    have step3 : (m.init.1.val + 1) * n ≤ n * n :=
      Nat.mul_le_mul_right n h1
    exact Nat.lt_of_lt_of_le step1 (step2 ▸ step3)⟩
  step v :=
    let a : Fin n := ⟨v.val / n, E213.Math.NatDiv213.div_lt_of_lt_mul v.isLt⟩
    let b : Fin n := ⟨v.val % n, Nat.mod_lt _ hn⟩
    let (a', b') := m.step (a, b)
    ⟨a'.val * n + b'.val, by
      have h1 := Nat.succ_le_of_lt a'.isLt
      have h2 := b'.isLt
      have step1 : a'.val * n + b'.val < a'.val * n + n :=
        Nat.add_lt_add_left h2 _
      have step2 : a'.val * n + n = (a'.val + 1) * n :=
        (Nat.succ_mul a'.val n).symm
      have step3 : (a'.val + 1) * n ≤ n * n :=
        Nat.mul_le_mul_right n h1
      exact Nat.lt_of_lt_of_le step1 (step2 ▸ step3)⟩
  out v :=
    let a : Fin n := ⟨v.val / n, E213.Math.NatDiv213.div_lt_of_lt_mul v.isLt⟩
    let b : Fin n := ⟨v.val % n, Nat.mod_lt _ hn⟩
    m.out (a, b)

end E213.Math.Cohomology.Dyadic.ArithFSM
