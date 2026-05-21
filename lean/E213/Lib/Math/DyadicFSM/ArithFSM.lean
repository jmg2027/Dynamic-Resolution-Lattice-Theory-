import E213.Lib.Math.DyadicFSM.BitAuto2
import E213.Meta.Nat.NatDiv213
import E213.Lib.Math.DyadicFSM.BitFSM

/-!
# ArithFSM — multi-state arithmetic recurrence (Tier 1 abstraction)

Note: per-prime instance files (`ArithFSM/Mod{Small, Medium, Large}.
lean`) IMPORT this file, so they cannot be imported here without
creating a build cycle.  They are pulled in by the parent
`DyadicFSM.lean` aggregator instead.

Captures the structure of Pell-like sequences for algebraic
irrationals.  An `ArithFSM2` has a 2-component state vector
(Fin n × Fin n) updating via a linear recurrence mod n.

Joint state space: Fin n × Fin n with n² values.  Transitions
are constrained to arithmetic recurrences (matrix mod n).

For Pell sequence (√2): (a_{k+1}, b_{k+1}) = (2a + b, a + b)
has finite state mod any fixed N (CRT-style closure).
-/

namespace E213.Lib.Math.DyadicFSM.ArithFSM

open E213.Lib.Math.DyadicFSM.BitFSM (BitFSM)



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

/-- **bits-period from run-period** — `bits = out ∘ run` by def, so any
    period of `run` transfers to `bits`.  G107 §4 Pell-FSM helper —
    absorbs the duplicated `show m.out (m.run _) = m.out (m.run _); rw [...]`
    closer in every per-modulus instance.  PURE. -/
theorem ArithFSM2.bits_period_of_run_period
    {n T : Nat} (m : ArithFSM2 n)
    (h : ∀ k, m.run (k + T) = m.run k) :
    ∀ k, m.bits (k + T) = m.bits k := fun k => by
  show m.out (m.run (k + T)) = m.out (m.run k)
  rw [h]

/-- **Period multiplication**: if `f` has period `T`, then `f` has
    period `n * T` for any `n`.  Generic — applies to any
    `f : Nat → Bool`, not just ArithFSM2 bits.  G107 §4 Pell-FSM
    helper for `_period_2T` / `_period_3T` doubled and tripled variants.
    PURE. -/
theorem bits_period_mul_of_period
    (f : Nat → Bool) {T : Nat}
    (h : ∀ k, f (k + T) = f k) :
    ∀ n k, f (k + n * T) = f k := by
  intro n
  induction n with
  | zero => intro k; rw [Nat.zero_mul, Nat.add_zero]
  | succ m ih =>
      intro k
      show f (k + (m + 1) * T) = f k
      have hreshape : k + (m + 1) * T = (k + m * T) + T := by
        rw [Nat.succ_mul, ← Nat.add_assoc]
      rw [hreshape, h, ih]

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
    ∀ k, pellFSMmod2.bits (k + 3) = pellFSMmod2.bits k :=
  ArithFSM2.bits_period_of_run_period _ pellFSMmod2_run_period_3

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
    ∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k :=
  ArithFSM2.bits_period_of_run_period _ pellFSMmod3_run_period_4

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
    let a : Fin n := ⟨v.val / n, E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul v.isLt⟩
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
    let a : Fin n := ⟨v.val / n, E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul v.isLt⟩
    let b : Fin n := ⟨v.val % n, Nat.mod_lt _ hn⟩
    m.out (a, b)

end E213.Lib.Math.DyadicFSM.ArithFSM
