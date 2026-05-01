import E213.Math.Cohomology.Dyadic.ArithFSMtoBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# ArithFSM3 — 3-state arithmetic FSM (cubic / Tribonacci class)

Generalisation of ArithFSM2 to 3-component state vectors.
Captures Tribonacci-style recurrences a_{k+1} = a + b + c
that arise from cubic irrationals (plastic ratio etc.).

Joint state space: Fin n × Fin n × Fin n with n³ values.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- 3-state arithmetic FSM.  State vector in (Fin n)³. -/
structure ArithFSM3 (n : Nat) where
  init : Fin n × Fin n × Fin n
  step : Fin n × Fin n × Fin n → Fin n × Fin n × Fin n
  out  : Fin n × Fin n × Fin n → Bool

/-- Run for k steps. -/
def ArithFSM3.run {n : Nat} (m : ArithFSM3 n) : Nat → Fin n × Fin n × Fin n
  | 0 => m.init
  | k + 1 => m.step (m.run k)

/-- Bit stream from arithmetic FSM. -/
def ArithFSM3.bits {n : Nat} (m : ArithFSM3 n) (k : Nat) : Bool :=
  m.out (m.run k)

/-- Tribonacci shift mod 2: state (a, b, c) → (b, c, a + b + c).
    Out: parity of a. -/
def tribFSMmod2 : ArithFSM3 2 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b, c) := p
    (b, c, ⟨(a.val + b.val + c.val) % 2, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Tribonacci mod-2 first values: 0,1,1,0,0,1,1,0,0,1,1,0 (period 4). -/
theorem tribFSMmod2_first10 :
    tribFSMmod2.bits 0 = false ∧ tribFSMmod2.bits 1 = true
    ∧ tribFSMmod2.bits 2 = true ∧ tribFSMmod2.bits 3 = false
    ∧ tribFSMmod2.bits 4 = false ∧ tribFSMmod2.bits 5 = true
    ∧ tribFSMmod2.bits 6 = true ∧ tribFSMmod2.bits 7 = false
    ∧ tribFSMmod2.bits 8 = false ∧ tribFSMmod2.bits 9 = true := by decide

/-- ★★★ Tribonacci mod-2 run cycles with period 4 (universally). -/
theorem tribFSMmod2_run_period_4 :
    ∀ k, tribFSMmod2.run (k + 4) = tribFSMmod2.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show tribFSMmod2.step (tribFSMmod2.run (k' + 4))
        = tribFSMmod2.step (tribFSMmod2.run k')
    rw [ih]

/-- ★★★★ Tribonacci mod-2 bits cycle with period 4. -/
theorem tribFSMmod2_bits_period_4 :
    ∀ k, tribFSMmod2.bits (k + 4) = tribFSMmod2.bits k := by
  intro k
  show tribFSMmod2.out (tribFSMmod2.run (k + 4))
      = tribFSMmod2.out (tribFSMmod2.run k)
  rw [tribFSMmod2_run_period_4]

/-- ★★★★★ Tribonacci mod-2 signature has period 4 from step 1
    (TIGHT; pre-period 1).  -/
theorem tribFSMmod2_signature_period_4_from_1 :
    ∀ k, k ≥ 1 →
      signature tribFSMmod2.bits (k + 4) = signature tribFSMmod2.bits k :=
  signature_period_of_bits_period_and_anchor_from
    tribFSMmod2.bits 4 1 tribFSMmod2_bits_period_4 (by decide)

end E213.Math.Cohomology.Dyadic.Conjecture
