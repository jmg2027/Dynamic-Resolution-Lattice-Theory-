import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.DyadicFSM.ConcretePellSig

import E213.Lib.Math.DyadicFSM.Signature.Signature
/-!
# ArithFSM3 — 3-state arithmetic FSM (cubic / Tribonacci class)

Generalisation of ArithFSM2 to 3-component state vectors.
Captures Tribonacci-style recurrences a_{k+1} = a + b + c
that arise from cubic irrationals (plastic ratio etc.).

Joint state space: Fin n × Fin n × Fin n with n³ values.
-/

namespace E213.Lib.Math.DyadicFSM.ArithFSM.V3

open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


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

end E213.Lib.Math.DyadicFSM.ArithFSM.V3

namespace E213.Lib.Math.DyadicFSM.ArithFSM

open E213.Lib.Math.DyadicFSM.ArithFSM.V3 (ArithFSM3)

/-- Pad ArithFSM₂(n) into ArithFSM₃(n) by adding an inert third
    component.  init = (a, b, 0), step ignores it.

    Defined at the `ArithFSM2` namespace (which is
    `E213.Lib.Math.DyadicFSM.ArithFSM.ArithFSM2`) so that dot
    notation `m.padTo3 hn` resolves correctly. -/
def ArithFSM2.padTo3 {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) : ArithFSM3 n where
  init := (m.init.1, m.init.2, ⟨0, hn⟩)
  step p := let (a, b, _) := p
    (m.step (a, b)).1 |> fun a' =>
      (a', (m.step (a, b)).2, ⟨0, hn⟩)
  out p := m.out (p.1, p.2.1)

/-- ★★★ padTo3 preserves the run's first-second components. -/
theorem padTo3_run_components {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) (k : Nat) :
    ((m.padTo3 hn).run k).1 = (m.run k).1
    ∧ ((m.padTo3 hn).run k).2.1 = (m.run k).2 := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k' ih =>
      have h1 : ((m.padTo3 hn).run k').1 = (m.run k').1 := ih.1
      have h2 : ((m.padTo3 hn).run k').2.1 = (m.run k').2 := ih.2
      show ((m.padTo3 hn).step ((m.padTo3 hn).run k')).1 = (m.step (m.run k')).1
        ∧ ((m.padTo3 hn).step ((m.padTo3 hn).run k')).2.1 = (m.step (m.run k')).2
      let p := (m.padTo3 hn).run k'
      have hp1 : p.1 = (m.run k').1 := h1
      have hp2 : p.2.1 = (m.run k').2 := h2
      refine ⟨?_, ?_⟩
      · show (m.step (p.1, p.2.1)).1 = (m.step (m.run k')).1
        rw [hp1, hp2]
      · show (m.step (p.1, p.2.1)).2 = (m.step (m.run k')).2
        rw [hp1, hp2]

/-- ★★★★ padTo3 preserves the bit stream. -/
theorem padTo3_bits_eq {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) (k : Nat) :
    (m.padTo3 hn).bits k = m.bits k := by
  show m.out (((m.padTo3 hn).run k).1, ((m.padTo3 hn).run k).2.1)
     = m.out (m.run k)
  have ⟨h1, h2⟩ := padTo3_run_components hn m k
  rw [h1, h2]

end E213.Lib.Math.DyadicFSM.ArithFSM
