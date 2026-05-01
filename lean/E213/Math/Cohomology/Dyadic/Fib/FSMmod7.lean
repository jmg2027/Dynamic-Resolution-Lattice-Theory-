import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Fibonacci ArithFSM mod 7 — period 16 (INERT, second instance)

7 mod 5 = 2.  (2/5) = -1, NQR, INERT.
Predict: 2(p+1) = 16.  TIGHT.

Second INERT instance for Fibonacci (after p=3, π=8), confirming
the 2(p+1) Fibonacci-Pisano formula at a larger size.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- Fibonacci-style FSM mod 7. -/
def fibFSMmod7 : ArithFSM2 7 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 7, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Fibonacci mod-7 run cycles with TIGHT period 16. -/
theorem fibFSMmod7_run_period_16 :
    ∀ k, fibFSMmod7.run (k + 16) = fibFSMmod7.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show fibFSMmod7.step (fibFSMmod7.run (k' + 16))
        = fibFSMmod7.step (fibFSMmod7.run k')
    rw [ih]

/-- ★★★★ Fibonacci mod-7 bits cycle with TIGHT period 16. -/
theorem fibFSMmod7_bits_period_16 :
    ∀ k, fibFSMmod7.bits (k + 16) = fibFSMmod7.bits k := by
  intro k
  show fibFSMmod7.out (fibFSMmod7.run (k + 16))
      = fibFSMmod7.out (fibFSMmod7.run k)
  rw [fibFSMmod7_run_period_16]

/-- ★★★★★ Fibonacci mod-7 signature has period 16 from step 1. -/
theorem fibFSMmod7_signature_period_16_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod7.bits (k + 16)
        = signature fibFSMmod7.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod7.bits 16 1 fibFSMmod7_bits_period_16 (by decide)

end E213.Math.Cohomology.Dyadic.Conjecture
