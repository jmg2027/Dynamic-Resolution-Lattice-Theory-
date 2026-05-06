import E213.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Math.DyadicFSM.ConcretePellSig

import E213.Math.DyadicFSM.ArithFSM
import E213.Math.DyadicFSM.Signature
/-!
# Fibonacci ArithFSM mod 13 — period 28 (INERT, third instance)

13 mod 5 = 3.  (3/5) = -1, NQR, INERT.
Fibonacci predict: 2(p+1) = 28.  TIGHT.
-/

namespace E213.Math.DyadicFSM.Fib.FSMmod13

open E213.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Math.DyadicFSM.Signature (signature)
open E213.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


def fibFSMmod13 : ArithFSM2 13 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 13, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

theorem fibFSMmod13_run_period_28 :
    ∀ k, fibFSMmod13.run (k + 28) = fibFSMmod13.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show fibFSMmod13.step (fibFSMmod13.run (k' + 28))
        = fibFSMmod13.step (fibFSMmod13.run k')
    rw [ih]

theorem fibFSMmod13_bits_period_28 :
    ∀ k, fibFSMmod13.bits (k + 28) = fibFSMmod13.bits k := by
  intro k
  show fibFSMmod13.out (fibFSMmod13.run (k + 28))
      = fibFSMmod13.out (fibFSMmod13.run k)
  rw [fibFSMmod13_run_period_28]

set_option maxRecDepth 1024 in
theorem fibFSMmod13_signature_period_28_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod13.bits (k + 28) = signature fibFSMmod13.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod13.bits 28 1 fibFSMmod13_bits_period_28 (by decide)

end E213.Math.DyadicFSM.Fib.FSMmod13
