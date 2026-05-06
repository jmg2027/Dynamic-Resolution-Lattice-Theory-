import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.DyadicFSM.ConcretePellSig

import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.Signature
/-!
# Fibonacci ArithFSM mod 11 — period 10 (SPLIT, first instance)

11 mod 5 = 1.  (1/5) = 1, QR, SPLIT.
Predict: p-1 = 10.  TIGHT.

First SPLIT instance for Fibonacci.  Bit period 10 (even) ⇒
signature period 10 (no doubling, even bit period).
-/

namespace E213.Lib.Math.DyadicFSM.Fib.FSMmod11

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Fibonacci-style FSM mod 11. -/
def fibFSMmod11 : ArithFSM2 11 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 11, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Fibonacci mod-11 run cycles with TIGHT period 10. -/
theorem fibFSMmod11_run_period_10 :
    ∀ k, fibFSMmod11.run (k + 10) = fibFSMmod11.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show fibFSMmod11.step (fibFSMmod11.run (k' + 10))
        = fibFSMmod11.step (fibFSMmod11.run k')
    rw [ih]

/-- ★★★★ Fibonacci mod-11 bits cycle with TIGHT period 10. -/
theorem fibFSMmod11_bits_period_10 :
    ∀ k, fibFSMmod11.bits (k + 10) = fibFSMmod11.bits k := by
  intro k
  show fibFSMmod11.out (fibFSMmod11.run (k + 10))
      = fibFSMmod11.out (fibFSMmod11.run k)
  rw [fibFSMmod11_run_period_10]

/-- ★★★★★ Fibonacci mod-11 signature has period 10 from step 1. -/
theorem fibFSMmod11_signature_period_10_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod11.bits (k + 10)
        = signature fibFSMmod11.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod11.bits 10 1 fibFSMmod11_bits_period_10 (by decide)

end E213.Lib.Math.DyadicFSM.Fib.FSMmod11
