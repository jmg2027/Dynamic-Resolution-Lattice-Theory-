import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.DyadicFSM.ConcretePellSig

import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.Signature
/-!
# Fibonacci ArithFSM mod 5 — period 20 (RAMIFIED case)

5 mod 5 = 0, RAMIFIED.  Pisano formula: π(p) = 4p = 20.  TIGHT.

Notable: at the ramified prime p=5 (= Δ), the Fibonacci period is
4·5 = 20, much larger than the inert/split formulas would give.
This reflects the special degeneracy of the discriminant at ramification.
-/

namespace E213.Lib.Math.DyadicFSM.Fib.FSMmod5

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Fibonacci-style FSM mod 5. -/
def fibFSMmod5 : ArithFSM2 5 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 5, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Fibonacci mod-5 run cycles with TIGHT period 20. -/
theorem fibFSMmod5_run_period_20 :
    ∀ k, fibFSMmod5.run (k + 20) = fibFSMmod5.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show fibFSMmod5.step (fibFSMmod5.run (k' + 20))
        = fibFSMmod5.step (fibFSMmod5.run k')
    rw [ih]

/-- ★★★★ Fibonacci mod-5 bits cycle with TIGHT period 20. -/
theorem fibFSMmod5_bits_period_20 :
    ∀ k, fibFSMmod5.bits (k + 20) = fibFSMmod5.bits k := by
  intro k
  show fibFSMmod5.out (fibFSMmod5.run (k + 20))
      = fibFSMmod5.out (fibFSMmod5.run k)
  rw [fibFSMmod5_run_period_20]

/-- ★★★★★ Fibonacci mod-5 signature has period 20 from step 1. -/
theorem fibFSMmod5_signature_period_20_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod5.bits (k + 20)
        = signature fibFSMmod5.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod5.bits 20 1 fibFSMmod5_bits_period_20 (by decide)

end E213.Lib.Math.DyadicFSM.Fib.FSMmod5
