import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Fibonacci ArithFSM mod 17 — period 36 (INERT, fourth instance)

17 mod 5 = 2.  (2/5) = -1, NQR, INERT.
Fibonacci predict: 2(p+1) = 36.  TIGHT.
-/

namespace E213.Math.Cohomology.Dyadic.Fib.FSMmod17

open E213.Math.Cohomology.Dyadic.ArithFSM (ArithFSM2)
open E213.Math.Cohomology.Dyadic.Signature (signature)


def fibFSMmod17 : ArithFSM2 17 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 17, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 1024 in
theorem fibFSMmod17_run_period_36 :
    ∀ k, fibFSMmod17.run (k + 36) = fibFSMmod17.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show fibFSMmod17.step (fibFSMmod17.run (k' + 36))
        = fibFSMmod17.step (fibFSMmod17.run k')
    rw [ih]

theorem fibFSMmod17_bits_period_36 :
    ∀ k, fibFSMmod17.bits (k + 36) = fibFSMmod17.bits k := by
  intro k
  show fibFSMmod17.out (fibFSMmod17.run (k + 36))
      = fibFSMmod17.out (fibFSMmod17.run k)
  rw [fibFSMmod17_run_period_36]

set_option maxRecDepth 2048 in
theorem fibFSMmod17_signature_period_36_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod17.bits (k + 36) = signature fibFSMmod17.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod17.bits 36 1 fibFSMmod17_bits_period_36 (by decide)

end E213.Math.Cohomology.Dyadic.Fib.FSMmod17
