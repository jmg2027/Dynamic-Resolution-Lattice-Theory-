import E213.Math.Cohomology.Dyadic.ArithFSMtoBitFSM
import E213.Math.Cohomology.DyadicConcretePellSig

/-!
# Fibonacci ArithFSM mod 23 — period 48 (INERT, fifth instance)

23 mod 5 = 3.  (3/5) = -1, NQR, INERT.
Fibonacci predict: 2(p+1) = 48.  TIGHT.
-/

namespace E213.Math.Cohomology.DyadicConjecture

def fibFSMmod23 : ArithFSM2 23 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 23, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 2048 in
theorem fibFSMmod23_run_period_48 :
    ∀ k, fibFSMmod23.run (k + 48) = fibFSMmod23.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show fibFSMmod23.step (fibFSMmod23.run (k' + 48))
        = fibFSMmod23.step (fibFSMmod23.run k')
    rw [ih]

theorem fibFSMmod23_bits_period_48 :
    ∀ k, fibFSMmod23.bits (k + 48) = fibFSMmod23.bits k := by
  intro k
  show fibFSMmod23.out (fibFSMmod23.run (k + 48))
      = fibFSMmod23.out (fibFSMmod23.run k)
  rw [fibFSMmod23_run_period_48]

set_option maxRecDepth 2048 in
theorem fibFSMmod23_signature_period_48_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod23.bits (k + 48) = signature fibFSMmod23.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod23.bits 48 1 fibFSMmod23_bits_period_48 (by decide)

end E213.Math.Cohomology.DyadicConjecture
