import E213.Math.Cohomology.Dyadic.ArithFSMtoBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Fibonacci ArithFSM mod 19 — period 18 (SPLIT, second instance)

19 mod 5 = 4 = (±2)², QR.  So (5/19) = 1, SPLIT.
Fibonacci predict: p-1 = 18.  TIGHT.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

def fibFSMmod19 : ArithFSM2 19 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 19, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

theorem fibFSMmod19_run_period_18 :
    ∀ k, fibFSMmod19.run (k + 18) = fibFSMmod19.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show fibFSMmod19.step (fibFSMmod19.run (k' + 18))
        = fibFSMmod19.step (fibFSMmod19.run k')
    rw [ih]

theorem fibFSMmod19_bits_period_18 :
    ∀ k, fibFSMmod19.bits (k + 18) = fibFSMmod19.bits k := by
  intro k
  show fibFSMmod19.out (fibFSMmod19.run (k + 18))
      = fibFSMmod19.out (fibFSMmod19.run k)
  rw [fibFSMmod19_run_period_18]

theorem fibFSMmod19_signature_period_18_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod19.bits (k + 18) = signature fibFSMmod19.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod19.bits 18 1 fibFSMmod19_bits_period_18 (by decide)

end E213.Math.Cohomology.Dyadic.Conjecture
