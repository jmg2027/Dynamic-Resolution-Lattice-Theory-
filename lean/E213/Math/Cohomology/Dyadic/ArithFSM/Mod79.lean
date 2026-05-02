import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 79 — period 39 (SPLIT, TIGHT)

79 mod 5 = 4, QR ⇒ SPLIT. Predict (p-1)/2 = 39. TIGHT.
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Mod79

open E213.Math.Cohomology.Dyadic.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)

open E213.Math.Cohomology.Dyadic.ArithFSM (ArithFSM2)


def pellFSMmod79 : ArithFSM2 79 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 79, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 79, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 1024 in
theorem pellFSMmod79_run_period_39 :
    ∀ k, pellFSMmod79.run (k + 39) = pellFSMmod79.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod79.step (pellFSMmod79.run (k' + 39))
        = pellFSMmod79.step (pellFSMmod79.run k')
    rw [ih]

theorem pellFSMmod79_bits_period_39 :
    ∀ k, pellFSMmod79.bits (k + 39) = pellFSMmod79.bits k := by
  intro k
  show pellFSMmod79.out (pellFSMmod79.run (k + 39))
      = pellFSMmod79.out (pellFSMmod79.run k)
  rw [pellFSMmod79_run_period_39]

end E213.Math.Cohomology.Dyadic.ArithFSM.Mod79
