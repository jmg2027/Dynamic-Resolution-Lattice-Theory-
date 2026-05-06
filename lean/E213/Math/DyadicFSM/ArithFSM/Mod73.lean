import E213.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Math.DyadicFSM.ConcretePellSig

import E213.Math.DyadicFSM.ArithFSM
/-!
# Pell ArithFSM mod 73 — period 74 (INERT, TIGHT)

73 mod 5 = 3, NQR ⇒ INERT. Predict p+1 = 74. TIGHT.
-/

namespace E213.Math.DyadicFSM.ArithFSM.Mod73

open E213.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)

open E213.Math.DyadicFSM.ArithFSM (ArithFSM2)


def pellFSMmod73 : ArithFSM2 73 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 73, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 73, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 2048 in
theorem pellFSMmod73_run_period_74 :
    ∀ k, pellFSMmod73.run (k + 74) = pellFSMmod73.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod73.step (pellFSMmod73.run (k' + 74))
        = pellFSMmod73.step (pellFSMmod73.run k')
    rw [ih]

theorem pellFSMmod73_bits_period_74 :
    ∀ k, pellFSMmod73.bits (k + 74) = pellFSMmod73.bits k := by
  intro k
  show pellFSMmod73.out (pellFSMmod73.run (k + 74))
      = pellFSMmod73.out (pellFSMmod73.run k)
  rw [pellFSMmod73_run_period_74]

end E213.Math.DyadicFSM.ArithFSM.Mod73
