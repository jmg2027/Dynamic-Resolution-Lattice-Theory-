import E213.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Math.DyadicFSM.ConcretePellSig

import E213.Math.DyadicFSM.ArithFSM
import E213.Math.DyadicFSM.Signature
/-!
# Pell ArithFSM mod 61 — period 30 (SPLIT, TIGHT)

61 mod 5 = 1.  (1/5) = 1, QR.  So (5/61) = 1, SPLIT.
Predict (p-1)/2 = 30, TIGHT (matches exactly).

Bit period 30 (even) ⇒ signature period 30 (no doubling).
-/

namespace E213.Math.DyadicFSM.ArithFSM.Mod61

open E213.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Math.DyadicFSM.Signature (signature)
open E213.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 61. -/
def pellFSMmod61 : ArithFSM2 61 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 61, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 61, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-61 run cycles with TIGHT period 30. -/
theorem pellFSMmod61_run_period_30 :
    ∀ k, pellFSMmod61.run (k + 30) = pellFSMmod61.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod61.step (pellFSMmod61.run (k' + 30))
        = pellFSMmod61.step (pellFSMmod61.run k')
    rw [ih]

/-- ★★★★ Pell mod-61 bits cycle with TIGHT period 30. -/
theorem pellFSMmod61_bits_period_30 :
    ∀ k, pellFSMmod61.bits (k + 30) = pellFSMmod61.bits k := by
  intro k
  show pellFSMmod61.out (pellFSMmod61.run (k + 30))
      = pellFSMmod61.out (pellFSMmod61.run k)
  rw [pellFSMmod61_run_period_30]

set_option maxRecDepth 2048 in
/-- ★★★★★ Pell mod-61 signature has period 30 (TIGHT, even). -/
theorem pellFSMmod61_signature_period_30 :
    ∀ k, signature pellFSMmod61.bits (k + 30)
        = signature pellFSMmod61.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod61.bits 30
    pellFSMmod61_bits_period_30 (by decide)

end E213.Math.DyadicFSM.ArithFSM.Mod61
