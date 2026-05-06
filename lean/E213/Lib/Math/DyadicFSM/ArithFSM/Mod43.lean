import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.DyadicFSM.ConcretePellSig

import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.Signature
/-!
# Pell ArithFSM mod 43 — period 44 (INERT case, sixth instance)

43 mod 5 = 3.  (3/5) = -1 (NQR).  So (5/43) = -1, INERT.

Pisano formula: inert case period | p + 1 = 44.  Tight: period
44 — exact match.

Sixth INERT instance (after p=3, 7, 13, 17, 23, 37), matching p+1
across all six sizes.  Bit period 44 (even); signature period 44
(no doubling).
-/

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod43

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 43. -/
def pellFSMmod43 : ArithFSM2 43 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 43, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 43, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-43 run cycles with TIGHT period 44. -/
theorem pellFSMmod43_run_period_44 :
    ∀ k, pellFSMmod43.run (k + 44) = pellFSMmod43.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod43.step (pellFSMmod43.run (k' + 44))
        = pellFSMmod43.step (pellFSMmod43.run k')
    rw [ih]

/-- ★★★★ Pell mod-43 bits cycle with TIGHT period 44. -/
theorem pellFSMmod43_bits_period_44 :
    ∀ k, pellFSMmod43.bits (k + 44) = pellFSMmod43.bits k := by
  intro k
  show pellFSMmod43.out (pellFSMmod43.run (k + 44))
      = pellFSMmod43.out (pellFSMmod43.run k)
  rw [pellFSMmod43_run_period_44]

set_option maxRecDepth 1024 in
/-- ★★★★★ Pell mod-43 signature has period 44 (TIGHT, even). -/
theorem pellFSMmod43_signature_period_44 :
    ∀ k, signature pellFSMmod43.bits (k + 44)
        = signature pellFSMmod43.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod43.bits 44
    pellFSMmod43_bits_period_44 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod43
