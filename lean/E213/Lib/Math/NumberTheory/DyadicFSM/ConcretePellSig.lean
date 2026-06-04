import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Signature
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.PeriodClosure
import E213.Meta.Tactic.NatHelper

import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature
/-!
# Concrete signature periods for the Pell ArithFSM family

The eventual-period theorem only existential.  Concrete computation
shows the actual periods are tight:

  - pellFSMmod2: bit period 3 ⇒ signature pre-period 1, period 6
  - pellFSMmod3: bit period 4 ⇒ signature period 4 (pure)
  - pellFSMmod5: bit period 10 ⇒ signature period 10 (pure)

This file gives a *universal closure* lemma: bits periodic with
period P AND sig P = sig 0 ⇒ sig is purely periodic with period P.

Then applies it to the Pell mod-3 and Pell mod-5 instances.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (pellFSMmod3_bits_period_4 pellFSMmod2_bits_period_3)

open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (nextVertex signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (pellFSMmod2 pellFSMmod3)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)


-- `signature_period_of_bits_period_and_anchor` (universal closure
-- with period P)
-- to break the ArithFSM ↔ ConcretePellSig build cycle.

/-- ★★★★ Pell mod-3 signature has period 4 (equal to bit period). -/
theorem pellFSMmod3_signature_period_4 :
    ∀ k, signature pellFSMmod3.bits (k + 4) = signature pellFSMmod3.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod3.bits 4
    pellFSMmod3_bits_period_4 (by decide)

/-- ★★★★★ Pell mod-5 signature has period 10 (equal to bit period). -/
theorem pellFSMmod5_signature_period_10 :
    ∀ k, signature pellFSMmod5.bits (k + 10) = signature pellFSMmod5.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod5.bits 10
    pellFSMmod5_bits_period_10 (by decide)

-- `signature_period_of_bits_period_and_anchor_from` (eventual-period
-- closure with pre-period N₀) moved to `Signature/PeriodClosure.lean`
-- — breaks the ArithFSM ↔ ConcretePellSig build cycle.

/-- ★★★★ Pell mod-2 signature has period 6 from step 1 (TIGHT;
    pre-period 1, then 2×3-fold cycle). -/
theorem pellFSMmod2_signature_period_6_from_1 :
    ∀ k, k ≥ 1 →
      signature pellFSMmod2.bits (k + 6) = signature pellFSMmod2.bits k := by
  apply signature_period_of_bits_period_and_anchor_from
    pellFSMmod2.bits 6 1
  · intro k
    have hp3 := pellFSMmod2_bits_period_3 (k + 3)
    have hp3' := pellFSMmod2_bits_period_3 k
    have heq : k + 6 = (k + 3) + 3 := (Nat.add_assoc k 3 3).symm
    rw [heq, hp3, hp3']
  · decide

end E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig
