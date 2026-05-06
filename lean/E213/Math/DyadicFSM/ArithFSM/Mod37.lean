import E213.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Math.DyadicFSM.ConcretePellSig

import E213.Math.DyadicFSM.ArithFSM
import E213.Math.DyadicFSM.Signature
/-!
# Pell ArithFSM mod 37 — period 38 (INERT case, fifth instance)

37 mod 5 = 2.  (2/5) = -1 (Euler: 2² = 4 ≡ -1 mod 5).  So (5/37) = -1,
INERT.

Pisano formula: inert case period | p + 1 = 38.  Computational
check confirms the Pell trajectory closes at step 38 (TIGHT).

Fifth INERT instance (after p=3, 7, 13, 17, 23), matching p+1 across
all six sizes.  Bit period 38 (even); signature period 38 (no doubling).
-/

namespace E213.Math.DyadicFSM.ArithFSM.Mod37

open E213.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Math.DyadicFSM.Signature (signature)
open E213.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 37. -/
def pellFSMmod37 : ArithFSM2 37 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 37, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 37, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-37 run cycles with TIGHT period 38. -/
theorem pellFSMmod37_run_period_38 :
    ∀ k, pellFSMmod37.run (k + 38) = pellFSMmod37.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod37.step (pellFSMmod37.run (k' + 38))
        = pellFSMmod37.step (pellFSMmod37.run k')
    rw [ih]

/-- ★★★★ Pell mod-37 bits cycle with TIGHT period 38. -/
theorem pellFSMmod37_bits_period_38 :
    ∀ k, pellFSMmod37.bits (k + 38) = pellFSMmod37.bits k := by
  intro k
  show pellFSMmod37.out (pellFSMmod37.run (k + 38))
      = pellFSMmod37.out (pellFSMmod37.run k)
  rw [pellFSMmod37_run_period_38]

/-- ★★★★★ Pell mod-37 signature has period 38 (TIGHT, even bit period). -/
theorem pellFSMmod37_signature_period_38 :
    ∀ k, signature pellFSMmod37.bits (k + 38)
        = signature pellFSMmod37.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod37.bits 38
    pellFSMmod37_bits_period_38 (by decide)

end E213.Math.DyadicFSM.ArithFSM.Mod37
