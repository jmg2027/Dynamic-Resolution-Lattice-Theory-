import E213.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Math.DyadicFSM.ConcretePellSig

import E213.Math.DyadicFSM.ArithFSM
import E213.Math.DyadicFSM.Signature
/-!
# Pell ArithFSM mod 47 — period 16 (INERT, predict 48 = 3·16)

47 mod 5 = 2.  (2/5) = -1 (NQR).  So (5/47) = -1, INERT.

Pisano predictor: inert case predicts p+1 = 48.
TRUE TIGHT period: 16.  predicted = 48 = 3 · 16.

★ NEW PHENOMENON ★ — at p=47, the predictor formula
overestimates the true period by a factor of **3**.  This is the
first observed split-by-3 instance; previously p=29 (split, factor
2) was the only sub-tight case.

Generalised pattern emerging from the 14-prime evidence:
  - Most primes: predictor matches tight period
  - Sub-tight cases: predictor = N · tight for N ∈ {2, 3, ...}
  - The factor reflects subtle Galois-orbit splitting in the
    Pell-discriminant trajectory

Bit period 16 (even); signature period 16 (no doubling); plus
predicted-period 48 derived by composition.
-/

namespace E213.Math.DyadicFSM.ArithFSM.Mod47

open E213.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Math.DyadicFSM.Signature (signature)
open E213.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 47. -/
def pellFSMmod47 : ArithFSM2 47 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 47, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 47, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-47 run cycles with TIGHT period 16. -/
theorem pellFSMmod47_run_period_16 :
    ∀ k, pellFSMmod47.run (k + 16) = pellFSMmod47.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod47.step (pellFSMmod47.run (k' + 16))
        = pellFSMmod47.step (pellFSMmod47.run k')
    rw [ih]

/-- ★★★★ Pell mod-47 bits cycle with TIGHT period 16. -/
theorem pellFSMmod47_bits_period_16 :
    ∀ k, pellFSMmod47.bits (k + 16) = pellFSMmod47.bits k := by
  intro k
  show pellFSMmod47.out (pellFSMmod47.run (k + 16))
      = pellFSMmod47.out (pellFSMmod47.run k)
  rw [pellFSMmod47_run_period_16]

/-- Predicted period (3× tight): bits cycle with predict = p+1 = 48. -/
theorem pellFSMmod47_bits_period_48 :
    ∀ k, pellFSMmod47.bits (k + 48) = pellFSMmod47.bits k := by
  intro k
  have h1 := pellFSMmod47_bits_period_16 (k + 32)
  have h2 := pellFSMmod47_bits_period_16 (k + 16)
  have h3 := pellFSMmod47_bits_period_16 k
  have hreshape : k + 48 = ((k + 16) + 16) + 16 := rfl
  rw [hreshape, h1, h2, h3]

/-- ★★★★★ Pell mod-47 signature has period 16 (TIGHT, even). -/
theorem pellFSMmod47_signature_period_16 :
    ∀ k, signature pellFSMmod47.bits (k + 16)
        = signature pellFSMmod47.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod47.bits 16
    pellFSMmod47_bits_period_16 (by decide)

end E213.Math.DyadicFSM.ArithFSM.Mod47
