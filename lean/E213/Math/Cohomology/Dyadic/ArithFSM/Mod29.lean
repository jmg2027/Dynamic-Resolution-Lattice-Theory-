import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 29 — predict 14 (SPLIT case, third instance)

29 mod 5 = 4 = (±2)², QR.  So (5/29) = 1, SPLIT.

Pisano predictor: split case predicts (p-1)/2 = 14.
Actual tight period: 7.  predicted = 14 = 2·7 still cycles bits.

Third SPLIT instance (after p=11, 19), confirming the split formula
(p-1)/2 at a larger size.  Bit period 7 (tight); signature period
14 (doubled by bipartite parity coupling).
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Mod29

open E213.Math.Cohomology.Dyadic.ArithFSM.V2 (ArithFSM2)
open E213.Math.Cohomology.Dyadic.Signature (signature)


/-- Pell-style FSM mod 29. -/
def pellFSMmod29 : ArithFSM2 29 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 29, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 29, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-29 first values check. -/
theorem pellFSMmod29_first_check :
    pellFSMmod29.bits 0 = true
    ∧ pellFSMmod29.bits 6 = false
    ∧ pellFSMmod29.bits 7 = true := by decide

/-- ★★★ Pell mod-29 run cycles with TIGHT period 7. -/
theorem pellFSMmod29_run_period_7 :
    ∀ k, pellFSMmod29.run (k + 7) = pellFSMmod29.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod29.step (pellFSMmod29.run (k' + 7))
        = pellFSMmod29.step (pellFSMmod29.run k')
    rw [ih]

/-- ★★★★ Pell mod-29 bits cycle with TIGHT period 7. -/
theorem pellFSMmod29_bits_period_7 :
    ∀ k, pellFSMmod29.bits (k + 7) = pellFSMmod29.bits k := by
  intro k
  show pellFSMmod29.out (pellFSMmod29.run (k + 7))
      = pellFSMmod29.out (pellFSMmod29.run k)
  rw [pellFSMmod29_run_period_7]

/-- Bipartite parity doubling: bit period 7 odd ⇒ predicted 14. -/
theorem pellFSMmod29_bits_period_14 :
    ∀ k, pellFSMmod29.bits (k + 14) = pellFSMmod29.bits k := by
  intro k
  have h1 := pellFSMmod29_bits_period_7 (k + 7)
  have h2 := pellFSMmod29_bits_period_7 k
  have hreshape : k + 14 = (k + 7) + 7 := rfl
  rw [hreshape, h1, h2]

/-- ★★★★★ Pell mod-29 signature has period 14 (TIGHT, doubled). -/
theorem pellFSMmod29_signature_period_14 :
    ∀ k, signature pellFSMmod29.bits (k + 14)
        = signature pellFSMmod29.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod29.bits 14
    pellFSMmod29_bits_period_14 (by decide)

end E213.Math.Cohomology.Dyadic.ArithFSM.Mod29
