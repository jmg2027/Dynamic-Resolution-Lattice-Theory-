import E213.Math.Cohomology.Dyadic.ArithFSMtoBitFSM
import E213.Math.Cohomology.DyadicConcretePellSig

/-!
# Pell ArithFSM mod 41 — period 20 (SPLIT case, fifth instance)

41 mod 5 = 1.  (1/5) = 1, QR.  So (5/41) = 1, SPLIT.

Pisano predictor: split case predicts (p-1)/2 = 20.
Tight: period 20.  predicted = 20 — exact match.

Fifth SPLIT instance (after p=11, 19, 29, 31).  Bit period 20
(even); signature period 20 (no doubling).
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- Pell-style FSM mod 41. -/
def pellFSMmod41 : ArithFSM2 41 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 41, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 41, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-41 run cycles with TIGHT period 20. -/
theorem pellFSMmod41_run_period_20 :
    ∀ k, pellFSMmod41.run (k + 20) = pellFSMmod41.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod41.step (pellFSMmod41.run (k' + 20))
        = pellFSMmod41.step (pellFSMmod41.run k')
    rw [ih]

/-- ★★★★ Pell mod-41 bits cycle with TIGHT period 20. -/
theorem pellFSMmod41_bits_period_20 :
    ∀ k, pellFSMmod41.bits (k + 20) = pellFSMmod41.bits k := by
  intro k
  show pellFSMmod41.out (pellFSMmod41.run (k + 20))
      = pellFSMmod41.out (pellFSMmod41.run k)
  rw [pellFSMmod41_run_period_20]

/-- ★★★★★ Pell mod-41 signature has period 20 (TIGHT, even). -/
theorem pellFSMmod41_signature_period_20 :
    ∀ k, signature pellFSMmod41.bits (k + 20)
        = signature pellFSMmod41.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod41.bits 20
    pellFSMmod41_bits_period_20 (by decide)

end E213.Math.Cohomology.DyadicConjecture
