import E213.Math.Cohomology.DyadicArithFSMtoBitFSM
import E213.Math.Cohomology.DyadicConcretePellSig

/-!
# Pell ArithFSM mod 31 — period 15 (SPLIT case, fourth instance)

31 mod 5 = 1.  (1/5) = 1, QR.  So (5/31) = 1, SPLIT.

Pisano predictor: split case predicts (p-1)/2 = 15.
Tight: period 15.  predicted = 15 — exact match.

Fourth SPLIT instance (after p=11, 19, 29).  Bit period 15 (odd);
signature period 30 (doubled by bipartite parity coupling).
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- Pell-style FSM mod 31. -/
def pellFSMmod31 : ArithFSM2 31 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 31, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 31, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-31 first values check. -/
theorem pellFSMmod31_first_check :
    pellFSMmod31.bits 0 = true
    ∧ pellFSMmod31.bits 14 = false
    ∧ pellFSMmod31.bits 15 = true := by decide

/-- ★★★ Pell mod-31 run cycles with TIGHT period 15. -/
theorem pellFSMmod31_run_period_15 :
    ∀ k, pellFSMmod31.run (k + 15) = pellFSMmod31.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod31.step (pellFSMmod31.run (k' + 15))
        = pellFSMmod31.step (pellFSMmod31.run k')
    rw [ih]

/-- ★★★★ Pell mod-31 bits cycle with TIGHT period 15. -/
theorem pellFSMmod31_bits_period_15 :
    ∀ k, pellFSMmod31.bits (k + 15) = pellFSMmod31.bits k := by
  intro k
  show pellFSMmod31.out (pellFSMmod31.run (k + 15))
      = pellFSMmod31.out (pellFSMmod31.run k)
  rw [pellFSMmod31_run_period_15]

/-- Bipartite parity doubling: bit period 15 odd ⇒ sig period 30. -/
theorem pellFSMmod31_bits_period_30 :
    ∀ k, pellFSMmod31.bits (k + 30) = pellFSMmod31.bits k := by
  intro k
  have h1 := pellFSMmod31_bits_period_15 (k + 15)
  have h2 := pellFSMmod31_bits_period_15 k
  have hreshape : k + 30 = (k + 15) + 15 := (Nat.add_assoc k 15 15).symm
  rw [hreshape, h1, h2]

/-- ★★★★★ Pell mod-31 signature has period 30 (TIGHT, doubled). -/
theorem pellFSMmod31_signature_period_30 :
    ∀ k, signature pellFSMmod31.bits (k + 30)
        = signature pellFSMmod31.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod31.bits 30
    pellFSMmod31_bits_period_30 (by decide)

end E213.Math.Cohomology.DyadicConjecture
