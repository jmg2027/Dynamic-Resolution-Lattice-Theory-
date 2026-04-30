import E213.Math.Cohomology.DyadicArithFSMtoBitFSM
import E213.Math.Cohomology.DyadicConcretePellSig

/-!
# Pell ArithFSM mod 13 — period 28 (INERT case, second instance)

Pell discriminant Δ = 5.  Legendre (5/13) = (13/5) = (3/5).
3^((5-1)/2) = 3² = 9 ≡ -1 mod 5.  So (5/13) = -1, INERT.

Pisano formula: π(13) | 2(13+1) = 28.  Computational check shows
the Pell trajectory mod 13 in (Fin 13)² returns to (1,1) at step 28.

This is the second INERT instance (after p=3, p=7), confirming the
inert formula at a larger size.  Bit period 28; signature period
also 28 (even, no parity doubling).
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- Pell-style FSM mod 13. -/
def pellFSMmod13 : ArithFSM2 13 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 13, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 13, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-13 first 5 bit values. -/
theorem pellFSMmod13_first5 :
    pellFSMmod13.bits 0 = true ∧ pellFSMmod13.bits 1 = false
    ∧ pellFSMmod13.bits 2 = false ∧ pellFSMmod13.bits 3 = false
    ∧ pellFSMmod13.bits 4 = false := by decide

/-- ★★★ Pell mod-13 run cycles with period 28. -/
theorem pellFSMmod13_run_period_28 :
    ∀ k, pellFSMmod13.run (k + 28) = pellFSMmod13.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod13.step (pellFSMmod13.run (k' + 28))
        = pellFSMmod13.step (pellFSMmod13.run k')
    rw [ih]

/-- ★★★★ Pell mod-13 bits cycle with period 28. -/
theorem pellFSMmod13_bits_period_28 :
    ∀ k, pellFSMmod13.bits (k + 28) = pellFSMmod13.bits k := by
  intro k
  show pellFSMmod13.out (pellFSMmod13.run (k + 28))
      = pellFSMmod13.out (pellFSMmod13.run k)
  rw [pellFSMmod13_run_period_28]

/-- ★★★★★ Pell mod-13 signature has period 28 (TIGHT, even). -/
theorem pellFSMmod13_signature_period_28 :
    ∀ k, signature pellFSMmod13.bits (k + 28)
        = signature pellFSMmod13.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod13.bits 28
    pellFSMmod13_bits_period_28 (by decide)

end E213.Math.Cohomology.DyadicConjecture
