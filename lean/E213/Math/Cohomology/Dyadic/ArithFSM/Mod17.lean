import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 17 — period 18 (INERT case, third instance)

Pell discriminant Δ = 5.  17 mod 5 = 2.  (2/5) = -1 (NQR), so by
quadratic reciprocity (5/17) = -1.  INERT.

Pisano formula (inert): period | p + 1 = 18.  Computational check
confirms the Pell trajectory closes at exactly step 18.

This is the third INERT instance (after p=3, p=7, p=13), confirming
the inert formula p+1 across multiple sizes.  Bit period 18 (even);
signature period also 18.
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Mod17

/-- Pell-style FSM mod 17. -/
def pellFSMmod17 : ArithFSM2 17 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 17, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 17, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-17 first 5 bit values. -/
theorem pellFSMmod17_first5 :
    pellFSMmod17.bits 0 = true ∧ pellFSMmod17.bits 1 = false
    ∧ pellFSMmod17.bits 2 = false ∧ pellFSMmod17.bits 3 = false
    ∧ pellFSMmod17.bits 4 = false := by decide

/-- ★★★ Pell mod-17 run cycles with period 18 (TIGHT). -/
theorem pellFSMmod17_run_period_18 :
    ∀ k, pellFSMmod17.run (k + 18) = pellFSMmod17.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod17.step (pellFSMmod17.run (k' + 18))
        = pellFSMmod17.step (pellFSMmod17.run k')
    rw [ih]

/-- ★★★★ Pell mod-17 bits cycle with period 18. -/
theorem pellFSMmod17_bits_period_18 :
    ∀ k, pellFSMmod17.bits (k + 18) = pellFSMmod17.bits k := by
  intro k
  show pellFSMmod17.out (pellFSMmod17.run (k + 18))
      = pellFSMmod17.out (pellFSMmod17.run k)
  rw [pellFSMmod17_run_period_18]

/-- ★★★★★ Pell mod-17 signature has period 18 (TIGHT). -/
theorem pellFSMmod17_signature_period_18 :
    ∀ k, signature pellFSMmod17.bits (k + 18)
        = signature pellFSMmod17.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod17.bits 18
    pellFSMmod17_bits_period_18 (by decide)

end E213.Math.Cohomology.Dyadic.ArithFSM.Mod17
