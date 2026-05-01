import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 19 — period 9 (SPLIT case, second instance)

Pell discriminant Δ = 5.  19 mod 5 = 4 = (±2)², QR.  So (5/19) = 1,
SPLIT.

Pisano formula: split case period | (p-1)/gcd((p-1),2) = 18/2 = 9.

Trajectory: (1,1) → (3,2) → (8,5) → (2,13) → (17,15) → (11,13)
                  → (16,5) → (18,2) → (0,1) → (1,1).  Period 9.

This is the second SPLIT instance (after p=11), confirming the split
formula (p-1)/2 at a larger size.  Bit period 9 (odd); signature
period 18 (doubled by bipartite parity coupling).
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Mod19

/-- Pell-style FSM mod 19. -/
def pellFSMmod19 : ArithFSM2 19 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 19, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 19, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-19 first values check. -/
theorem pellFSMmod19_first10 :
    pellFSMmod19.bits 0 = true ∧ pellFSMmod19.bits 1 = false
    ∧ pellFSMmod19.bits 8 = false ∧ pellFSMmod19.bits 9 = true := by decide

/-- ★★★ Pell mod-19 run cycles with period 9. -/
theorem pellFSMmod19_run_period_9 :
    ∀ k, pellFSMmod19.run (k + 9) = pellFSMmod19.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod19.step (pellFSMmod19.run (k' + 9))
        = pellFSMmod19.step (pellFSMmod19.run k')
    rw [ih]

/-- ★★★★ Pell mod-19 bits cycle with period 9. -/
theorem pellFSMmod19_bits_period_9 :
    ∀ k, pellFSMmod19.bits (k + 9) = pellFSMmod19.bits k := by
  intro k
  show pellFSMmod19.out (pellFSMmod19.run (k + 9))
      = pellFSMmod19.out (pellFSMmod19.run k)
  rw [pellFSMmod19_run_period_9]

/-- Bipartite parity doubling: bit period 9 odd ⇒ signature period 18. -/
theorem pellFSMmod19_bits_period_18 :
    ∀ k, pellFSMmod19.bits (k + 18) = pellFSMmod19.bits k := by
  intro k
  have h1 := pellFSMmod19_bits_period_9 (k + 9)
  have h2 := pellFSMmod19_bits_period_9 k
  have hreshape : k + 18 = (k + 9) + 9 := rfl
  rw [hreshape, h1, h2]

/-- ★★★★★ Pell mod-19 signature has period 18 (TIGHT, doubled). -/
theorem pellFSMmod19_signature_period_18 :
    ∀ k, signature pellFSMmod19.bits (k + 18)
        = signature pellFSMmod19.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod19.bits 18
    pellFSMmod19_bits_period_18 (by decide)

end E213.Math.Cohomology.Dyadic.ArithFSM.Mod19
