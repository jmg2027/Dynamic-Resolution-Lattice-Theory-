import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 13 — period 14 (INERT case, second instance)

Pell discriminant Δ = 5.  Legendre (5/13) = (13/5) = (3/5).
3^((5-1)/2) = 3² = 9 ≡ -1 mod 5.  So (5/13) = -1, INERT.

Pisano formula (inert): period | p + 1 = 14.

Trajectory:
  (1,1) → (3,2) → (8,5) → (8,0) → (3,8) → (1,11)
        → (0,12) → (12,12) → (10,11) → (5,8) → (5,0)
        → (10,5) → (12,2) → (0,1) → (1,1).

Period 14, exactly p+1.  Bit period 14 (even); signature period
also 14 (no parity doubling needed).
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

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

/-- ★★★ Pell mod-13 run cycles with period 14 (TIGHT). -/
theorem pellFSMmod13_run_period_14 :
    ∀ k, pellFSMmod13.run (k + 14) = pellFSMmod13.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod13.step (pellFSMmod13.run (k' + 14))
        = pellFSMmod13.step (pellFSMmod13.run k')
    rw [ih]

/-- ★★★★ Pell mod-13 bits cycle with period 14. -/
theorem pellFSMmod13_bits_period_14 :
    ∀ k, pellFSMmod13.bits (k + 14) = pellFSMmod13.bits k := by
  intro k
  show pellFSMmod13.out (pellFSMmod13.run (k + 14))
      = pellFSMmod13.out (pellFSMmod13.run k)
  rw [pellFSMmod13_run_period_14]

/-- ★★★★★ Pell mod-13 signature has period 14 (TIGHT). -/
theorem pellFSMmod13_signature_period_14 :
    ∀ k, signature pellFSMmod13.bits (k + 14)
        = signature pellFSMmod13.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod13.bits 14
    pellFSMmod13_bits_period_14 (by decide)

end E213.Math.Cohomology.Dyadic.Conjecture
