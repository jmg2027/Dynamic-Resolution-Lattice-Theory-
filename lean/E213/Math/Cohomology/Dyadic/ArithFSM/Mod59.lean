import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 59 — period 29 (SPLIT, TIGHT)

59 mod 5 = 4 = (±2)², QR.  So (5/59) = 1, SPLIT.
Predict (p-1)/2 = 29, TIGHT (matches exactly).

Bit period 29 (odd) ⇒ signature period 58 (doubled).
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Mod59

/-- Pell-style FSM mod 59. -/
def pellFSMmod59 : ArithFSM2 59 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 59, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 59, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-59 run cycles with TIGHT period 29. -/
theorem pellFSMmod59_run_period_29 :
    ∀ k, pellFSMmod59.run (k + 29) = pellFSMmod59.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod59.step (pellFSMmod59.run (k' + 29))
        = pellFSMmod59.step (pellFSMmod59.run k')
    rw [ih]

/-- ★★★★ Pell mod-59 bits cycle with TIGHT period 29. -/
theorem pellFSMmod59_bits_period_29 :
    ∀ k, pellFSMmod59.bits (k + 29) = pellFSMmod59.bits k := by
  intro k
  show pellFSMmod59.out (pellFSMmod59.run (k + 29))
      = pellFSMmod59.out (pellFSMmod59.run k)
  rw [pellFSMmod59_run_period_29]

/-- Bipartite parity doubling: bit period 29 odd ⇒ predicted 58. -/
theorem pellFSMmod59_bits_period_58 :
    ∀ k, pellFSMmod59.bits (k + 58) = pellFSMmod59.bits k := by
  intro k
  have h1 := pellFSMmod59_bits_period_29 (k + 29)
  have h2 := pellFSMmod59_bits_period_29 k
  have hreshape : k + 58 = (k + 29) + 29 := rfl
  rw [hreshape, h1, h2]

set_option maxRecDepth 2048 in
/-- ★★★★★ Pell mod-59 signature has period 58 (TIGHT, doubled). -/
theorem pellFSMmod59_signature_period_58 :
    ∀ k, signature pellFSMmod59.bits (k + 58)
        = signature pellFSMmod59.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod59.bits 58
    pellFSMmod59_bits_period_58 (by decide)

end E213.Math.Cohomology.Dyadic.ArithFSM.Mod59
