import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 23 — period 24 (INERT case, fourth instance)

23 mod 5 = 3.  (3/5) = -1 (3² ≡ -1 mod 5), so (5/23) = -1.  INERT.

Pisano formula: period | p + 1 = 24.  Computational check confirms
the Pell trajectory closes at step 24.

Fourth INERT instance (after p=3, 7, 13, 17), matching p+1 across
all four sizes.  Bit period 24 (even); signature period 24.
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Mod23

/-- Pell-style FSM mod 23. -/
def pellFSMmod23 : ArithFSM2 23 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 23, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 23, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-23 run cycles with period 24 (TIGHT). -/
theorem pellFSMmod23_run_period_24 :
    ∀ k, pellFSMmod23.run (k + 24) = pellFSMmod23.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod23.step (pellFSMmod23.run (k' + 24))
        = pellFSMmod23.step (pellFSMmod23.run k')
    rw [ih]

/-- ★★★★ Pell mod-23 bits cycle with period 24. -/
theorem pellFSMmod23_bits_period_24 :
    ∀ k, pellFSMmod23.bits (k + 24) = pellFSMmod23.bits k := by
  intro k
  show pellFSMmod23.out (pellFSMmod23.run (k + 24))
      = pellFSMmod23.out (pellFSMmod23.run k)
  rw [pellFSMmod23_run_period_24]

/-- ★★★★★ Pell mod-23 signature has period 24 (TIGHT). -/
theorem pellFSMmod23_signature_period_24 :
    ∀ k, signature pellFSMmod23.bits (k + 24)
        = signature pellFSMmod23.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod23.bits 24
    pellFSMmod23_bits_period_24 (by decide)

end E213.Math.Cohomology.Dyadic.ArithFSM.Mod23
