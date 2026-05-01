import E213.Math.Cohomology.Dyadic.ArithFSMtoBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 53 — period 54 (INERT, TIGHT)

53 mod 5 = 3.  (3/5) = -1.  So (5/53) = -1, INERT.
Predict p+1 = 54, TIGHT.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- Pell-style FSM mod 53. -/
def pellFSMmod53 : ArithFSM2 53 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 53, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 53, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 2048 in
/-- ★★★ Pell mod-53 run cycles with TIGHT period 54. -/
theorem pellFSMmod53_run_period_54 :
    ∀ k, pellFSMmod53.run (k + 54) = pellFSMmod53.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod53.step (pellFSMmod53.run (k' + 54))
        = pellFSMmod53.step (pellFSMmod53.run k')
    rw [ih]

/-- ★★★★ Pell mod-53 bits cycle with TIGHT period 54. -/
theorem pellFSMmod53_bits_period_54 :
    ∀ k, pellFSMmod53.bits (k + 54) = pellFSMmod53.bits k := by
  intro k
  show pellFSMmod53.out (pellFSMmod53.run (k + 54))
      = pellFSMmod53.out (pellFSMmod53.run k)
  rw [pellFSMmod53_run_period_54]

set_option maxRecDepth 2048 in
/-- ★★★★★ Pell mod-53 signature has period 54 (TIGHT, even). -/
theorem pellFSMmod53_signature_period_54 :
    ∀ k, signature pellFSMmod53.bits (k + 54)
        = signature pellFSMmod53.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod53.bits 54
    pellFSMmod53_bits_period_54 (by decide)

end E213.Math.Cohomology.Dyadic.Conjecture
