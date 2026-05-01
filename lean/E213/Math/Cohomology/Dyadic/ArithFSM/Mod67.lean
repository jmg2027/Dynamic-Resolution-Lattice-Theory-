import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 67 — period 68 (INERT, TIGHT)

67 mod 5 = 2, NQR ⇒ INERT. Predict p+1 = 68. TIGHT.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

def pellFSMmod67 : ArithFSM2 67 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 67, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 67, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 2048 in
theorem pellFSMmod67_run_period_68 :
    ∀ k, pellFSMmod67.run (k + 68) = pellFSMmod67.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod67.step (pellFSMmod67.run (k' + 68))
        = pellFSMmod67.step (pellFSMmod67.run k')
    rw [ih]

theorem pellFSMmod67_bits_period_68 :
    ∀ k, pellFSMmod67.bits (k + 68) = pellFSMmod67.bits k := by
  intro k
  show pellFSMmod67.out (pellFSMmod67.run (k + 68))
      = pellFSMmod67.out (pellFSMmod67.run k)
  rw [pellFSMmod67_run_period_68]

end E213.Math.Cohomology.Dyadic.Conjecture
