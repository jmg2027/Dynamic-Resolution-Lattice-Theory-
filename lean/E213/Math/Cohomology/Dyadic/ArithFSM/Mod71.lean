import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 71 — period 35 (SPLIT, TIGHT)

71 mod 5 = 1, QR ⇒ SPLIT. Predict (p-1)/2 = 35. TIGHT.
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Mod71

def pellFSMmod71 : ArithFSM2 71 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 71, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 71, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 1024 in
theorem pellFSMmod71_run_period_35 :
    ∀ k, pellFSMmod71.run (k + 35) = pellFSMmod71.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod71.step (pellFSMmod71.run (k' + 35))
        = pellFSMmod71.step (pellFSMmod71.run k')
    rw [ih]

theorem pellFSMmod71_bits_period_35 :
    ∀ k, pellFSMmod71.bits (k + 35) = pellFSMmod71.bits k := by
  intro k
  show pellFSMmod71.out (pellFSMmod71.run (k + 35))
      = pellFSMmod71.out (pellFSMmod71.run k)
  rw [pellFSMmod71_run_period_35]

end E213.Math.Cohomology.Dyadic.ArithFSM.Mod71
