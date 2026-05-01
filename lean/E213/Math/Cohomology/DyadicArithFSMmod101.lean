import E213.Math.Cohomology.DyadicArithFSMtoBitFSM
import E213.Math.Cohomology.DyadicConcretePellSig

/-!
# Pell ArithFSM mod 101 — TIGHT period 25, predict 50 (×2 SUB-TIGHT)

101 mod 5 = 1, QR ⇒ SPLIT. Predict (p-1)/2 = 50.
TIGHT period: 25.  predict = 2 · tight.

★ Fourth ×2 sub-tight case ★ (after p=29, p=89).

Pattern: split ×2 sub-tight at primes where p ≡ 1 mod 4 AND
specific Frobenius structure.  Now confirmed at p ∈ {29, 89, 101}.
-/

namespace E213.Math.Cohomology.DyadicConjecture

def pellFSMmod101 : ArithFSM2 101 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 101, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 101, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 1024 in
theorem pellFSMmod101_run_period_25 :
    ∀ k, pellFSMmod101.run (k + 25) = pellFSMmod101.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod101.step (pellFSMmod101.run (k' + 25))
        = pellFSMmod101.step (pellFSMmod101.run k')
    rw [ih]

theorem pellFSMmod101_bits_period_25 :
    ∀ k, pellFSMmod101.bits (k + 25) = pellFSMmod101.bits k := by
  intro k
  show pellFSMmod101.out (pellFSMmod101.run (k + 25))
      = pellFSMmod101.out (pellFSMmod101.run k)
  rw [pellFSMmod101_run_period_25]

theorem pellFSMmod101_bits_period_50 :
    ∀ k, pellFSMmod101.bits (k + 50) = pellFSMmod101.bits k := by
  intro k
  have h1 := pellFSMmod101_bits_period_25 (k + 25)
  have h2 := pellFSMmod101_bits_period_25 k
  have hreshape : k + 50 = (k + 25) + 25 := (Nat.add_assoc k 25 25).symm
  rw [hreshape, h1, h2]

end E213.Math.Cohomology.DyadicConjecture
