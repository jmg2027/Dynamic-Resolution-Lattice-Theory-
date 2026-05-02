import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 89 — TIGHT period 22, predict 44 (×2 SUB-TIGHT)

89 mod 5 = 4, QR ⇒ SPLIT. Predict (p-1)/2 = 44.
TIGHT period: 22.  predict = 2 · tight (×2 SUB-TIGHT).

★ Third ×2 sub-tight case ★ (after p=29). Confirms the pattern:
×2 sub-tight occurs at some split primes due to Frobenius-stable
subgroup of order (p-1)/2 in the trajectory.

Sub-tight cases now in Pell-5:
  p=29 (split, ×2): tight 7,  predict 14
  p=47 (inert, ×3): tight 16, predict 48
  p=89 (split, ×2): tight 22, predict 44 ★ NEW

Galois-orbit interpretation: predictor formula gives upper bound
on tight period; tightness depends on absence of Frobenius-stable
subgroups in Pell trajectory.
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Mod89

open E213.Math.Cohomology.Dyadic.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)

open E213.Math.Cohomology.Dyadic.ArithFSM (ArithFSM2)


def pellFSMmod89 : ArithFSM2 89 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 89, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 89, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 1024 in
theorem pellFSMmod89_run_period_22 :
    ∀ k, pellFSMmod89.run (k + 22) = pellFSMmod89.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod89.step (pellFSMmod89.run (k' + 22))
        = pellFSMmod89.step (pellFSMmod89.run k')
    rw [ih]

theorem pellFSMmod89_bits_period_22 :
    ∀ k, pellFSMmod89.bits (k + 22) = pellFSMmod89.bits k := by
  intro k
  show pellFSMmod89.out (pellFSMmod89.run (k + 22))
      = pellFSMmod89.out (pellFSMmod89.run k)
  rw [pellFSMmod89_run_period_22]

theorem pellFSMmod89_bits_period_44 :
    ∀ k, pellFSMmod89.bits (k + 44) = pellFSMmod89.bits k := by
  intro k
  have h1 := pellFSMmod89_bits_period_22 (k + 22)
  have h2 := pellFSMmod89_bits_period_22 k
  have hreshape : k + 44 = (k + 22) + 22 := rfl
  rw [hreshape, h1, h2]

end E213.Math.Cohomology.Dyadic.ArithFSM.Mod89
