import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

import E213.Math.Cohomology.Dyadic.ArithFSM
import E213.Math.Cohomology.Dyadic.Signature
/-!
# Pell ArithFSM mod 11 — period 5 (SPLIT case)

Pell trajectory in (Fin 11 × Fin 11):

  (1,1) → (3,2) → (8,5) → (10,2) → (0,1) → (1,1)  [period 5]

The Legendre lens predicted (5/11) = QR (split), which by the
Pisano formula gives π_F(11) | 11 - 1 = 10, and our period
= π_F(11) / gcd(π_F(11), 2) = 10 / 2 = 5.

This is the FIRST split-case Pell instance, complementing the
previous inert/ramified cases (mod 3, 5, 7).
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Mod11

open E213.Math.Cohomology.Dyadic.ArithFSM (ArithFSM2)
open E213.Math.Cohomology.Dyadic.Signature (signature)
open E213.Math.Cohomology.Dyadic.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 11. -/
def pellFSMmod11 : ArithFSM2 11 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 11, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 11, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-11 first 12 bit values: T F F F F T F F F F T F. -/
theorem pellFSMmod11_first12 :
    pellFSMmod11.bits 0 = true ∧ pellFSMmod11.bits 1 = false
    ∧ pellFSMmod11.bits 2 = false ∧ pellFSMmod11.bits 3 = false
    ∧ pellFSMmod11.bits 4 = false ∧ pellFSMmod11.bits 5 = true
    ∧ pellFSMmod11.bits 6 = false ∧ pellFSMmod11.bits 7 = false
    ∧ pellFSMmod11.bits 8 = false ∧ pellFSMmod11.bits 9 = false
    ∧ pellFSMmod11.bits 10 = true ∧ pellFSMmod11.bits 11 = false := by decide

/-- ★★★ Pell mod-11 run cycles with period 5 (SPLIT — shorter than inert). -/
theorem pellFSMmod11_run_period_5 :
    ∀ k, pellFSMmod11.run (k + 5) = pellFSMmod11.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod11.step (pellFSMmod11.run (k' + 5))
        = pellFSMmod11.step (pellFSMmod11.run k')
    rw [ih]

/-- ★★★★ Pell mod-11 bits cycle with period 5. -/
theorem pellFSMmod11_bits_period_5 :
    ∀ k, pellFSMmod11.bits (k + 5) = pellFSMmod11.bits k := by
  intro k
  show pellFSMmod11.out (pellFSMmod11.run (k + 5))
      = pellFSMmod11.out (pellFSMmod11.run k)
  rw [pellFSMmod11_run_period_5]

/-- Bit period doubles to signature period 10 (bipartite parity coupling,
    bit period 5 is odd). -/
theorem pellFSMmod11_bits_period_10 :
    ∀ k, pellFSMmod11.bits (k + 10) = pellFSMmod11.bits k := by
  intro k
  have h1 := pellFSMmod11_bits_period_5 (k + 5)
  have h2 := pellFSMmod11_bits_period_5 k
  have hreshape : k + 10 = (k + 5) + 5 := rfl
  rw [hreshape, h1, h2]

/-- ★★★★★ Pell mod-11 signature has period 10 (TIGHT, doubled by parity). -/
theorem pellFSMmod11_signature_period_10 :
    ∀ k, signature pellFSMmod11.bits (k + 10) = signature pellFSMmod11.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod11.bits 10
    pellFSMmod11_bits_period_10 (by decide)

/-- ★★★★ Pell mod-11 signature period bound: 605 = 5·121. -/
theorem pellFSMmod11_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 605
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod11.bits (k + P) = signature pellFSMmod11.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 11) (by decide) pellFSMmod11
  exact ⟨N, P, hP, hbound, hk⟩

end E213.Math.Cohomology.Dyadic.ArithFSM.Mod11
