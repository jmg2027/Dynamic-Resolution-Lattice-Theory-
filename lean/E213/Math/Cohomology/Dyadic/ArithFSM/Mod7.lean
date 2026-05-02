import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Pell ArithFSM mod 7 — period 8

Extends the Pell family with a fourth modulus.  Trajectory in
(Fin 7 × Fin 7) state space:

  (1,1) → (3,2) → (1,5) → (0,6) → (6,6)
        → (4,5) → (6,2) → (0,1) → (1,1) [period 8]

Bound 5n² = 5·49 = 245 (universal); TIGHT signature period
will be matched after computation.
-/

namespace E213.Math.Cohomology.Dyadic.ArithFSM.Mod7

open E213.Math.Cohomology.Dyadic.ArithFSM (ArithFSM2)
open E213.Math.Cohomology.Dyadic.Signature (signature)


/-- Pell-style FSM mod 7. -/
def pellFSMmod7 : ArithFSM2 7 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 7, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 7, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-7 first 12 bit values. -/
theorem pellFSMmod7_first12 :
    pellFSMmod7.bits 0 = true ∧ pellFSMmod7.bits 1 = false
    ∧ pellFSMmod7.bits 2 = true ∧ pellFSMmod7.bits 3 = false
    ∧ pellFSMmod7.bits 4 = false ∧ pellFSMmod7.bits 5 = false
    ∧ pellFSMmod7.bits 6 = false ∧ pellFSMmod7.bits 7 = false
    ∧ pellFSMmod7.bits 8 = true ∧ pellFSMmod7.bits 9 = false
    ∧ pellFSMmod7.bits 10 = true ∧ pellFSMmod7.bits 11 = false := by decide

/-- ★★★ Pell mod-7 run cycles with period 8. -/
theorem pellFSMmod7_run_period_8 :
    ∀ k, pellFSMmod7.run (k + 8) = pellFSMmod7.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod7.step (pellFSMmod7.run (k' + 8))
        = pellFSMmod7.step (pellFSMmod7.run k')
    rw [ih]

/-- ★★★★ Pell mod-7 bits cycle with period 8. -/
theorem pellFSMmod7_bits_period_8 :
    ∀ k, pellFSMmod7.bits (k + 8) = pellFSMmod7.bits k := by
  intro k
  show pellFSMmod7.out (pellFSMmod7.run (k + 8))
      = pellFSMmod7.out (pellFSMmod7.run k)
  rw [pellFSMmod7_run_period_8]

/-- ★★★★★ Pell mod-7 signature has period 8 (TIGHT). -/
theorem pellFSMmod7_signature_period_8 :
    ∀ k, signature pellFSMmod7.bits (k + 8) = signature pellFSMmod7.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod7.bits 8
    pellFSMmod7_bits_period_8 (by decide)

/-- ★★★★ Pell mod-7 signature period bound: 245 = 5·49. -/
theorem pellFSMmod7_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 245
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod7.bits (k + P) = signature pellFSMmod7.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 7) (by decide) pellFSMmod7
  exact ⟨N, P, hP, hbound, hk⟩

end E213.Math.Cohomology.Dyadic.ArithFSM.Mod7
