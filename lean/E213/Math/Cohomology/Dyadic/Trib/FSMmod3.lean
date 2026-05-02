import E213.Math.Cohomology.Dyadic.ArithFSM.V3
import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Tribonacci ArithFSM3 mod 3 — period 13 (cubic class, second instance)

Generalises Tribonacci mod 2 (period 4) to mod 3.

Tribonacci recurrence: a_{k+3} = a_k + a_{k+1} + a_{k+2}.
State (a, b, c) → (b, c, a+b+c).  Out: parity (a == 1).
Initial: (0, 1, 1).

Trajectory mod 3 first 13 bits:
  [0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0]
then repeats.

Wall–Sun (Tribonacci-Pisano) period mod 3 is 13 — a *prime*
period despite the modulus being prime, suggesting non-trivial
Galois behaviour for the cubic plastic-style recurrence.
-/

namespace E213.Math.Cohomology.Dyadic.Trib.FSMmod3

open E213.Math.Cohomology.Dyadic.ArithFSM.V3 (ArithFSM3)
open E213.Math.Cohomology.Dyadic.Signature (signature)


/-- Tribonacci shift mod 3: state (a, b, c) → (b, c, a + b + c).
    Out: parity of a (bit = a == 1). -/
def tribFSMmod3 : ArithFSM3 3 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b, c) := p
    (b, c, ⟨(a.val + b.val + c.val) % 3, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Tribonacci mod-3 first-13 sanity check. -/
theorem tribFSMmod3_first13 :
    tribFSMmod3.bits 0 = false  ∧ tribFSMmod3.bits 1 = true
    ∧ tribFSMmod3.bits 2 = true ∧ tribFSMmod3.bits 11 = true
    ∧ tribFSMmod3.bits 12 = false := by decide

/-- ★★★ Tribonacci mod-3 run cycles with period 13 (TIGHT). -/
theorem tribFSMmod3_run_period_13 :
    ∀ k, tribFSMmod3.run (k + 13) = tribFSMmod3.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show tribFSMmod3.step (tribFSMmod3.run (k' + 13))
        = tribFSMmod3.step (tribFSMmod3.run k')
    rw [ih]

/-- ★★★★ Tribonacci mod-3 bits cycle with period 13. -/
theorem tribFSMmod3_bits_period_13 :
    ∀ k, tribFSMmod3.bits (k + 13) = tribFSMmod3.bits k := by
  intro k
  show tribFSMmod3.out (tribFSMmod3.run (k + 13))
      = tribFSMmod3.out (tribFSMmod3.run k)
  rw [tribFSMmod3_run_period_13]

/-- Bipartite parity doubling: bit period 13 odd ⇒ predicted 26 (sig). -/
theorem tribFSMmod3_bits_period_26 :
    ∀ k, tribFSMmod3.bits (k + 26) = tribFSMmod3.bits k := by
  intro k
  have h1 := tribFSMmod3_bits_period_13 (k + 13)
  have h2 := tribFSMmod3_bits_period_13 k
  have hreshape : k + 26 = (k + 13) + 13 := rfl
  rw [hreshape, h1, h2]

/-- ★★★★★ Tribonacci mod-3 signature has period 26 from step 1
    (pre-period 1; bit period 13 odd ⇒ signature doubled). -/
theorem tribFSMmod3_signature_period_26_from_1 :
    ∀ k, k ≥ 1 →
      signature tribFSMmod3.bits (k + 26)
        = signature tribFSMmod3.bits k :=
  signature_period_of_bits_period_and_anchor_from
    tribFSMmod3.bits 26 1 tribFSMmod3_bits_period_26 (by decide)

end E213.Math.Cohomology.Dyadic.Trib.FSMmod3
