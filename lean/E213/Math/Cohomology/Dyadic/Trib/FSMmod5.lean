import E213.Math.Cohomology.Dyadic.ArithFSM.V3
import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Tribonacci ArithFSM3 mod 5 — period 31 (cubic class, third instance)

Generalises Tribonacci mod 2 (period 4) and mod 3 (period 13) to
mod 5 (period 31).

Tribonacci recurrence: a_{k+3} = a_k + a_{k+1} + a_{k+2}.
State (a, b, c) → (b, c, a+b+c).  Out: (a == 1).
Initial: (0, 1, 1).

Wall–Sun (Tribonacci-Pisano) period mod 5 is 31 — a *prime*
period (31 prime).  Cubic Galois behaviour: the trajectory closes
in 31 steps despite (Fin 5)³ having 125 states.

Three-modulus CRT base case: {2, 3, 5} → periods {4, 13, 31}.
Wall–Sun lcm = lcm(4, 13, 31) = 1612.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- Tribonacci shift mod 5: state (a, b, c) → (b, c, a + b + c).
    Out: parity of a (bit = a == 1). -/
def tribFSMmod5 : ArithFSM3 5 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b, c) := p
    (b, c, ⟨(a.val + b.val + c.val) % 5, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Tribonacci mod-5 first values check. -/
theorem tribFSMmod5_first_check :
    tribFSMmod5.bits 0 = false ∧ tribFSMmod5.bits 1 = true
    ∧ tribFSMmod5.bits 30 = false := by decide

/-- ★★★ Tribonacci mod-5 run cycles with TIGHT period 31. -/
theorem tribFSMmod5_run_period_31 :
    ∀ k, tribFSMmod5.run (k + 31) = tribFSMmod5.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show tribFSMmod5.step (tribFSMmod5.run (k' + 31))
        = tribFSMmod5.step (tribFSMmod5.run k')
    rw [ih]

/-- ★★★★ Tribonacci mod-5 bits cycle with period 31. -/
theorem tribFSMmod5_bits_period_31 :
    ∀ k, tribFSMmod5.bits (k + 31) = tribFSMmod5.bits k := by
  intro k
  show tribFSMmod5.out (tribFSMmod5.run (k + 31))
      = tribFSMmod5.out (tribFSMmod5.run k)
  rw [tribFSMmod5_run_period_31]

/-- Bipartite parity doubling: bit period 31 odd ⇒ predicted 62 (sig). -/
theorem tribFSMmod5_bits_period_62 :
    ∀ k, tribFSMmod5.bits (k + 62) = tribFSMmod5.bits k := by
  intro k
  have h1 := tribFSMmod5_bits_period_31 (k + 31)
  have h2 := tribFSMmod5_bits_period_31 k
  have hreshape : k + 62 = (k + 31) + 31 := rfl
  rw [hreshape, h1, h2]

set_option maxRecDepth 1024 in
/-- ★★★★★ Tribonacci mod-5 signature has period 62 from step 1
    (pre-period 1; bit period 31 odd ⇒ signature doubled). -/
theorem tribFSMmod5_signature_period_62_from_1 :
    ∀ k, k ≥ 1 →
      signature tribFSMmod5.bits (k + 62)
        = signature tribFSMmod5.bits k :=
  signature_period_of_bits_period_and_anchor_from
    tribFSMmod5.bits 62 1 tribFSMmod5_bits_period_62 (by decide)

end E213.Math.Cohomology.Dyadic.Conjecture
