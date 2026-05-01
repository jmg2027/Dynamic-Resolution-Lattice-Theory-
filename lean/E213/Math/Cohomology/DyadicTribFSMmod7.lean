import E213.Math.Cohomology.Dyadic.ArithFSM3
import E213.Math.Cohomology.Dyadic.ArithFSMtoBitFSM
import E213.Math.Cohomology.DyadicConcretePellSig

/-!
# Tribonacci ArithFSM3 mod 7 — period 48 (cubic class, fourth instance)

7 mod 5 = 2.  Tribonacci-Pisano period mod 7 = 48.

Trib trajectory: state (a, b, c) → (b, c, a+b+c).  Out: (a == 1).
Initial: (0, 1, 1).

Wall–Sun (Tribonacci-Pisano) periods now: π(2)=4, π(3)=13, π(5)=31, π(7)=48.
At mod 7, period 48 is *highly composite* (= 16·3 = 48), unlike
the prime periods at mod 3, 5.  This is the first cubic-Pisano
non-prime period in our table — significant because it suggests
mixed Galois behaviour (not pure prime cycles).

Cubic CRT extended to {2, 3, 5, 7} → lcm(4, 13, 31, 48) = 25584.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- Tribonacci shift mod 7. -/
def tribFSMmod7 : ArithFSM3 7 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b, c) := p
    (b, c, ⟨(a.val + b.val + c.val) % 7, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Tribonacci mod-7 run cycles with TIGHT period 48. -/
theorem tribFSMmod7_run_period_48 :
    ∀ k, tribFSMmod7.run (k + 48) = tribFSMmod7.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show tribFSMmod7.step (tribFSMmod7.run (k' + 48))
        = tribFSMmod7.step (tribFSMmod7.run k')
    rw [ih]

/-- ★★★★ Tribonacci mod-7 bits cycle with TIGHT period 48. -/
theorem tribFSMmod7_bits_period_48 :
    ∀ k, tribFSMmod7.bits (k + 48) = tribFSMmod7.bits k := by
  intro k
  show tribFSMmod7.out (tribFSMmod7.run (k + 48))
      = tribFSMmod7.out (tribFSMmod7.run k)
  rw [tribFSMmod7_run_period_48]

set_option maxRecDepth 2048 in
/-- ★★★★★ Tribonacci mod-7 signature has period 48 from step 1
    (pre-period 1; even bit period 48 ⇒ no doubling). -/
theorem tribFSMmod7_signature_period_48_from_1 :
    ∀ k, k ≥ 1 →
      signature tribFSMmod7.bits (k + 48)
        = signature tribFSMmod7.bits k :=
  signature_period_of_bits_period_and_anchor_from
    tribFSMmod7.bits 48 1 tribFSMmod7_bits_period_48 (by decide)

end E213.Math.Cohomology.DyadicConjecture
