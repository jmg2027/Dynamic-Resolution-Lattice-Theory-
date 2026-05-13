import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.DyadicFSM.ArithFSM.V3
import E213.Lib.Math.DyadicFSM.ConcretePellSig
import E213.Lib.Math.DyadicFSM.Signature.Signature

/-!
# Trib.FSMmod — Tribonacci ArithFSM per-modulus instances

Per-prime Tribonacci-FSM evidence at mod {3, 5, 7}.  Pattern:
3-state ArithFSM with characteristic polynomial `t^3 - t^2 - t - 1`,
projected per modulus to compute concrete Pisano-like period.

Per-N namespaces preserved (`Trib.FSMmod{N}`).
-/

namespace E213.Lib.Math.DyadicFSM.Trib.FSMmod3

open E213.Lib.Math.DyadicFSM.ArithFSM.V3 (ArithFSM3)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


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

end E213.Lib.Math.DyadicFSM.Trib.FSMmod3

namespace E213.Lib.Math.DyadicFSM.Trib.FSMmod5

open E213.Lib.Math.DyadicFSM.ArithFSM.V3 (ArithFSM3)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


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

end E213.Lib.Math.DyadicFSM.Trib.FSMmod5

namespace E213.Lib.Math.DyadicFSM.Trib.FSMmod7

open E213.Lib.Math.DyadicFSM.ArithFSM.V3 (ArithFSM3)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


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

end E213.Lib.Math.DyadicFSM.Trib.FSMmod7
