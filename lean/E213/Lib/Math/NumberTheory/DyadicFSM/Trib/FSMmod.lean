import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3
import E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature

/-!
# Trib.FSMmod — Tribonacci ArithFSM per-modulus instances

Per-prime Tribonacci-FSM evidence at mod {3, 5, 7}.  Pattern:
3-state ArithFSM with characteristic polynomial `t^3 - t^2 - t - 1`,
projected per modulus to compute concrete Pisano-like period.

Per-N namespaces preserved (`Trib.FSMmod{N}`).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Trib.FSMmod3

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3 (ArithFSM3)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3.ArithFSM3 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (bits_period_mul_of_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Tribonacci shift mod 3: state (a, b, c) → (b, c, a + b + c).
    Out: parity of a (bit = a == 1). -/
def tribFSMmod3 : ArithFSM3 3 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b, c) := p
    (b, c, ⟨(a.val + b.val + c.val) % 3, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Tribonacci mod-3 run cycles with period 13. -/
theorem tribFSMmod3_run_period_13 :
    ∀ k, tribFSMmod3.run (k + 13) = tribFSMmod3.run k :=
  ArithFSM3.run_period_of_base _ (by decide)

/-- ★★★★ Tribonacci mod-3 bits cycle with period 13. -/
theorem tribFSMmod3_bits_period_13 :
    ∀ k, tribFSMmod3.bits (k + 13) = tribFSMmod3.bits k :=
  bits_period_of_run_period _ tribFSMmod3_run_period_13

/-- Bipartite parity doubling: bit period 13 odd ⇒ predicted 26 (sig). -/
theorem tribFSMmod3_bits_period_26 :
    ∀ k, tribFSMmod3.bits (k + 26) = tribFSMmod3.bits k :=
  bits_period_mul_of_period _ tribFSMmod3_bits_period_13 2

/-- ★★★★★ Tribonacci mod-3 signature has period 26 from step 1
    (pre-period 1; bit period 13 odd ⇒ signature doubled). -/
theorem tribFSMmod3_signature_period_26_from_1 :
    ∀ k, k ≥ 1 →
      signature tribFSMmod3.bits (k + 26)
        = signature tribFSMmod3.bits k :=
  signature_period_of_bits_period_and_anchor_from
    tribFSMmod3.bits 26 1 tribFSMmod3_bits_period_26 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Trib.FSMmod3

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Trib.FSMmod5

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3 (ArithFSM3)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3.ArithFSM3 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (bits_period_mul_of_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Tribonacci shift mod 5: state (a, b, c) → (b, c, a + b + c).
    Out: parity of a (bit = a == 1). -/
def tribFSMmod5 : ArithFSM3 5 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b, c) := p
    (b, c, ⟨(a.val + b.val + c.val) % 5, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Tribonacci mod-5 run cycles with TIGHT period 31. -/
theorem tribFSMmod5_run_period_31 :
    ∀ k, tribFSMmod5.run (k + 31) = tribFSMmod5.run k :=
  ArithFSM3.run_period_of_base _ (by decide)

/-- ★★★★ Tribonacci mod-5 bits cycle with period 31. -/
theorem tribFSMmod5_bits_period_31 :
    ∀ k, tribFSMmod5.bits (k + 31) = tribFSMmod5.bits k :=
  bits_period_of_run_period _ tribFSMmod5_run_period_31

/-- Bipartite parity doubling: bit period 31 odd ⇒ predicted 62 (sig). -/
theorem tribFSMmod5_bits_period_62 :
    ∀ k, tribFSMmod5.bits (k + 62) = tribFSMmod5.bits k :=
  bits_period_mul_of_period _ tribFSMmod5_bits_period_31 2

set_option maxRecDepth 1024 in
/-- ★★★★★ Tribonacci mod-5 signature has period 62 from step 1
    (pre-period 1; bit period 31 odd ⇒ signature doubled). -/
theorem tribFSMmod5_signature_period_62_from_1 :
    ∀ k, k ≥ 1 →
      signature tribFSMmod5.bits (k + 62)
        = signature tribFSMmod5.bits k :=
  signature_period_of_bits_period_and_anchor_from
    tribFSMmod5.bits 62 1 tribFSMmod5_bits_period_62 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Trib.FSMmod5

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Trib.FSMmod7

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3 (ArithFSM3)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V3.ArithFSM3 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Tribonacci shift mod 7. -/
def tribFSMmod7 : ArithFSM3 7 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b, c) := p
    (b, c, ⟨(a.val + b.val + c.val) % 7, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Tribonacci mod-7 run cycles with TIGHT period 48. -/
theorem tribFSMmod7_run_period_48 :
    ∀ k, tribFSMmod7.run (k + 48) = tribFSMmod7.run k :=
  ArithFSM3.run_period_of_base _ (by decide)

/-- ★★★★ Tribonacci mod-7 bits cycle with TIGHT period 48. -/
theorem tribFSMmod7_bits_period_48 :
    ∀ k, tribFSMmod7.bits (k + 48) = tribFSMmod7.bits k :=
  bits_period_of_run_period _ tribFSMmod7_run_period_48

set_option maxRecDepth 2048 in
/-- ★★★★★ Tribonacci mod-7 signature has period 48 from step 1
    (pre-period 1; even bit period 48 ⇒ no doubling). -/
theorem tribFSMmod7_signature_period_48_from_1 :
    ∀ k, k ≥ 1 →
      signature tribFSMmod7.bits (k + 48)
        = signature tribFSMmod7.bits k :=
  signature_period_of_bits_period_and_anchor_from
    tribFSMmod7.bits 48 1 tribFSMmod7_bits_period_48 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Trib.FSMmod7
