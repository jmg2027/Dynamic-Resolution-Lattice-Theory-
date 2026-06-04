import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature

/-!
# Fib.FSMmod — Fibonacci ArithFSM per-modulus instances

Per-prime Fibonacci-FSM evidence (modulo {3, 5, 7, 11, 13, 17, 19,
23}).  Each modulus = one instance of the Fibonacci recurrence
projected onto `ArithFSM`, plus its concrete Pisano period bound.

Pattern (per p):
  - SPLIT case  (`(5/p) = 1`): period divides `p - 1`
  - INERT case  (`(5/p) = -1`): period divides `2(p + 1)`
  - SPECIAL     (`p ∈ {3, 5}`): direct check

Per-N namespaces preserved (`Fib.FSMmod{N}`).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod3

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ArithFSM2 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Fibonacci-style FSM mod 3. -/
def fibFSMmod3 : ArithFSM2 3 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Fibonacci mod-3 run cycles with TIGHT period 8. -/
theorem fibFSMmod3_run_period_8 :
    ∀ k, fibFSMmod3.run (k + 8) = fibFSMmod3.run k :=
  ArithFSM2.run_period_of_base _ (by decide)

/-- ★★★★ Fibonacci mod-3 bits cycle with TIGHT period 8. -/
theorem fibFSMmod3_bits_period_8 :
    ∀ k, fibFSMmod3.bits (k + 8) = fibFSMmod3.bits k :=
  bits_period_of_run_period _ fibFSMmod3_run_period_8

/-- ★★★★★ Fibonacci mod-3 signature has period 8 from step 1
    (pre-period 1; init bit is `false`, distinct from base sig 0). -/
theorem fibFSMmod3_signature_period_8_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod3.bits (k + 8)
        = signature fibFSMmod3.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod3.bits 8 1 fibFSMmod3_bits_period_8 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod3

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod5

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ArithFSM2 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Fibonacci-style FSM mod 5. -/
def fibFSMmod5 : ArithFSM2 5 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 5, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Fibonacci mod-5 run cycles with TIGHT period 20. -/
theorem fibFSMmod5_run_period_20 :
    ∀ k, fibFSMmod5.run (k + 20) = fibFSMmod5.run k :=
  ArithFSM2.run_period_of_base _ (by decide)

/-- ★★★★ Fibonacci mod-5 bits cycle with TIGHT period 20. -/
theorem fibFSMmod5_bits_period_20 :
    ∀ k, fibFSMmod5.bits (k + 20) = fibFSMmod5.bits k :=
  bits_period_of_run_period _ fibFSMmod5_run_period_20

/-- ★★★★★ Fibonacci mod-5 signature has period 20 from step 1. -/
theorem fibFSMmod5_signature_period_20_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod5.bits (k + 20)
        = signature fibFSMmod5.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod5.bits 20 1 fibFSMmod5_bits_period_20 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod5

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod7

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ArithFSM2 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Fibonacci-style FSM mod 7. -/
def fibFSMmod7 : ArithFSM2 7 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 7, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Fibonacci mod-7 run cycles with TIGHT period 16. -/
theorem fibFSMmod7_run_period_16 :
    ∀ k, fibFSMmod7.run (k + 16) = fibFSMmod7.run k :=
  ArithFSM2.run_period_of_base _ (by decide)

/-- ★★★★ Fibonacci mod-7 bits cycle with TIGHT period 16. -/
theorem fibFSMmod7_bits_period_16 :
    ∀ k, fibFSMmod7.bits (k + 16) = fibFSMmod7.bits k :=
  bits_period_of_run_period _ fibFSMmod7_run_period_16

/-- ★★★★★ Fibonacci mod-7 signature has period 16 from step 1. -/
theorem fibFSMmod7_signature_period_16_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod7.bits (k + 16)
        = signature fibFSMmod7.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod7.bits 16 1 fibFSMmod7_bits_period_16 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod7

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod11

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ArithFSM2 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Fibonacci-style FSM mod 11. -/
def fibFSMmod11 : ArithFSM2 11 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 11, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Fibonacci mod-11 run cycles with TIGHT period 10. -/
theorem fibFSMmod11_run_period_10 :
    ∀ k, fibFSMmod11.run (k + 10) = fibFSMmod11.run k :=
  ArithFSM2.run_period_of_base _ (by decide)

/-- ★★★★ Fibonacci mod-11 bits cycle with TIGHT period 10. -/
theorem fibFSMmod11_bits_period_10 :
    ∀ k, fibFSMmod11.bits (k + 10) = fibFSMmod11.bits k :=
  bits_period_of_run_period _ fibFSMmod11_run_period_10

/-- ★★★★★ Fibonacci mod-11 signature has period 10 from step 1. -/
theorem fibFSMmod11_signature_period_10_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod11.bits (k + 10)
        = signature fibFSMmod11.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod11.bits 10 1 fibFSMmod11_bits_period_10 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod11

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod13

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ArithFSM2 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


def fibFSMmod13 : ArithFSM2 13 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 13, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

theorem fibFSMmod13_run_period_28 :
    ∀ k, fibFSMmod13.run (k + 28) = fibFSMmod13.run k :=
  ArithFSM2.run_period_of_base _ (by decide)

theorem fibFSMmod13_bits_period_28 :
    ∀ k, fibFSMmod13.bits (k + 28) = fibFSMmod13.bits k :=
  bits_period_of_run_period _ fibFSMmod13_run_period_28

set_option maxRecDepth 1024 in
theorem fibFSMmod13_signature_period_28_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod13.bits (k + 28) = signature fibFSMmod13.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod13.bits 28 1 fibFSMmod13_bits_period_28 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod13

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod17

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ArithFSM2 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


def fibFSMmod17 : ArithFSM2 17 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 17, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 1024 in
theorem fibFSMmod17_run_period_36 :
    ∀ k, fibFSMmod17.run (k + 36) = fibFSMmod17.run k :=
  ArithFSM2.run_period_of_base _ (by decide)

theorem fibFSMmod17_bits_period_36 :
    ∀ k, fibFSMmod17.bits (k + 36) = fibFSMmod17.bits k :=
  bits_period_of_run_period _ fibFSMmod17_run_period_36

set_option maxRecDepth 2048 in
theorem fibFSMmod17_signature_period_36_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod17.bits (k + 36) = signature fibFSMmod17.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod17.bits 36 1 fibFSMmod17_bits_period_36 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod17

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod19

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ArithFSM2 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


def fibFSMmod19 : ArithFSM2 19 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 19, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

theorem fibFSMmod19_run_period_18 :
    ∀ k, fibFSMmod19.run (k + 18) = fibFSMmod19.run k :=
  ArithFSM2.run_period_of_base _ (by decide)

theorem fibFSMmod19_bits_period_18 :
    ∀ k, fibFSMmod19.bits (k + 18) = fibFSMmod19.bits k :=
  bits_period_of_run_period _ fibFSMmod19_run_period_18

theorem fibFSMmod19_signature_period_18_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod19.bits (k + 18) = signature fibFSMmod19.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod19.bits 18 1 fibFSMmod19_bits_period_18 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod19

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod23

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ArithFSM2 (bits_period_of_run_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


def fibFSMmod23 : ArithFSM2 23 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 23, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 2048 in
theorem fibFSMmod23_run_period_48 :
    ∀ k, fibFSMmod23.run (k + 48) = fibFSMmod23.run k :=
  ArithFSM2.run_period_of_base _ (by decide)

theorem fibFSMmod23_bits_period_48 :
    ∀ k, fibFSMmod23.bits (k + 48) = fibFSMmod23.bits k :=
  bits_period_of_run_period _ fibFSMmod23_run_period_48

set_option maxRecDepth 2048 in
theorem fibFSMmod23_signature_period_48_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod23.bits (k + 48) = signature fibFSMmod23.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod23.bits 48 1 fibFSMmod23_bits_period_48 (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.Fib.FSMmod23
