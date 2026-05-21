import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.DyadicFSM.Signature.PeriodClosure
import E213.Lib.Math.DyadicFSM.Signature.Signature

/-!
# ArithFSM.ModMedium — per-prime ArithFSM instances (Medium primes)

Per-prime ArithFSM Fibonacci-recurrence period instances for primes
[29, 31, 37, 41, 43, 47].

Per-N namespaces preserved (`ArithFSM.Mod{N}`).
-/

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod29

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 29. -/
def pellFSMmod29 : ArithFSM2 29 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 29, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 29, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-29 first values check. -/
theorem pellFSMmod29_first_check :
    pellFSMmod29.bits 0 = true
    ∧ pellFSMmod29.bits 6 = false
    ∧ pellFSMmod29.bits 7 = true := by decide

/-- ★★★ Pell mod-29 run cycles with TIGHT period 7. -/
theorem pellFSMmod29_run_period_7 :
    ∀ k, pellFSMmod29.run (k + 7) = pellFSMmod29.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod29.step (pellFSMmod29.run (k' + 7))
        = pellFSMmod29.step (pellFSMmod29.run k')
    rw [ih]

/-- ★★★★ Pell mod-29 bits cycle with TIGHT period 7. -/
theorem pellFSMmod29_bits_period_7 :
    ∀ k, pellFSMmod29.bits (k + 7) = pellFSMmod29.bits k :=
  ArithFSM2.bits_period_of_run_period _ pellFSMmod29_run_period_7

/-- Bipartite parity doubling: bit period 7 odd ⇒ predicted 14. -/
theorem pellFSMmod29_bits_period_14 :
    ∀ k, pellFSMmod29.bits (k + 14) = pellFSMmod29.bits k := by
  intro k
  have h1 := pellFSMmod29_bits_period_7 (k + 7)
  have h2 := pellFSMmod29_bits_period_7 k
  have hreshape : k + 14 = (k + 7) + 7 := rfl
  rw [hreshape, h1, h2]

/-- ★★★★★ Pell mod-29 signature has period 14 (TIGHT, doubled). -/
theorem pellFSMmod29_signature_period_14 :
    ∀ k, signature pellFSMmod29.bits (k + 14)
        = signature pellFSMmod29.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod29.bits 14
    pellFSMmod29_bits_period_14 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod29

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod31

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 31. -/
def pellFSMmod31 : ArithFSM2 31 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 31, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 31, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-31 first values check. -/
theorem pellFSMmod31_first_check :
    pellFSMmod31.bits 0 = true
    ∧ pellFSMmod31.bits 14 = false
    ∧ pellFSMmod31.bits 15 = true := by decide

/-- ★★★ Pell mod-31 run cycles with TIGHT period 15. -/
theorem pellFSMmod31_run_period_15 :
    ∀ k, pellFSMmod31.run (k + 15) = pellFSMmod31.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod31.step (pellFSMmod31.run (k' + 15))
        = pellFSMmod31.step (pellFSMmod31.run k')
    rw [ih]

/-- ★★★★ Pell mod-31 bits cycle with TIGHT period 15. -/
theorem pellFSMmod31_bits_period_15 :
    ∀ k, pellFSMmod31.bits (k + 15) = pellFSMmod31.bits k :=
  ArithFSM2.bits_period_of_run_period _ pellFSMmod31_run_period_15

/-- Bipartite parity doubling: bit period 15 odd ⇒ sig period 30. -/
theorem pellFSMmod31_bits_period_30 :
    ∀ k, pellFSMmod31.bits (k + 30) = pellFSMmod31.bits k := by
  intro k
  have h1 := pellFSMmod31_bits_period_15 (k + 15)
  have h2 := pellFSMmod31_bits_period_15 k
  have hreshape : k + 30 = (k + 15) + 15 := rfl
  rw [hreshape, h1, h2]

/-- ★★★★★ Pell mod-31 signature has period 30 (TIGHT, doubled). -/
theorem pellFSMmod31_signature_period_30 :
    ∀ k, signature pellFSMmod31.bits (k + 30)
        = signature pellFSMmod31.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod31.bits 30
    pellFSMmod31_bits_period_30 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod31

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod37

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 37. -/
def pellFSMmod37 : ArithFSM2 37 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 37, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 37, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-37 run cycles with TIGHT period 38. -/
theorem pellFSMmod37_run_period_38 :
    ∀ k, pellFSMmod37.run (k + 38) = pellFSMmod37.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod37.step (pellFSMmod37.run (k' + 38))
        = pellFSMmod37.step (pellFSMmod37.run k')
    rw [ih]

/-- ★★★★ Pell mod-37 bits cycle with TIGHT period 38. -/
theorem pellFSMmod37_bits_period_38 :
    ∀ k, pellFSMmod37.bits (k + 38) = pellFSMmod37.bits k :=
  ArithFSM2.bits_period_of_run_period _ pellFSMmod37_run_period_38

/-- ★★★★★ Pell mod-37 signature has period 38 (TIGHT, even bit period). -/
theorem pellFSMmod37_signature_period_38 :
    ∀ k, signature pellFSMmod37.bits (k + 38)
        = signature pellFSMmod37.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod37.bits 38
    pellFSMmod37_bits_period_38 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod37

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod41

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 41. -/
def pellFSMmod41 : ArithFSM2 41 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 41, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 41, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-41 run cycles with TIGHT period 20. -/
theorem pellFSMmod41_run_period_20 :
    ∀ k, pellFSMmod41.run (k + 20) = pellFSMmod41.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod41.step (pellFSMmod41.run (k' + 20))
        = pellFSMmod41.step (pellFSMmod41.run k')
    rw [ih]

/-- ★★★★ Pell mod-41 bits cycle with TIGHT period 20. -/
theorem pellFSMmod41_bits_period_20 :
    ∀ k, pellFSMmod41.bits (k + 20) = pellFSMmod41.bits k :=
  ArithFSM2.bits_period_of_run_period _ pellFSMmod41_run_period_20

/-- ★★★★★ Pell mod-41 signature has period 20 (TIGHT, even). -/
theorem pellFSMmod41_signature_period_20 :
    ∀ k, signature pellFSMmod41.bits (k + 20)
        = signature pellFSMmod41.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod41.bits 20
    pellFSMmod41_bits_period_20 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod41

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod43

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 43. -/
def pellFSMmod43 : ArithFSM2 43 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 43, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 43, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-43 run cycles with TIGHT period 44. -/
theorem pellFSMmod43_run_period_44 :
    ∀ k, pellFSMmod43.run (k + 44) = pellFSMmod43.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod43.step (pellFSMmod43.run (k' + 44))
        = pellFSMmod43.step (pellFSMmod43.run k')
    rw [ih]

/-- ★★★★ Pell mod-43 bits cycle with TIGHT period 44. -/
theorem pellFSMmod43_bits_period_44 :
    ∀ k, pellFSMmod43.bits (k + 44) = pellFSMmod43.bits k :=
  ArithFSM2.bits_period_of_run_period _ pellFSMmod43_run_period_44

set_option maxRecDepth 1024 in
/-- ★★★★★ Pell mod-43 signature has period 44 (TIGHT, even). -/
theorem pellFSMmod43_signature_period_44 :
    ∀ k, signature pellFSMmod43.bits (k + 44)
        = signature pellFSMmod43.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod43.bits 44
    pellFSMmod43_bits_period_44 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod43

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod47

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 47. -/
def pellFSMmod47 : ArithFSM2 47 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 47, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 47, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-47 run cycles with TIGHT period 16. -/
theorem pellFSMmod47_run_period_16 :
    ∀ k, pellFSMmod47.run (k + 16) = pellFSMmod47.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod47.step (pellFSMmod47.run (k' + 16))
        = pellFSMmod47.step (pellFSMmod47.run k')
    rw [ih]

/-- ★★★★ Pell mod-47 bits cycle with TIGHT period 16. -/
theorem pellFSMmod47_bits_period_16 :
    ∀ k, pellFSMmod47.bits (k + 16) = pellFSMmod47.bits k :=
  ArithFSM2.bits_period_of_run_period _ pellFSMmod47_run_period_16

/-- Predicted period (3× tight): bits cycle with predict = p+1 = 48. -/
theorem pellFSMmod47_bits_period_48 :
    ∀ k, pellFSMmod47.bits (k + 48) = pellFSMmod47.bits k := by
  intro k
  have h1 := pellFSMmod47_bits_period_16 (k + 32)
  have h2 := pellFSMmod47_bits_period_16 (k + 16)
  have h3 := pellFSMmod47_bits_period_16 k
  have hreshape : k + 48 = ((k + 16) + 16) + 16 := rfl
  rw [hreshape, h1, h2, h3]

/-- ★★★★★ Pell mod-47 signature has period 16 (TIGHT, even). -/
theorem pellFSMmod47_signature_period_16 :
    ∀ k, signature pellFSMmod47.bits (k + 16)
        = signature pellFSMmod47.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod47.bits 16
    pellFSMmod47_bits_period_16 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod47
