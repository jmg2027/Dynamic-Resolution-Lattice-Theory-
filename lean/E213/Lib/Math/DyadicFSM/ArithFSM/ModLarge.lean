import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.DyadicFSM.ConcretePellSig
import E213.Lib.Math.DyadicFSM.Signature.Signature

/-!
# ArithFSM.ModLarge — per-prime ArithFSM instances (Large primes)

Per-prime ArithFSM Fibonacci-recurrence period instances for primes
[53, 59, 61, 67, 71, 73, 79, 89, 101].

Per-N namespaces preserved (`ArithFSM.Mod{N}`).
-/

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod53

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 53. -/
def pellFSMmod53 : ArithFSM2 53 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 53, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 53, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 2048 in
/-- ★★★ Pell mod-53 run cycles with TIGHT period 54. -/
theorem pellFSMmod53_run_period_54 :
    ∀ k, pellFSMmod53.run (k + 54) = pellFSMmod53.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod53.step (pellFSMmod53.run (k' + 54))
        = pellFSMmod53.step (pellFSMmod53.run k')
    rw [ih]

/-- ★★★★ Pell mod-53 bits cycle with TIGHT period 54. -/
theorem pellFSMmod53_bits_period_54 :
    ∀ k, pellFSMmod53.bits (k + 54) = pellFSMmod53.bits k := by
  intro k
  show pellFSMmod53.out (pellFSMmod53.run (k + 54))
      = pellFSMmod53.out (pellFSMmod53.run k)
  rw [pellFSMmod53_run_period_54]

set_option maxRecDepth 2048 in
/-- ★★★★★ Pell mod-53 signature has period 54 (TIGHT, even). -/
theorem pellFSMmod53_signature_period_54 :
    ∀ k, signature pellFSMmod53.bits (k + 54)
        = signature pellFSMmod53.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod53.bits 54
    pellFSMmod53_bits_period_54 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod53

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod59

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 59. -/
def pellFSMmod59 : ArithFSM2 59 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 59, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 59, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-59 run cycles with TIGHT period 29. -/
theorem pellFSMmod59_run_period_29 :
    ∀ k, pellFSMmod59.run (k + 29) = pellFSMmod59.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod59.step (pellFSMmod59.run (k' + 29))
        = pellFSMmod59.step (pellFSMmod59.run k')
    rw [ih]

/-- ★★★★ Pell mod-59 bits cycle with TIGHT period 29. -/
theorem pellFSMmod59_bits_period_29 :
    ∀ k, pellFSMmod59.bits (k + 29) = pellFSMmod59.bits k := by
  intro k
  show pellFSMmod59.out (pellFSMmod59.run (k + 29))
      = pellFSMmod59.out (pellFSMmod59.run k)
  rw [pellFSMmod59_run_period_29]

/-- Bipartite parity doubling: bit period 29 odd ⇒ predicted 58. -/
theorem pellFSMmod59_bits_period_58 :
    ∀ k, pellFSMmod59.bits (k + 58) = pellFSMmod59.bits k := by
  intro k
  have h1 := pellFSMmod59_bits_period_29 (k + 29)
  have h2 := pellFSMmod59_bits_period_29 k
  have hreshape : k + 58 = (k + 29) + 29 := rfl
  rw [hreshape, h1, h2]

set_option maxRecDepth 2048 in
/-- ★★★★★ Pell mod-59 signature has period 58 (TIGHT, doubled). -/
theorem pellFSMmod59_signature_period_58 :
    ∀ k, signature pellFSMmod59.bits (k + 58)
        = signature pellFSMmod59.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod59.bits 58
    pellFSMmod59_bits_period_58 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod59

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod61

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 61. -/
def pellFSMmod61 : ArithFSM2 61 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 61, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 61, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-61 run cycles with TIGHT period 30. -/
theorem pellFSMmod61_run_period_30 :
    ∀ k, pellFSMmod61.run (k + 30) = pellFSMmod61.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod61.step (pellFSMmod61.run (k' + 30))
        = pellFSMmod61.step (pellFSMmod61.run k')
    rw [ih]

/-- ★★★★ Pell mod-61 bits cycle with TIGHT period 30. -/
theorem pellFSMmod61_bits_period_30 :
    ∀ k, pellFSMmod61.bits (k + 30) = pellFSMmod61.bits k := by
  intro k
  show pellFSMmod61.out (pellFSMmod61.run (k + 30))
      = pellFSMmod61.out (pellFSMmod61.run k)
  rw [pellFSMmod61_run_period_30]

set_option maxRecDepth 2048 in
/-- ★★★★★ Pell mod-61 signature has period 30 (TIGHT, even). -/
theorem pellFSMmod61_signature_period_30 :
    ∀ k, signature pellFSMmod61.bits (k + 30)
        = signature pellFSMmod61.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod61.bits 30
    pellFSMmod61_bits_period_30 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod61

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod67

open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)


def pellFSMmod67 : ArithFSM2 67 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 67, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 67, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 2048 in
theorem pellFSMmod67_run_period_68 :
    ∀ k, pellFSMmod67.run (k + 68) = pellFSMmod67.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod67.step (pellFSMmod67.run (k' + 68))
        = pellFSMmod67.step (pellFSMmod67.run k')
    rw [ih]

theorem pellFSMmod67_bits_period_68 :
    ∀ k, pellFSMmod67.bits (k + 68) = pellFSMmod67.bits k := by
  intro k
  show pellFSMmod67.out (pellFSMmod67.run (k + 68))
      = pellFSMmod67.out (pellFSMmod67.run k)
  rw [pellFSMmod67_run_period_68]

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod67

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod71

open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)


def pellFSMmod71 : ArithFSM2 71 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 71, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 71, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 1024 in
theorem pellFSMmod71_run_period_35 :
    ∀ k, pellFSMmod71.run (k + 35) = pellFSMmod71.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod71.step (pellFSMmod71.run (k' + 35))
        = pellFSMmod71.step (pellFSMmod71.run k')
    rw [ih]

theorem pellFSMmod71_bits_period_35 :
    ∀ k, pellFSMmod71.bits (k + 35) = pellFSMmod71.bits k := by
  intro k
  show pellFSMmod71.out (pellFSMmod71.run (k + 35))
      = pellFSMmod71.out (pellFSMmod71.run k)
  rw [pellFSMmod71_run_period_35]

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod71

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod73

open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)


def pellFSMmod73 : ArithFSM2 73 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 73, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 73, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 2048 in
theorem pellFSMmod73_run_period_74 :
    ∀ k, pellFSMmod73.run (k + 74) = pellFSMmod73.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod73.step (pellFSMmod73.run (k' + 74))
        = pellFSMmod73.step (pellFSMmod73.run k')
    rw [ih]

theorem pellFSMmod73_bits_period_74 :
    ∀ k, pellFSMmod73.bits (k + 74) = pellFSMmod73.bits k := by
  intro k
  show pellFSMmod73.out (pellFSMmod73.run (k + 74))
      = pellFSMmod73.out (pellFSMmod73.run k)
  rw [pellFSMmod73_run_period_74]

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod73

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod79

open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)


def pellFSMmod79 : ArithFSM2 79 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 79, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 79, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 1024 in
theorem pellFSMmod79_run_period_39 :
    ∀ k, pellFSMmod79.run (k + 39) = pellFSMmod79.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod79.step (pellFSMmod79.run (k' + 39))
        = pellFSMmod79.step (pellFSMmod79.run k')
    rw [ih]

theorem pellFSMmod79_bits_period_39 :
    ∀ k, pellFSMmod79.bits (k + 39) = pellFSMmod79.bits k := by
  intro k
  show pellFSMmod79.out (pellFSMmod79.run (k + 39))
      = pellFSMmod79.out (pellFSMmod79.run k)
  rw [pellFSMmod79_run_period_39]

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod79

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod89

open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)


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

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod89

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod101

open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)


def pellFSMmod101 : ArithFSM2 101 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 101, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 101, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

set_option maxRecDepth 1024 in
theorem pellFSMmod101_run_period_25 :
    ∀ k, pellFSMmod101.run (k + 25) = pellFSMmod101.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod101.step (pellFSMmod101.run (k' + 25))
        = pellFSMmod101.step (pellFSMmod101.run k')
    rw [ih]

theorem pellFSMmod101_bits_period_25 :
    ∀ k, pellFSMmod101.bits (k + 25) = pellFSMmod101.bits k := by
  intro k
  show pellFSMmod101.out (pellFSMmod101.run (k + 25))
      = pellFSMmod101.out (pellFSMmod101.run k)
  rw [pellFSMmod101_run_period_25]

theorem pellFSMmod101_bits_period_50 :
    ∀ k, pellFSMmod101.bits (k + 50) = pellFSMmod101.bits k := by
  intro k
  have h1 := pellFSMmod101_bits_period_25 (k + 25)
  have h2 := pellFSMmod101_bits_period_25 k
  have hreshape : k + 50 = (k + 25) + 25 := rfl
  rw [hreshape, h1, h2]

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod101
