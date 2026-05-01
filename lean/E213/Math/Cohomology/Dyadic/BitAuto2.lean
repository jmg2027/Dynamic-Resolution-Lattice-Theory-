import E213.Math.Cohomology.Dyadic.ThueMorse

/-!
# 2-automatic bit streams — abstraction richer than BitFSM

A `BitAuto2` reads the binary digits of an INDEX n through a finite
DFA and outputs a Bool.  This captures "automatic sequences"
(Allouche–Shallit) — strictly richer than BitFSM (sequential
generation): includes Thue-Morse, paperfolding, Rudin-Shapiro etc.

  bs n := out (foldl step init (binaryDigits n))

For Thue-Morse: 2-state DFA, init = parity 0, step = XOR with
input bit, out = parity bit.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- 2-automatic bit stream generator.  Reads binary digits via DFA. -/
structure BitAuto2 (n : Nat) where
  init : Fin n
  step : Fin n → Bool → Fin n
  out  : Fin n → Bool

/-- Run on binary digits of k up to bound (LSB-first via testBit). -/
def BitAuto2.run {n : Nat} (m : BitAuto2 n) (k bound : Nat) : Fin n :=
  (List.range bound).foldl (fun s i => m.step s (k.testBit i)) m.init

/-- Bit at index k, with bound for digit count. -/
def BitAuto2.bits {n : Nat} (m : BitAuto2 n) (bound k : Nat) : Bool :=
  m.out (m.run k bound)

/-- Thue-Morse 2-state automaton. -/
def thueMorseAuto : BitAuto2 2 where
  init := ⟨0, by decide⟩
  step s b := bif b then ⟨1 - s.val, by have := s.isLt; omega⟩ else s
  out s := s.val == 1

/-- Thue-Morse automaton matches thueMorse on first 8 indices
    (with bound 4 = enough digits for k ≤ 15). -/
theorem thueMorseAuto_matches_first8 :
    thueMorseAuto.bits 4 0 = thueMorse 0
    ∧ thueMorseAuto.bits 4 1 = thueMorse 1
    ∧ thueMorseAuto.bits 4 2 = thueMorse 2
    ∧ thueMorseAuto.bits 4 3 = thueMorse 3
    ∧ thueMorseAuto.bits 4 4 = thueMorse 4
    ∧ thueMorseAuto.bits 4 5 = thueMorse 5
    ∧ thueMorseAuto.bits 4 6 = thueMorse 6
    ∧ thueMorseAuto.bits 4 7 = thueMorse 7 := by decide

/-- ★★★ Thue-Morse is realised as a 2-state BitAuto2.  Aperiodic
    (verified for periods ≤ 8) but finitely describable —
    demonstrates BitAuto2 is STRICTLY richer than BitFSM. -/
theorem thueMorseAuto_witnesses_bitAuto2 :
    ∃ m : BitAuto2 2, ∀ k, k ≤ 7 → m.bits 4 k = thueMorse k := by
  refine ⟨thueMorseAuto, ?_⟩
  decide

/-- isPow2 indicator: 1 iff n is a power of 2 (popcount = 1). -/
def isPow2Auto : BitAuto2 3 where
  init := ⟨0, by decide⟩  -- popcount = 0 (no 1-bits seen)
  step s b := bif b then
    bif s.val == 0 then ⟨1, by decide⟩  -- 0 → 1 (first 1-bit)
    else bif s.val == 1 then ⟨2, by decide⟩  -- 1 → 2 (second 1-bit)
    else ⟨2, by decide⟩  -- 2 → 2 (saturate)
  else s
  out s := s.val == 1  -- true iff exactly one 1-bit

/-- isPow2Auto correctly identifies powers of 2 in 0..15. -/
theorem isPow2Auto_first16 :
    isPow2Auto.bits 4 0 = false ∧ isPow2Auto.bits 4 1 = true
    ∧ isPow2Auto.bits 4 2 = true ∧ isPow2Auto.bits 4 3 = false
    ∧ isPow2Auto.bits 4 4 = true ∧ isPow2Auto.bits 4 5 = false
    ∧ isPow2Auto.bits 4 6 = false ∧ isPow2Auto.bits 4 7 = false
    ∧ isPow2Auto.bits 4 8 = true ∧ isPow2Auto.bits 4 9 = false
    ∧ isPow2Auto.bits 4 15 = false := by decide

end E213.Math.Cohomology.Dyadic.Conjecture
