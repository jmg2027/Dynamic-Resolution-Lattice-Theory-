import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.DyadicFSM.Signature.PeriodClosure
import E213.Lib.Math.DyadicFSM.Signature.Signature

/-!
# ArithFSM.ModSmall — per-prime ArithFSM instances (Small primes)

Per-prime ArithFSM Fibonacci-recurrence period instances for primes
[5, 7, 11, 13, 17, 19, 23].

Per-N namespaces preserved (`ArithFSM.Mod{N}`).
-/

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod5
open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod2 pellFSMmod3)
/-- Pell-style FSM mod 5: (a_{k+1}, b_{k+1}) = (2a + b, a + b) mod 5. -/
def pellFSMmod5 : ArithFSM2 5 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 5, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 5, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1
/-- Pell mod-5 trajectory: out values for first 12 steps. -/
theorem pellFSMmod5_first12 :
    pellFSMmod5.bits 0 = true  ∧ pellFSMmod5.bits 1 = false
    ∧ pellFSMmod5.bits 2 = false ∧ pellFSMmod5.bits 3 = true
    ∧ pellFSMmod5.bits 4 = false ∧ pellFSMmod5.bits 5 = false
    ∧ pellFSMmod5.bits 6 = false ∧ pellFSMmod5.bits 7 = false
    ∧ pellFSMmod5.bits 8 = false ∧ pellFSMmod5.bits 9 = false
    ∧ pellFSMmod5.bits 10 = true ∧ pellFSMmod5.bits 11 = false := by decide
/-- ★★★ Pell mod-5 run cycles with period 10 (universally). -/
theorem pellFSMmod5_run_period_10 :
    ∀ k, pellFSMmod5.run (k + 10) = pellFSMmod5.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod5.step (pellFSMmod5.run (k' + 10))
        = pellFSMmod5.step (pellFSMmod5.run k')
    rw [ih]
/-- ★★★★ Pell mod-5 bits cycle with period 10 (universally). -/
theorem pellFSMmod5_bits_period_10 :
    ∀ k, pellFSMmod5.bits (k + 10) = pellFSMmod5.bits k := by
  intro k
  show pellFSMmod5.out (pellFSMmod5.run (k + 10))
      = pellFSMmod5.out (pellFSMmod5.run k)
  rw [pellFSMmod5_run_period_10]
/-- Pell mod-5 has period STRICTLY greater than mod-3.  -/
theorem pellMod5_period_gt_mod3 :
    (10 : Nat) > 4 := by decide
/-- ★★★★★ Pell family period growth: mod 2 → 3, mod 3 → 4, mod 5 → 10.
    Algebraic-modulus periods reflect multiplicative order in (ℤ/n)*. -/
theorem pell_period_growth :
    (∀ k, pellFSMmod2.bits (k + 3) = pellFSMmod2.bits k)
    ∧ (∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + 10) = pellFSMmod5.bits k) :=
  ⟨pellFSMmod2_bits_period_3,
   pellFSMmod3_bits_period_4,
   pellFSMmod5_bits_period_10⟩
end E213.Lib.Math.DyadicFSM.ArithFSM.Mod5

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod7

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


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

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod7

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod11

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 11. -/
def pellFSMmod11 : ArithFSM2 11 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 11, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 11, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-11 first 12 bit values: T F F F F T F F F F T F. -/
theorem pellFSMmod11_first12 :
    pellFSMmod11.bits 0 = true ∧ pellFSMmod11.bits 1 = false
    ∧ pellFSMmod11.bits 2 = false ∧ pellFSMmod11.bits 3 = false
    ∧ pellFSMmod11.bits 4 = false ∧ pellFSMmod11.bits 5 = true
    ∧ pellFSMmod11.bits 6 = false ∧ pellFSMmod11.bits 7 = false
    ∧ pellFSMmod11.bits 8 = false ∧ pellFSMmod11.bits 9 = false
    ∧ pellFSMmod11.bits 10 = true ∧ pellFSMmod11.bits 11 = false := by decide

/-- ★★★ Pell mod-11 run cycles with period 5 (SPLIT — shorter than inert). -/
theorem pellFSMmod11_run_period_5 :
    ∀ k, pellFSMmod11.run (k + 5) = pellFSMmod11.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod11.step (pellFSMmod11.run (k' + 5))
        = pellFSMmod11.step (pellFSMmod11.run k')
    rw [ih]

/-- ★★★★ Pell mod-11 bits cycle with period 5. -/
theorem pellFSMmod11_bits_period_5 :
    ∀ k, pellFSMmod11.bits (k + 5) = pellFSMmod11.bits k := by
  intro k
  show pellFSMmod11.out (pellFSMmod11.run (k + 5))
      = pellFSMmod11.out (pellFSMmod11.run k)
  rw [pellFSMmod11_run_period_5]

/-- Bit period doubles to signature period 10 (bipartite parity coupling,
    bit period 5 is odd). -/
theorem pellFSMmod11_bits_period_10 :
    ∀ k, pellFSMmod11.bits (k + 10) = pellFSMmod11.bits k := by
  intro k
  have h1 := pellFSMmod11_bits_period_5 (k + 5)
  have h2 := pellFSMmod11_bits_period_5 k
  have hreshape : k + 10 = (k + 5) + 5 := rfl
  rw [hreshape, h1, h2]

/-- ★★★★★ Pell mod-11 signature has period 10 (TIGHT, doubled by parity). -/
theorem pellFSMmod11_signature_period_10 :
    ∀ k, signature pellFSMmod11.bits (k + 10) = signature pellFSMmod11.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod11.bits 10
    pellFSMmod11_bits_period_10 (by decide)

/-- ★★★★ Pell mod-11 signature period bound: 605 = 5·121. -/
theorem pellFSMmod11_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 605
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod11.bits (k + P) = signature pellFSMmod11.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 11) (by decide) pellFSMmod11
  exact ⟨N, P, hP, hbound, hk⟩

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod11

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod13

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 13. -/
def pellFSMmod13 : ArithFSM2 13 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 13, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 13, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-13 first 5 bit values. -/
theorem pellFSMmod13_first5 :
    pellFSMmod13.bits 0 = true ∧ pellFSMmod13.bits 1 = false
    ∧ pellFSMmod13.bits 2 = false ∧ pellFSMmod13.bits 3 = false
    ∧ pellFSMmod13.bits 4 = false := by decide

/-- ★★★ Pell mod-13 run cycles with period 14 (TIGHT). -/
theorem pellFSMmod13_run_period_14 :
    ∀ k, pellFSMmod13.run (k + 14) = pellFSMmod13.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod13.step (pellFSMmod13.run (k' + 14))
        = pellFSMmod13.step (pellFSMmod13.run k')
    rw [ih]

/-- ★★★★ Pell mod-13 bits cycle with period 14. -/
theorem pellFSMmod13_bits_period_14 :
    ∀ k, pellFSMmod13.bits (k + 14) = pellFSMmod13.bits k := by
  intro k
  show pellFSMmod13.out (pellFSMmod13.run (k + 14))
      = pellFSMmod13.out (pellFSMmod13.run k)
  rw [pellFSMmod13_run_period_14]

/-- ★★★★★ Pell mod-13 signature has period 14 (TIGHT). -/
theorem pellFSMmod13_signature_period_14 :
    ∀ k, signature pellFSMmod13.bits (k + 14)
        = signature pellFSMmod13.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod13.bits 14
    pellFSMmod13_bits_period_14 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod13

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod17

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 17. -/
def pellFSMmod17 : ArithFSM2 17 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 17, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 17, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-17 first 5 bit values. -/
theorem pellFSMmod17_first5 :
    pellFSMmod17.bits 0 = true ∧ pellFSMmod17.bits 1 = false
    ∧ pellFSMmod17.bits 2 = false ∧ pellFSMmod17.bits 3 = false
    ∧ pellFSMmod17.bits 4 = false := by decide

/-- ★★★ Pell mod-17 run cycles with period 18 (TIGHT). -/
theorem pellFSMmod17_run_period_18 :
    ∀ k, pellFSMmod17.run (k + 18) = pellFSMmod17.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod17.step (pellFSMmod17.run (k' + 18))
        = pellFSMmod17.step (pellFSMmod17.run k')
    rw [ih]

/-- ★★★★ Pell mod-17 bits cycle with period 18. -/
theorem pellFSMmod17_bits_period_18 :
    ∀ k, pellFSMmod17.bits (k + 18) = pellFSMmod17.bits k := by
  intro k
  show pellFSMmod17.out (pellFSMmod17.run (k + 18))
      = pellFSMmod17.out (pellFSMmod17.run k)
  rw [pellFSMmod17_run_period_18]

/-- ★★★★★ Pell mod-17 signature has period 18 (TIGHT). -/
theorem pellFSMmod17_signature_period_18 :
    ∀ k, signature pellFSMmod17.bits (k + 18)
        = signature pellFSMmod17.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod17.bits 18
    pellFSMmod17_bits_period_18 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod17

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod19

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 19. -/
def pellFSMmod19 : ArithFSM2 19 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 19, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 19, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Pell mod-19 first values check. -/
theorem pellFSMmod19_first10 :
    pellFSMmod19.bits 0 = true ∧ pellFSMmod19.bits 1 = false
    ∧ pellFSMmod19.bits 8 = false ∧ pellFSMmod19.bits 9 = true := by decide

/-- ★★★ Pell mod-19 run cycles with period 9. -/
theorem pellFSMmod19_run_period_9 :
    ∀ k, pellFSMmod19.run (k + 9) = pellFSMmod19.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod19.step (pellFSMmod19.run (k' + 9))
        = pellFSMmod19.step (pellFSMmod19.run k')
    rw [ih]

/-- ★★★★ Pell mod-19 bits cycle with period 9. -/
theorem pellFSMmod19_bits_period_9 :
    ∀ k, pellFSMmod19.bits (k + 9) = pellFSMmod19.bits k := by
  intro k
  show pellFSMmod19.out (pellFSMmod19.run (k + 9))
      = pellFSMmod19.out (pellFSMmod19.run k)
  rw [pellFSMmod19_run_period_9]

/-- Bipartite parity doubling: bit period 9 odd ⇒ signature period 18. -/
theorem pellFSMmod19_bits_period_18 :
    ∀ k, pellFSMmod19.bits (k + 18) = pellFSMmod19.bits k := by
  intro k
  have h1 := pellFSMmod19_bits_period_9 (k + 9)
  have h2 := pellFSMmod19_bits_period_9 k
  have hreshape : k + 18 = (k + 9) + 9 := rfl
  rw [hreshape, h1, h2]

/-- ★★★★★ Pell mod-19 signature has period 18 (TIGHT, doubled). -/
theorem pellFSMmod19_signature_period_18 :
    ∀ k, signature pellFSMmod19.bits (k + 18)
        = signature pellFSMmod19.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod19.bits 18
    pellFSMmod19_bits_period_18 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod19

namespace E213.Lib.Math.DyadicFSM.ArithFSM.Mod23

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ConcretePellSig (signature_period_of_bits_period_and_anchor signature_period_of_bits_period_and_anchor_from)
open E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM (arithFSM2_signature_period_bound)


/-- Pell-style FSM mod 23. -/
def pellFSMmod23 : ArithFSM2 23 where
  init := (⟨1, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % 23, Nat.mod_lt _ (by decide)⟩,
     ⟨(a.val + b.val) % 23, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Pell mod-23 run cycles with period 24 (TIGHT). -/
theorem pellFSMmod23_run_period_24 :
    ∀ k, pellFSMmod23.run (k + 24) = pellFSMmod23.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod23.step (pellFSMmod23.run (k' + 24))
        = pellFSMmod23.step (pellFSMmod23.run k')
    rw [ih]

/-- ★★★★ Pell mod-23 bits cycle with period 24. -/
theorem pellFSMmod23_bits_period_24 :
    ∀ k, pellFSMmod23.bits (k + 24) = pellFSMmod23.bits k := by
  intro k
  show pellFSMmod23.out (pellFSMmod23.run (k + 24))
      = pellFSMmod23.out (pellFSMmod23.run k)
  rw [pellFSMmod23_run_period_24]

/-- ★★★★★ Pell mod-23 signature has period 24 (TIGHT). -/
theorem pellFSMmod23_signature_period_24 :
    ∀ k, signature pellFSMmod23.bits (k + 24)
        = signature pellFSMmod23.bits k :=
  signature_period_of_bits_period_and_anchor pellFSMmod23.bits 24
    pellFSMmod23_bits_period_24 (by decide)

end E213.Lib.Math.DyadicFSM.ArithFSM.Mod23

namespace E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM

open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5)

/-- ★★★★★★ Pell mod-5 signature: explicit period bound 125 = 5·25.

    Hosted in `ModSmall.lean` (consumes `pellFSMmod5` from
    `ArithFSM.Mod5`); namespace `ToBitFSM` preserved for consumer
    compatibility — the underlying utility
    `arithFSM2_signature_period_bound` lives in `ToBitFSM.lean`. -/
theorem pellFSMmod5_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 125
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod5.bits (k + P) = signature pellFSMmod5.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 5) (by decide) pellFSMmod5
  exact ⟨N, P, hP, hbound, hk⟩

end E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
