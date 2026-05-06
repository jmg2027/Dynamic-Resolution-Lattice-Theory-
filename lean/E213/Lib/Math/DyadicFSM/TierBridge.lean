import E213.Lib.Math.DyadicFSM.Classifier
import E213.Lib.Math.NatHelpers.NatDiv213

import E213.Lib.Math.DyadicFSM.Conjecture
import E213.Lib.Math.DyadicFSM.Signature
/-!
# Dyadic-tier bridge — K_{3,2}^{(2)} signature ↔ D2 hierarchy

D2 (`research-notes/archive/D2_complexity_class_hierarchy.md`) classifies
213 numbers into 3 tiers: FSM (rationals + algebraic — Pell-style
modular state), ICT (e, π — Cauchy modulus, no FSM), Power-set
(non-computable, outside framework).

This file connects the K_{3,2}^{(2)} signature classifier to that
hierarchy via the *eventually-periodic* abstraction.
-/

namespace E213.Lib.Math.DyadicFSM.TierBridge

open E213.Lib.Math.DyadicFSM.Signature (signature nextVertex)
open E213.Lib.Math.DyadicFSM.Classifier (signature_periodic_implies_bits_periodic)
open E213.Lib.Math.DyadicFSM.Conjecture (periodicBit)

/-- Eventually periodic: from some pre-period N onward, period p. -/
def EventuallyPeriodic {α : Type} (f : Nat → α) (p : Nat) : Prop :=
  0 < p ∧ ∃ N, ∀ n, n ≥ N → f (n + p) = f n

/-- ★★★ Eventually-periodic signature ⇒ eventually-periodic bits. -/
theorem ev_periodic_sig_imp_ev_periodic_bits
    (bs : Nat → Bool) (p : Nat)
    (h : EventuallyPeriodic (signature bs) p) :
    EventuallyPeriodic bs p := by
  obtain ⟨hp, N, hN⟩ := h
  refine ⟨hp, N, ?_⟩
  exact signature_periodic_implies_bits_periodic bs p N hp hN

/-- Contrapositive — aperiodic bits ⇒ aperiodic signature
    (any pre-period N, any period p). -/
theorem aperiodic_bits_imp_aperiodic_sig
    (bs : Nat → Bool)
    (h : ∀ p N : Nat, 0 < p → ∃ n, n ≥ N ∧ bs (n + p) ≠ bs n)
    (p : Nat) :
    ¬ EventuallyPeriodic (signature bs) p := by
  rintro ⟨hp, N, hN⟩
  obtain ⟨n, hn, hne⟩ := h p N hp
  exact hne (signature_periodic_implies_bits_periodic bs p N hp hN n hn)

/-! ## Concrete forward direction via simpler bit-stream form.

    Use `bit13 k := k % 2 == 1` (the 1/3 dyadic pattern) directly,
    bypassing periodicBit's dependent-if form. -/

/-- 1/3 dyadic bit pattern: 0,1,0,1,... -/
def bit13 (k : Nat) : Bool := k % 2 == 1

/-- STRICT ∅-AXIOM via 213-native add_mod_right_pos. -/
theorem bit13_period_2 (k : Nat) : bit13 (k + 2) = bit13 k := by
  show ((k + 2) % 2 == 1) = (k % 2 == 1)
  rw [E213.Lib.Math.NatHelpers.NatDiv213.add_mod_right_pos (by decide : 0 < 2) k]

/-- ★ Concrete forward: 1/3 signature has period 2 from step 1.
    STRICT ∅-AXIOM (no omega). -/
theorem one_third_signature_periodic :
    ∀ n, n ≥ 1 → signature bit13 (n + 2) = signature bit13 n := by
  intro n hn
  induction n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ n' ih =>
    by_cases h : n' = 0
    · subst h; decide
    · have hn' : n' ≥ 1 := Nat.pos_of_ne_zero h
      have ih' : signature bit13 (n' + 2) = signature bit13 n' := ih hn'
      have hbs_eq : bit13 (n' + 2) = bit13 n' := bit13_period_2 n'
      have h_idx : n' + 1 + 2 = n' + 2 + 1 := Nat.succ_add n' 2
      rw [h_idx]
      show nextVertex (signature bit13 (n' + 2)) (bit13 (n' + 2))
        = nextVertex (signature bit13 n') (bit13 n')
      rw [ih', hbs_eq]

/-! ## Connection to D2 hierarchy (statements; proofs deferred)

| D2 Tier | Bit stream | K_{3,2}^{(2)} signature |
|---------|-----------|-------------------------|
| Tier 0 (rationals) | eventually periodic | EVENTUALLY PERIODIC |
| Tier 1 (algebraic, √2 etc.) | aperiodic | aperiodic, but with
   bounded *trajectory complexity* (FSM joint state) |
| Tier 2 (transcendentals e, π) | aperiodic | aperiodic, with
   *unbounded* trajectory complexity |
| Tier 3 (non-computable) | not extractable | undefined |

**Key open conjecture** (G1 §5 follow-up):
For Tier 1 vs Tier 2, the signature complexity (entropy / Kolmogorov)
distinguishes them — Tier 1 has bounded complexity per bit
(joint Pell-state × K_{3,2}^{(2)} state), Tier 2 has growing
complexity (factorial trajectory in HasModulus's N(m, k)).

**Forward direction (deferred — pigeonhole)**:
  bs eventually periodic ⇒ signature eventually periodic.
Proof: joint state (sig n, n mod p) has 5p values; pigeonhole
forces a cycle within ≤ 5p+1 steps after pre-period N.
(Available via `OS.Pigeonhole.no_inj_lt`; full formalisation
is the natural next step.) -/

end E213.Lib.Math.DyadicFSM.TierBridge
