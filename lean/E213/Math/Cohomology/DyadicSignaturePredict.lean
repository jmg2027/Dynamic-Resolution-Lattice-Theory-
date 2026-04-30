import E213.Math.Cohomology.DyadicPisanoPredictor7

/-!
# Signature-period predictor — bipartite parity doubling layer

Extends `pisano_predict` to predict signature periods (vs bit
periods).  The bipartite alternation invariant `signature` ↔
S/T parity coupling means:

  - Even bit period ⇒ signature period = bit period
  - Odd bit period  ⇒ signature period = 2 × bit period

Encoded as `signature_predict : Nat → Nat`:

  signature_predict p :=
    let bp := pisano_predict p
    if bp is even then bp else 2 * bp

Verified at all 7 primes:

  | p  | bit period | signature period | predict |
  |  3 |     4      |     4            |    4    |
  |  5 |    10      |    10            |   10    |
  |  7 |     8      |     8            |    8    |
  | 11 |     5  odd |    10  (=2·5)    |   10    |
  | 13 |    14      |    14            |   14    |
  | 17 |    18      |    18            |   18    |
  | 19 |     9  odd |    18  (=2·9)    |   18    |
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- Signature-period predictor: doubles the bit-period predictor
    when the bit period is odd (bipartite parity coupling). -/
def signature_predict (p : Nat) (hp : 1 < p) : Nat :=
  let bp := pisano_predict p hp
  if bp % 2 = 0 then bp else 2 * bp

/-- ★★★★★★ signature_predict matches actual TIGHT signature periods. -/
theorem signature_predict_correct_7 :
    signature_predict 3 (by omega) = 4
    ∧ signature_predict 5 (by omega) = 10
    ∧ signature_predict 7 (by omega) = 8
    ∧ signature_predict 11 (by omega) = 10
    ∧ signature_predict 13 (by omega) = 14
    ∧ signature_predict 17 (by omega) = 18
    ∧ signature_predict 19 (by omega) = 18 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ Signature predictor REALISES Pell signature period at
    all 7 primes (via Legendre lens trajectory). -/
theorem signature_predict_realises_pell_7 :
    (∀ k, signature pellFSMmod3.bits (k + signature_predict 3 (by omega))
        = signature pellFSMmod3.bits k)
    ∧ (∀ k, signature pellFSMmod5.bits (k + signature_predict 5 (by omega))
        = signature pellFSMmod5.bits k)
    ∧ (∀ k, signature pellFSMmod7.bits (k + signature_predict 7 (by omega))
        = signature pellFSMmod7.bits k)
    ∧ (∀ k, signature pellFSMmod11.bits (k + signature_predict 11 (by omega))
        = signature pellFSMmod11.bits k)
    ∧ (∀ k, signature pellFSMmod13.bits (k + signature_predict 13 (by omega))
        = signature pellFSMmod13.bits k)
    ∧ (∀ k, signature pellFSMmod17.bits (k + signature_predict 17 (by omega))
        = signature pellFSMmod17.bits k)
    ∧ (∀ k, signature pellFSMmod19.bits (k + signature_predict 19 (by omega))
        = signature pellFSMmod19.bits k) := by
  obtain ⟨h3, h5, h7, h11, h13, h17, h19⟩ := signature_predict_correct_7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; rw [h3]; exact pellFSMmod3_signature_period_4 k
  · intro k; rw [h5]; exact pellFSMmod5_signature_period_10 k
  · intro k; rw [h7]
    have := pellFSMmod7_signature_period_8 k; exact this
  · intro k; rw [h11]; exact pellFSMmod11_signature_period_10 k
  · intro k; rw [h13]; exact pellFSMmod13_signature_period_14 k
  · intro k; rw [h17]; exact pellFSMmod17_signature_period_18 k
  · intro k; rw [h19]; exact pellFSMmod19_signature_period_18 k

end E213.Math.Cohomology.DyadicConjecture
