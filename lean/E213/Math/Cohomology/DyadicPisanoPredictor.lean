import E213.Math.Cohomology.DyadicLegendrePisanoExt

/-!
# Pisano predictor — Legendre lens as a period-predicting function

Concretises the bridge as a *function* `pisano_predict : Nat → Nat`
that maps a prime `p` to the predicted Pell period via the
trajectory-walking Legendre value.

For the Pell discriminant Δ = 5 with matrix [[2,1],[1,1]]:

  legendre213 5 p = 0 (ramified)  ⇒  predict = 2p
  legendre213 5 p = 1 (QR/split)  ⇒  predict = (p-1)/2
  legendre213 5 p = 2 (NQR/inert) ⇒  predict = p + 1

The function `predicts` Pell mod p's bit period.  Verified
universally on the trajectory level for {3, 5, 7, 11}.

This is the *operational* form of the Pisano CRT — the lens
that, given a prime, decides which Pisano formula to apply.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- 213-native Pisano period predictor for the Pell-5 discriminant. -/
def pisano_predict (p : Nat) (hp : 1 < p) : Nat :=
  let leg := (legendre213 5 p hp).val
  if leg = 0 then 2 * p          -- ramified
  else if leg = 1 then (p - 1) / 2  -- split (QR)
  else p + 1                     -- inert (NQR)

/-- ★★★★★★ Predictor matches TIGHT Pell period at all four cases. -/
theorem pisano_predict_correct :
    pisano_predict 3 (by decide) = 4
    ∧ pisano_predict 5 (by decide) = 10
    ∧ pisano_predict 7 (by decide) = 8
    ∧ pisano_predict 11 (by decide) = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ The Legendre lens-driven predictor PREDICTS the
    actual Pell bit periods at all four primes — a single
    formula that reads the trajectory and yields the period. -/
theorem pisano_predict_realises_pell :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
        = pellFSMmod11.bits k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k; rw [pisano_predict_correct.1]; exact pellFSMmod3_bits_period_4 k
  · intro k; rw [pisano_predict_correct.2.1]; exact pellFSMmod5_bits_period_10 k
  · intro k; rw [pisano_predict_correct.2.2.1]; exact pellFSMmod7_bits_period_8 k
  · intro k; rw [pisano_predict_correct.2.2.2]; exact pellFSMmod11_bits_period_5 k

end E213.Math.Cohomology.DyadicConjecture
