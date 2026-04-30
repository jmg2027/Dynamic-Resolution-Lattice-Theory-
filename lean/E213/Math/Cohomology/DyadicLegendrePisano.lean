import E213.Math.Cohomology.DyadicLegendreSmall
import E213.Math.Cohomology.DyadicArithFSMmod7
import E213.Math.Cohomology.DyadicPellFamily

/-!
# Legendre lens ↔ Pisano period bridge

The 213-native Legendre value `legendre213 5 p` predicts the Pell
period type:

  Legendre = 1 (split, QR):    π(p) | p - 1
  Legendre = 2 (inert, NQR):   π(p) | p + 1 (×2 for parity)
  Legendre = 0 (ramified):     π(p) special, p = 5

For the discriminant Δ = 5 of the Pell matrix [[2,1],[1,1]],
we observe:

  | p  | (5/p) Legendre | TIGHT period | Predicted formula |
  |  3 |  2 (NQR/inert) |     4        | p + 1 = 4         |
  |  5 |  0 (ramified)  |    10        | 2p = 10           |
  |  7 |  2 (NQR/inert) |     8        | p + 1 = 8         |

All three primes confirm the Pisano-style branch law via the
trajectory-walking Legendre lens.  No external number theory used.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★★ Bridge: at p ∈ {3, 7} (NQR, inert), the Pell period
    matches the inert formula p + 1.  At p = 5 (ramified), the
    period matches 2p.  The Legendre lens *predicts* the Pell
    period via trajectory branch law. -/
theorem legendre_pisano_bridge_table :
    -- p = 3: NQR + inert, period = p+1 = 4
    (legendre213 5 3 (by omega) = ⟨2, by decide⟩
      ∧ ∀ k, pellFSMmod3.bits (k + (3 + 1)) = pellFSMmod3.bits k)
    -- p = 5: ramified, period = 2p = 10
    ∧ (legendre213 5 5 (by omega) = ⟨0, by decide⟩
        ∧ ∀ k, pellFSMmod5.bits (k + (2 * 5)) = pellFSMmod5.bits k)
    -- p = 7: NQR + inert, period = p+1 = 8
    ∧ (legendre213 5 7 (by omega) = ⟨2, by decide⟩
        ∧ ∀ k, pellFSMmod7.bits (k + (7 + 1)) = pellFSMmod7.bits k) := by
  refine ⟨⟨legendre_5_mod_3, ?_⟩, ⟨legendre_5_mod_5, ?_⟩,
          ⟨legendre_5_mod_7, ?_⟩⟩
  · intro k
    have h : (3 : Nat) + 1 = 4 := by decide
    rw [h]; exact pellFSMmod3_bits_period_4 k
  · intro k
    have h : (2 : Nat) * 5 = 10 := by decide
    rw [h]; exact pellFSMmod5_bits_period_10 k
  · intro k
    have h : (7 : Nat) + 1 = 8 := by decide
    rw [h]; exact pellFSMmod7_bits_period_8 k

end E213.Math.Cohomology.DyadicConjecture
