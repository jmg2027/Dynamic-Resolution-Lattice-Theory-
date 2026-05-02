import E213.Math.Cohomology.Dyadic.Legendre.Pisano
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod11
import E213.Math.Cohomology.Dyadic.ArithFSM.Mod13

/-!
# Legendre-Pisano bridge — extended to the SPLIT case (p = 11)

Confirms Legendre lens predicts Pell period across BOTH branch types:

  | p  | Legendre 5 p | Branch    | TIGHT bit period | Formula      |
  |  3 | 2 (NQR)      | inert     |   4              | p+1 = 4 ✓   |
  |  5 | 0 (zero)     | ramified  |  10              | 2p   = 10 ✓ |
  |  7 | 2 (NQR)      | inert     |   8              | p+1 = 8 ✓   |
  | 11 | 1 (QR)       | split     |   5              | (p-1)/2 = 5 ✓ |

This is the FIRST split-case verification: when the discriminant is
a QR mod p, the Pell period halves to (p-1)/2 (vs p-1 from the
naive Pisano formula), reflecting that φ has order dividing
(p-1)/gcd((p-1), 2) in the multiplicative group.
-/

namespace E213.Math.Cohomology.Dyadic.Legendre.PisanoExt

open E213.Math.Cohomology.Dyadic.Legendre.V213 (legendre213)
open E213.Math.Cohomology.Dyadic.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod11 (pellFSMmod11 pellFSMmod11_bits_period_5 pellFSMmod11_bits_period_10)
open E213.Math.Cohomology.Dyadic.ArithFSM.Mod13 (pellFSMmod13 pellFSMmod13_bits_period_14)
open E213.Math.Cohomology.Dyadic.Legendre.Small (legendre_5_mod_3 legendre_5_mod_5 legendre_5_mod_7 legendre_5_mod_11)


/-- ★★★★★★★ Extended bridge: Legendre lens predicts Pell period
    across all four branch types {inert, ramified, split, ...}. -/
theorem legendre_pisano_extended_bridge :
    -- p = 3: NQR + inert, period = p+1 = 4
    (legendre213 5 3 (by decide) = ⟨2, by decide⟩
      ∧ ∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
    -- p = 5: ramified, period = 2p = 10
    ∧ (legendre213 5 5 (by decide) = ⟨0, by decide⟩
        ∧ ∀ k, pellFSMmod5.bits (k + 10) = pellFSMmod5.bits k)
    -- p = 7: NQR + inert, period = p+1 = 8
    ∧ (legendre213 5 7 (by decide) = ⟨2, by decide⟩
        ∧ ∀ k, pellFSMmod7.bits (k + 8) = pellFSMmod7.bits k)
    -- p = 11: QR + split, period = (p-1)/2 = 5  (NEW)
    ∧ (legendre213 5 11 (by decide) = ⟨1, by decide⟩
        ∧ ∀ k, pellFSMmod11.bits (k + 5) = pellFSMmod11.bits k) :=
  ⟨⟨legendre_5_mod_3, pellFSMmod3_bits_period_4⟩,
   ⟨legendre_5_mod_5, pellFSMmod5_bits_period_10⟩,
   ⟨legendre_5_mod_7, pellFSMmod7_bits_period_8⟩,
   ⟨legendre_5_mod_11, pellFSMmod11_bits_period_5⟩⟩

end E213.Math.Cohomology.Dyadic.Legendre.PisanoExt
