import E213.Math.Cohomology.Dyadic.Legendre.Small
import E213.Math.Cohomology.Dyadic.ArithFSMmod13
import E213.Math.Cohomology.Dyadic.ArithFSMmod19
import E213.Math.Cohomology.Dyadic.Legendre.PisanoExt
import E213.Math.Cohomology.Dyadic.Pisano.Predictor

/-!
# Legendre lens at p ∈ {13, 19} + extended Pisano bridge (6 primes)

Adds two more verified primes to the bridge:
  - p = 13: NQR (inert), bit period 14 = p+1 (TIGHT)
  - p = 19: QR (split), bit period 9 = (p-1)/2

This brings the total verified count to 6 primes covering all
three branch types (inert, split, ramified) with multiple
instances each.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★★ Pell discriminant 5 is NQR mod 13 (inert). -/
theorem legendre_5_mod_13 :
    legendre213 5 13 (by omega) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Pell discriminant 5 is QR mod 19 (split). -/
theorem legendre_5_mod_19 :
    legendre213 5 19 (by omega) = ⟨1, by decide⟩ := by decide

/-- ★★★★★★★ Extended Legendre-Pisano bridge — 6 primes verified. -/
theorem legendre_pisano_6prime_bridge :
    -- p = 3: NQR/inert, period p+1 = 4
    (legendre213 5 3 (by omega) = ⟨2, by decide⟩
      ∧ ∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
    -- p = 5: ramified, period 2p = 10
    ∧ (legendre213 5 5 (by omega) = ⟨0, by decide⟩
        ∧ ∀ k, pellFSMmod5.bits (k + 10) = pellFSMmod5.bits k)
    -- p = 7: NQR/inert, period p+1 = 8
    ∧ (legendre213 5 7 (by omega) = ⟨2, by decide⟩
        ∧ ∀ k, pellFSMmod7.bits (k + 8) = pellFSMmod7.bits k)
    -- p = 11: QR/split, period (p-1)/2 = 5
    ∧ (legendre213 5 11 (by omega) = ⟨1, by decide⟩
        ∧ ∀ k, pellFSMmod11.bits (k + 5) = pellFSMmod11.bits k)
    -- p = 13: NQR/inert, period p+1 = 14  (NEW)
    ∧ (legendre213 5 13 (by omega) = ⟨2, by decide⟩
        ∧ ∀ k, pellFSMmod13.bits (k + 14) = pellFSMmod13.bits k)
    -- p = 19: QR/split, period (p-1)/2 = 9  (NEW)
    ∧ (legendre213 5 19 (by omega) = ⟨1, by decide⟩
        ∧ ∀ k, pellFSMmod19.bits (k + 9) = pellFSMmod19.bits k) :=
  ⟨⟨legendre_5_mod_3, pellFSMmod3_bits_period_4⟩,
   ⟨legendre_5_mod_5, pellFSMmod5_bits_period_10⟩,
   ⟨legendre_5_mod_7, pellFSMmod7_bits_period_8⟩,
   ⟨legendre_5_mod_11, pellFSMmod11_bits_period_5⟩,
   ⟨legendre_5_mod_13, pellFSMmod13_bits_period_14⟩,
   ⟨legendre_5_mod_19, pellFSMmod19_bits_period_9⟩⟩

end E213.Math.Cohomology.Dyadic.Conjecture
