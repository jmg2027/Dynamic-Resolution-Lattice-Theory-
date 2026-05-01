import E213.Math.Cohomology.DyadicPisanoPredictor14
import E213.Math.Cohomology.DyadicArithFSMmod53
import E213.Math.Cohomology.DyadicArithFSMmod59
import E213.Math.Cohomology.DyadicArithFSMmod61

/-!
# Pisano predictor — 17-prime evidence (mod 53, 59, 61 added)

  | p  | Legendre | Branch    | true bit | predict | match |
  | 53 |     2    | inert     |    54    |   54    | TIGHT | NEW
  | 59 |     1    | split     |    29    |   29    | TIGHT | NEW
  | 61 |     1    | split     |    30    |   30    | TIGHT | NEW

All three new primes TIGHT.

Inert (9): {3, 7, 13, 17, 23, 37, 43, 47, 53}
Split (7): {11, 19, 29, 31, 41, 59, 61}
Ramified (1): {5}

Total 17 primes — current strongest empirical evidence for the
Pisano predictor's universality on the Pell-5 lens.

Sub-tight cases remain at 2 of 17:
  p=29 (split, ×2): predict 14 = 2 · tight 7
  p=47 (inert, ×3): predict 48 = 3 · tight 16
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★ Legendre 5 mod 53 = NQR (inert). -/
theorem legendre_5_mod_53 :
    legendre213 5 53 (by omega) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 59 = QR (split). -/
theorem legendre_5_mod_59 :
    legendre213 5 59 (by omega) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 61 = QR (split). -/
theorem legendre_5_mod_61 :
    legendre213 5 61 (by omega) = ⟨1, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor REALISES Pell period at 17 primes. -/
theorem pisano_predict_realises_pell_17 :
    -- All 14 previous primes
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by omega))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by omega))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by omega))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by omega))
        = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by omega))
        = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (by omega))
        = pellFSMmod17.bits k)
    ∧ (∀ k, pellFSMmod19.bits (k + pisano_predict 19 (by omega))
        = pellFSMmod19.bits k)
    ∧ (∀ k, pellFSMmod23.bits (k + pisano_predict 23 (by omega))
        = pellFSMmod23.bits k)
    ∧ (∀ k, pellFSMmod29.bits (k + pisano_predict 29 (by omega))
        = pellFSMmod29.bits k)
    ∧ (∀ k, pellFSMmod31.bits (k + pisano_predict 31 (by omega))
        = pellFSMmod31.bits k)
    ∧ (∀ k, pellFSMmod37.bits (k + pisano_predict 37 (by omega))
        = pellFSMmod37.bits k)
    ∧ (∀ k, pellFSMmod41.bits (k + pisano_predict 41 (by omega))
        = pellFSMmod41.bits k)
    ∧ (∀ k, pellFSMmod43.bits (k + pisano_predict 43 (by omega))
        = pellFSMmod43.bits k)
    ∧ (∀ k, pellFSMmod47.bits (k + pisano_predict 47 (by omega))
        = pellFSMmod47.bits k)
    -- Three new primes
    ∧ (∀ k, pellFSMmod53.bits (k + pisano_predict 53 (by omega))
        = pellFSMmod53.bits k)
    ∧ (∀ k, pellFSMmod59.bits (k + pisano_predict 59 (by omega))
        = pellFSMmod59.bits k)
    ∧ (∀ k, pellFSMmod61.bits (k + pisano_predict 61 (by omega))
        = pellFSMmod61.bits k) := by
  have h53 : pisano_predict 53 (by omega) = 54 := by decide
  have h59 : pisano_predict 59 (by omega) = 29 := by decide
  have h61 : pisano_predict 61 (by omega) = 30 := by decide
  obtain ⟨h3, h5, h7, h11, h13, h17, h19, h23, h29, h31, h37,
          h41, h43, h47⟩ := pisano_predict_realises_pell_14
  refine ⟨h3, h5, h7, h11, h13, h17, h19, h23, h29, h31, h37,
          h41, h43, h47, ?_, ?_, ?_⟩
  · intro k; rw [h53]; exact pellFSMmod53_bits_period_54 k
  · intro k; rw [h59]; exact pellFSMmod59_bits_period_29 k
  · intro k; rw [h61]; exact pellFSMmod61_bits_period_30 k

end E213.Math.Cohomology.DyadicConjecture
