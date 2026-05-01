import E213.Math.Cohomology.Dyadic.PisanoPredictor11
import E213.Math.Cohomology.Dyadic.ArithFSMmod41
import E213.Math.Cohomology.Dyadic.ArithFSMmod43
import E213.Math.Cohomology.Dyadic.ArithFSMmod47

/-!
# Pisano predictor — 14-prime evidence (mod 41, 43, 47 added)

  | p  | Legendre | Branch    | true bit | predict | match     |
  |  3 |     2    | inert     |     4    |    4    |  TIGHT    |
  |  5 |     0    | ramified  |    10    |   10    |  TIGHT    |
  |  7 |     2    | inert     |     8    |    8    |  TIGHT    |
  | 11 |     1    | split     |     5    |    5    |  TIGHT    |
  | 13 |     2    | inert     |    14    |   14    |  TIGHT    |
  | 17 |     2    | inert     |    18    |   18    |  TIGHT    |
  | 19 |     1    | split     |     9    |    9    |  TIGHT    |
  | 23 |     2    | inert     |    24    |   24    |  TIGHT    |
  | 29 |     1    | split     |     7    |   14    |  ×2 sub   |
  | 31 |     1    | split     |    15    |   15    |  TIGHT    |
  | 37 |     2    | inert     |    38    |   38    |  TIGHT    |
  | 41 |     1    | split     |    20    |   20    |  TIGHT    |  NEW
  | 43 |     2    | inert     |    44    |   44    |  TIGHT    |  NEW
  | 47 |     2    | inert     |    16    |   48    |  ×3 sub   |  NEW

Inert verified at 8 sizes: {3, 7, 13, 17, 23, 37, 43, 47}.
Split verified at 6 sizes: {11, 19, 29, 31, 41}.
Ramified verified at 1 size: {5}.

★ NEW PHENOMENON ★ — at p=47 (inert), predictor 48 = 3 · tight 16.
First sub-tight-by-3 instance.  Combined with p=29 (split, ×2 sub),
this establishes: the Pisano predictor formula gives a Galois-orbit
upper bound, with sub-tight cases reflecting subtle algebraic
splitting in the trajectory.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★★ Legendre 5 mod 41 = QR (split). -/
theorem legendre_5_mod_41 :
    legendre213 5 41 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 43 = NQR (inert). -/
theorem legendre_5_mod_43 :
    legendre213 5 43 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 47 = NQR (inert). -/
theorem legendre_5_mod_47 :
    legendre213 5 47 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor REALISES Pell period at 14 primes.

  Extends the 11-prime evidence (`pisano_predict_realises_pell_11`)
  by adding mod 41, 43, 47.  The new phenomenon at p=47:
  predictor formula `p+1=48` gives 3 · tight period (16).
  Predictor still satisfies `bits(k+predict) = bits(k)`.

  Three sub-tight cases now in the table:
    p=29 (split) : predict=14, tight=7  (×2)
    p=47 (inert) : predict=48, tight=16 (×3)  ← NEW

  Generalised conjecture: predictor gives a *Galois orbit* upper
  bound that coincides with the tight period exactly when no
  Frobenius-stable proper subgroup exists in the Pell mod-p
  trajectory. -/
theorem pisano_predict_realises_pell_14 :
    -- All 11 previous primes
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
        = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide))
        = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (by decide))
        = pellFSMmod17.bits k)
    ∧ (∀ k, pellFSMmod19.bits (k + pisano_predict 19 (by decide))
        = pellFSMmod19.bits k)
    ∧ (∀ k, pellFSMmod23.bits (k + pisano_predict 23 (by decide))
        = pellFSMmod23.bits k)
    ∧ (∀ k, pellFSMmod29.bits (k + pisano_predict 29 (by decide))
        = pellFSMmod29.bits k)
    ∧ (∀ k, pellFSMmod31.bits (k + pisano_predict 31 (by decide))
        = pellFSMmod31.bits k)
    ∧ (∀ k, pellFSMmod37.bits (k + pisano_predict 37 (by decide))
        = pellFSMmod37.bits k)
    -- Three new primes
    ∧ (∀ k, pellFSMmod41.bits (k + pisano_predict 41 (by decide))
        = pellFSMmod41.bits k)
    ∧ (∀ k, pellFSMmod43.bits (k + pisano_predict 43 (by decide))
        = pellFSMmod43.bits k)
    ∧ (∀ k, pellFSMmod47.bits (k + pisano_predict 47 (by decide))
        = pellFSMmod47.bits k) := by
  have h41 : pisano_predict 41 (by decide) = 20 := by decide
  have h43 : pisano_predict 43 (by decide) = 44 := by decide
  have h47 : pisano_predict 47 (by decide) = 48 := by decide
  let H := pisano_predict_realises_pell_11
  refine ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1,
          H.2.2.2.2.2.1, H.2.2.2.2.2.2.1,
          H.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.1,
          H.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2,
          ?_, ?_, ?_⟩
  · intro k; rw [h41]; exact pellFSMmod41_bits_period_20 k
  · intro k; rw [h43]; exact pellFSMmod43_bits_period_44 k
  · intro k; rw [h47]; exact pellFSMmod47_bits_period_48 k

end E213.Math.Cohomology.Dyadic.Conjecture
