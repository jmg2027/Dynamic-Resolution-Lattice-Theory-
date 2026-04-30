import E213.Math.Cohomology.DyadicPellProperSmall

/-!
# Pell proper Legendre-Pisano bridge (D = 8)

Confirms that the Legendre lens with discriminant 8 predicts
the Pell-proper Pisano period across both branch types:

  | p | (8/p) Legendre | Branch | TIGHT period | Predicted |
  | 3 |  2 (NQR)       | inert  |     8        | 2(p+1) = 8  |
  | 5 |  2 (NQR)       | inert  |    12        | 2(p+1) = 12 |
  | 7 |  1 (QR)        | split  |     6        | p-1    = 6  |

All three predictions exactly match.  This demonstrates that
the Legendre-Pisano framework is *parametric* in the discriminant
— same lens infrastructure works for D = 5 (Pell-Fibonacci-squared)
and D = 8 (Pell proper).
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- ★★★★★ Legendre 8 mod 3 = NQR. -/
theorem legendre_8_mod_3 :
    legendre213 8 3 (by omega) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 8 mod 5 = NQR. -/
theorem legendre_8_mod_5 :
    legendre213 8 5 (by omega) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 8 mod 7 = QR (8 ≡ 1 mod 7). -/
theorem legendre_8_mod_7 :
    legendre213 8 7 (by omega) = ⟨1, by decide⟩ := by decide

/-- ★★★★★★ pisano_predict_proper matches TIGHT Pell proper periods. -/
theorem pisano_predict_proper_correct :
    pisano_predict_proper 3 (by omega) = 8
    ∧ pisano_predict_proper 5 (by omega) = 12
    ∧ pisano_predict_proper 7 (by omega) = 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ Pell proper Legendre-Pisano bridge — both branch types. -/
theorem pellProper_legendre_bridge :
    -- p = 3: inert, period 8 = 2(p+1)
    (legendre213 8 3 (by omega) = ⟨2, by decide⟩
      ∧ ∀ k, (pellProperFSMmod 3 (by omega)).run (k + 8)
          = (pellProperFSMmod 3 (by omega)).run k)
    -- p = 5: inert, period 12 = 2(p+1)
    ∧ (legendre213 8 5 (by omega) = ⟨2, by decide⟩
        ∧ ∀ k, (pellProperFSMmod 5 (by omega)).run (k + 12)
            = (pellProperFSMmod 5 (by omega)).run k)
    -- p = 7: split, period 6 = p-1
    ∧ (legendre213 8 7 (by omega) = ⟨1, by decide⟩
        ∧ ∀ k, (pellProperFSMmod 7 (by omega)).run (k + 6)
            = (pellProperFSMmod 7 (by omega)).run k) :=
  ⟨⟨legendre_8_mod_3, pellProper3_run_period_8⟩,
   ⟨legendre_8_mod_5, pellProper5_run_period_12⟩,
   ⟨legendre_8_mod_7, pellProper7_run_period_6⟩⟩

end E213.Math.Cohomology.DyadicConjecture
