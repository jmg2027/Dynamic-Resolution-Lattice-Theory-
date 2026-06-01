import E213.Lib.Math.Padic.Valuation
import E213.Lib.Math.Cohomology.Fractal.ConfigCount

/-!
# Real213-p-adic ↔ configCount bridge

The 5-adic Real213 (`ZpSeq 5`) gives base-5 expansions whose
truncations connect to the parametric configuration-count family
`configCount n` (`Fractal/ConfigCount.lean`).  The identity
`configCount 2 = 5^25` is a bare arithmetic theorem; no fractal
level is privileged and no level is a "resolution limit".

This file records level-25 instances of the general truncation
bound `(x : ZpSeq 5).trunc n < 5^n`.

## Results

  · Every 5-adic integer truncated at level 25 lies in `[0, 5^25)`
    (the level-25 instance of the parametric bound)
  · The 5-adic zero / one satisfy the corresponding truncation /
    valuation facts at level 25
  · `configCount 2 = 5^25` as a bare arithmetic identity
-/

namespace E213.Lib.Math.Padic.DRLTIntegration

open E213.Lib.Math.Padic (ZpSeq)
open E213.Lib.Math.Padic.Valuation (vAt vAt_zero vAt_one_pos)

/-! ## 5-adic level-25 truncation lives in [0, 5^25) -/

/-- ★★★★ **Every 5-adic integer's level-25 truncation is below 5^25**.

  For any `x : ZpSeq 5`, `x.trunc 25 < 5^25`.  This is the
  level-25 instance of the parametric bound `x.trunc n < 5^n`;
  `5^25` here is `configCount 2` as bare arithmetic, no level
  privileged. -/
theorem trunc_25_lt_config2 (x : ZpSeq 5) :
    x.trunc 25 < 5^25 :=
  ZpSeq.trunc_lt_p_pow (by decide) x 25

/-! ## Canonical 5-adic instances at level 25 -/

/-- The 5-adic zero truncated at level 25 = 0 < 5^25. -/
theorem zero_trunc_25 :
    (ZpSeq.zero 5 (by decide)).trunc 25 = 0 :=
  ZpSeq.trunc_zero 5 (by decide) 25

/-- The 5-adic one has truncation 1 at level 1 (and at all higher
    levels — but stable at 1 since rest of digits are 0). -/
theorem one_trunc_1 :
    (ZpSeq.one 5 (by decide)).trunc 1 = 1 :=
  ZpSeq.trunc_one_at_one 5 (by decide)

/-! ## 5-adic valuation at level 25 -/

/-- 5-adic zero has maximum valuation at level 25. -/
theorem vAt_zero_5adic_level_25 :
    vAt (ZpSeq.zero 5 (by decide)) 25 = 25 :=
  vAt_zero (by decide) 25

/-- 5-adic one has zero valuation at level 25. -/
theorem vAt_one_5adic_level_25 :
    vAt (ZpSeq.one 5 (by decide)) 25 = 0 :=
  vAt_one_pos (by decide) 25 (by decide)

/-! ## configCount bridge bundle -/

/-- ★★★★★ **5-adic ↔ configCount bridge at level 25**

  The Real213-p-adic framework at p = 5, evaluated at truncation
  level 25, bundles with the bare identity `configCount 2 = 5^25`:

    · Every 5-adic integer truncated at level 25 lies in [0, 5^25)
      (level-25 instance of the parametric bound)
    · Canonical 5-adic elements (zero, one) satisfy the
      corresponding truncation / valuation facts
    · The 5-adic valuation of zero at level 25 is 25

  `configCount 2 = 5^25` is a bare arithmetic theorem; no fractal
  level is privileged and level 25 is not a resolution limit. -/
theorem padic_DRLT_alignment :
    -- level-2 configuration count bridge
    E213.Lib.Math.Cohomology.Fractal.ConfigCount.configCount 2 = 5^25
    -- 5-adic truncation lives in [0, 5^25) for any sequence
    ∧ (∀ x : ZpSeq 5, x.trunc 25 < 5^25)
    -- Canonical 5-adic instances
    ∧ (ZpSeq.zero 5 (by decide)).trunc 25 = 0
    ∧ (ZpSeq.one 5 (by decide)).trunc 1 = 1
    -- Valuation alignment
    ∧ vAt (ZpSeq.zero 5 (by decide)) 25 = 25
    ∧ vAt (ZpSeq.one 5 (by decide)) 25 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact E213.Lib.Math.Cohomology.Fractal.ConfigCount.configCount_two_pow
  · intro x; exact trunc_25_lt_config2 x
  · exact zero_trunc_25
  · exact one_trunc_1
  · exact vAt_zero_5adic_level_25
  · exact vAt_one_5adic_level_25

end E213.Lib.Math.Padic.DRLTIntegration
