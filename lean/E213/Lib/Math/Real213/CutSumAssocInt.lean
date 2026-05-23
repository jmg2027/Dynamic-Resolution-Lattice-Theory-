import E213.Lib.Math.Real213.Sum.CutSumEq
import E213.Lib.Math.Real213.Sum.CutSumOne
/-!
# cutSum associativity for integer cuts (precision-bounded rigor)

The general `cutSum_assoc` is blocked by the precision-doubling
artifact (`cutSum (cutSum cx cy) cz` reads cx at precision 4k vs
`cutSum cx (cutSum cy cz)` reads cx at 2k).  But for the **integer
cut class** `constCut a 1`, the associativity holds by Nat-level
addition associativity, factored through `cutSum_int_int`.

  `cutSum (cutSum (constCut a 1) (constCut b 1)) (constCut c 1)`
    cutEq
  `cutSum (constCut a 1) (cutSum (constCut b 1) (constCut c 1))`

Both sides reduce to `constCut (a + b + c) 1` via `cutSum_int_int`.

Higher-precision (b ≥ 2) associativity remains open due to
precision artifacts; the integer-class result is the rigor stake.

All declarations PURE.
-/

namespace E213.Lib.Math.Real213.CutSumAssocInt

open E213.Lib.Math.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Sum.CutSumEq
  (cutSum_cutEq_left cutSum_cutEq_right)
open E213.Lib.Math.Real213.Sum.CutSumOne (cutSum_int_int)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-! ## §1 — Integer-cut associativity (cutEq form) -/

/-- ★★★ **cutSum associativity for integer cuts**:
    `(a + b) + c = a + (b + c)` lifts to cutSum at constCut · 1. -/
theorem cutSum_assoc_int (a b c : Nat) :
    cutEq (cutSum (cutSum (constCut a 1) (constCut b 1)) (constCut c 1))
          (cutSum (constCut a 1)
                  (cutSum (constCut b 1) (constCut c 1))) := by
  intro m k
  -- LHS: rewrite inner cutSum to constCut (a+b) 1
  rw [cutSum_cutEq_left
        (cutSum (constCut a 1) (constCut b 1))
        (constCut (a+b) 1)
        (constCut c 1)
        (cutSum_int_int a b) m k]
  -- LHS = cutSum (constCut (a+b) 1) (constCut c 1) m k
  --     = constCut ((a+b)+c) 1 m k
  rw [cutSum_int_int (a+b) c m k]
  -- RHS: rewrite inner cutSum to constCut (b+c) 1
  rw [cutSum_cutEq_right
        (constCut a 1)
        (cutSum (constCut b 1) (constCut c 1))
        (constCut (b+c) 1)
        (cutSum_int_int b c) m k]
  -- RHS = cutSum (constCut a 1) (constCut (b+c) 1) m k
  --     = constCut (a+(b+c)) 1 m k
  rw [cutSum_int_int a (b+c) m k]
  -- Need: constCut ((a+b)+c) 1 m k = constCut (a+(b+c)) 1 m k
  rw [Nat.add_assoc]

/-! ## §2 — Pointwise / Bool form at fixed (m, k) -/

/-- ★ Pointwise `cutSum_assoc_int` at concrete (m, k). -/
theorem cutSum_assoc_int_at (a b c m k : Nat) :
    cutSum (cutSum (constCut a 1) (constCut b 1)) (constCut c 1) m k
    = cutSum (constCut a 1)
             (cutSum (constCut b 1) (constCut c 1)) m k :=
  cutSum_assoc_int a b c m k

/-! ## §3 — Smoke at concrete values -/

/-- Smoke: associativity at `(a, b, c) = (1, 2, 3)` and `(m, k) = (0, 1)`. -/
theorem cutSum_assoc_int_smoke_1_2_3 :
    cutSum (cutSum (constCut 1 1) (constCut 2 1)) (constCut 3 1) 0 1
    = cutSum (constCut 1 1) (cutSum (constCut 2 1) (constCut 3 1)) 0 1 :=
  cutSum_assoc_int_at 1 2 3 0 1

/-- Smoke: with zero cut on the left, `(0 + b) + c = 0 + (b + c)`. -/
theorem cutSum_assoc_int_smoke_zero_left :
    cutSum (cutSum (constCut 0 1) (constCut 2 1)) (constCut 3 1) 1 2
    = cutSum (constCut 0 1) (cutSum (constCut 2 1) (constCut 3 1)) 1 2 :=
  cutSum_assoc_int_at 0 2 3 1 2

/-! ## §4 — Capstone -/

/-- ★★★★★ **cutSum associativity (integer-cut class) capstone**.

    Bundles: (a) cutEq form for arbitrary (a, b, c),
    (b) pointwise at fixed (m, k), (c) two smoke witnesses.

    Reading: the precision-doubling artifact blocks general
    cutSum_assoc, but the **integer cut class** (constCut a 1)
    admits associativity by factoring through `cutSum_int_int`
    + `Nat.add_assoc`.

    The Wave-5 trajectory-pw argument (user's observation) at the
    integer class: both `((a+b)+c)/1` and `(a+(b+c))/1` are the
    same constant cut, so all trajectories converge to the same
    endpoint distinguishing. -/
theorem cutSum_assoc_int_capstone (a b c : Nat) :
    -- (a) cutEq form
    cutEq (cutSum (cutSum (constCut a 1) (constCut b 1)) (constCut c 1))
          (cutSum (constCut a 1)
                  (cutSum (constCut b 1) (constCut c 1)))
    -- (b) Pointwise at (1, 1)
    ∧ cutSum (cutSum (constCut a 1) (constCut b 1)) (constCut c 1) 1 1
        = cutSum (constCut a 1)
                 (cutSum (constCut b 1) (constCut c 1)) 1 1
    -- (c) Smoke at concrete values
    ∧ cutSum (cutSum (constCut 1 1) (constCut 2 1)) (constCut 3 1) 0 1
        = cutSum (constCut 1 1)
                 (cutSum (constCut 2 1) (constCut 3 1)) 0 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact cutSum_assoc_int a b c
  · exact cutSum_assoc_int_at a b c 1 1
  · exact cutSum_assoc_int_smoke_1_2_3

end E213.Lib.Math.Real213.CutSumAssocInt
