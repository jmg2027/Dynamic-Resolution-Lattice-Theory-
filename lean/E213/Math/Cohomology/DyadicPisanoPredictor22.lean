import E213.Math.Cohomology.DyadicPisanoPredictor20
import E213.Math.Cohomology.DyadicArithFSMmod79
import E213.Math.Cohomology.DyadicArithFSMmod89

/-!
# Pisano predictor — 22-prime evidence + sub-tight pattern

Extends 20-prime Pell-5 predictor (commit 81919aa) to 22 primes.

  | p  | leg | branch | tight | predict | match  |
  | 79 |  1  | split  |  39   |   39    | TIGHT  |
  | 89 |  1  | split  |  22   |   44    | ×2 SUB |  ← NEW

★ Third ×2 sub-tight case (after p=29, p=47) ★

Sub-tight history (3 of 22):
  p=29 (split, ×2): tight 7,  predict 14
  p=47 (inert, ×3): tight 16, predict 48
  p=89 (split, ×2): tight 22, predict 44

Pattern: split ×2 sub-tight at p ∈ {29, 89, 101, ...}
        inert ×3 sub-tight at p ∈ {47, ...}

Frobenius-orbit interpretation: predictor is upper bound, tight
period coincides iff no Frobenius-stable proper subgroup.
-/

namespace E213.Math.Cohomology.DyadicConjecture

theorem legendre_5_mod_79 :
    legendre213 5 79 (by omega) = ⟨1, by decide⟩ := by decide

theorem legendre_5_mod_89 :
    legendre213 5 89 (by omega) = ⟨1, by decide⟩ := by decide

end E213.Math.Cohomology.DyadicConjecture
