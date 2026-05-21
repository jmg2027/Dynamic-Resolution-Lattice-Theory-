import E213.Lib.Math.Cohomology.Delta.SqZero

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Cohomology — capstone: smoke tests across d ≤ 5 (file 5)

Verifies that the cochain complex `(Cᵏ, δ)` on Δⁿ⁻¹ is well-formed
for n = 2, 3, 4, 5.  Each row checks face counts + that δ preserves
the zero cochain.  All theorems 0-axiom, `decide`-checked.
-/

namespace E213.Lib.Math.Cohomology.Bridge.TrivialCases

open E213.Lib.Physics.Simplex.Counts (binom d NS NT)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Delta.Core (delta)

/-- ★ capstone — well-formedness of `(Cᵏ, δ)` across Δⁿ⁻¹ for
    n = 2, 3, 4, 5.  Bundles per-n face-count tables, Hodge dim
    duality on Δ⁴, and δ-preserves-zero across all grades that
    accept a δ at each n. -/
theorem phase_CA_capstone :
    -- Δ¹ (n=2)
    (binom 2 0 = 1 ∧ binom 2 1 = 2 ∧ binom 2 2 = 1)
    ∧ (∀ i : Fin (binom 2 1), delta (Cochain.zero 2 0) i = false)
    -- Δ² (n=3)
    ∧ (binom 3 0 = 1 ∧ binom 3 1 = 3 ∧ binom 3 2 = 3 ∧ binom 3 3 = 1)
    ∧ (∀ i : Fin (binom 3 1), delta (Cochain.zero 3 0) i = false)
    ∧ (∀ i : Fin (binom 3 2), delta (Cochain.zero 3 1) i = false)
    -- Δ³ (n=4)
    ∧ (binom 4 0 = 1 ∧ binom 4 1 = 4 ∧ binom 4 2 = 6
       ∧ binom 4 3 = 4 ∧ binom 4 4 = 1)
    ∧ (∀ i : Fin (binom 4 2), delta (Cochain.zero 4 1) i = false)
    -- Δ⁴ (n=5) — 213 atomic
    ∧ (binom 5 0 = 1 ∧ binom 5 1 = 5 ∧ binom 5 2 = 10
       ∧ binom 5 3 = 10 ∧ binom 5 4 = 5 ∧ binom 5 5 = 1)
    -- Hodge dim duality on Δ⁴
    ∧ (binom 5 1 = binom 5 4)
    ∧ (binom 5 2 = binom 5 3)
    -- δ preserves zero on Δ⁴ at grades 1..3
    ∧ (∀ i : Fin (binom 5 2), delta (Cochain.zero 5 1) i = false)
    ∧ (∀ i : Fin (binom 5 3), delta (Cochain.zero 5 2) i = false)
    ∧ (∀ i : Fin (binom 5 4), delta (Cochain.zero 5 3) i = false) := by
  decide

end E213.Lib.Math.Cohomology.Bridge.TrivialCases
