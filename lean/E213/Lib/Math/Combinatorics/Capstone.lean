import E213.Lib.Math.Combinatorics.Binomial
import E213.Lib.Math.Combinatorics.Catalan
import E213.Lib.Math.Combinatorics.Stirling
import E213.Lib.Math.Combinatorics.GeneratingFunction

/-!
# Combinatorics 213 — Capstone synthesis

Four cluster witnesses + total bundle, all `#print axioms` ∅.
-/

namespace E213.Lib.Math.Combinatorics.Capstone

open E213.Lib.Math.Combinatorics.Catalan (catalan)
open E213.Lib.Math.Combinatorics.Stirling (stirling2 bell)
open E213.Lib.Math.Combinatorics.GeneratingFunction (one xVar)
open E213.Lib.Physics.Simplex.Counts (binom)

/-- ★ **Binomial witness** ★ — Pascal's row 5 = (1, 5, 10, 10, 5, 1). -/
theorem binomial_witness :
    binom 5 0 = 1 ∧ binom 5 1 = 5 ∧ binom 5 2 = 10
    ∧ binom 5 3 = 10 ∧ binom 5 4 = 5 ∧ binom 5 5 = 1 := by decide

/-- ★ **Catalan witness** ★ — C₅ = 42. -/
theorem catalan_witness :
    catalan 0 = 1 ∧ catalan 1 = 1 ∧ catalan 2 = 2
    ∧ catalan 3 = 5 ∧ catalan 4 = 14 ∧ catalan 5 = 42 := by decide

/-- ★ **Stirling witness** ★ — Bell decomposition into Stirling sums. -/
theorem stirling_witness :
    bell 4 = stirling2 4 1 + stirling2 4 2 + stirling2 4 3 + stirling2 4 4 :=
  by decide

/-- ★ **Generating-function witness** ★ — basic series at low orders. -/
theorem gf_witness :
    one 0 = 1 ∧ xVar 1 = 1 ∧ xVar 0 = 0 := ⟨rfl, rfl, rfl⟩

/-- ★★★ **Total witness** ★★★ — 4-fact grand bundle. -/
theorem total_witness :
    binom 5 5 = 1
    ∧ catalan 5 = 42
    ∧ bell 5 = 52
    ∧ one 0 = 1 := by decide

end E213.Lib.Math.Combinatorics.Capstone
