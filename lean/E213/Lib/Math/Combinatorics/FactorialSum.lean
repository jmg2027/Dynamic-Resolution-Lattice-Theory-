import E213.Lib.Math.Combinatorics.Permutations
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Meta.Nat.PolyNatMTactic

/-!
# Factorial telescoping identity `Σ k·k! = (n+1)! − 1` (∅-axiom)

`Σ_{k=0}^{n} k·k! = (n+1)! − 1`, in the subtraction-free shift form
`Σ_{k=0}^{n} k·k! + 1 = (n+1)!` (`fact_telescope`).  A clean telescoping
induction (`(k+1)! − k! = k·k!`) reusing the corpus factorial
(`Permutations.fact`) and `sumTo`.  Genuinely absent.
-/

namespace E213.Lib.Math.Combinatorics.FactorialSum

open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)

/-- ★ **Factorial telescoping**: `Σ_{k=0}^{n} k·k! + 1 = (n+1)!`. -/
theorem fact_telescope (n : Nat) :
    sumTo (n + 1) (fun k => k * fact k) + 1 = fact (n + 1) := by
  induction n with
  | zero => decide
  | succ m ih =>
      rw [sumTo_succ (m + 1) (fun k => k * fact k)]
      have hreg :
          (sumTo (m + 1) (fun k => k * fact k) + (m + 1) * fact (m + 1)) + 1
            = (sumTo (m + 1) (fun k => k * fact k) + 1) + (m + 1) * fact (m + 1) := by
        ring_nat
      rw [hreg, ih]
      show fact (m + 1) + (m + 1) * fact (m + 1) = (m + 2) * fact (m + 1)
      ring_nat

end E213.Lib.Math.Combinatorics.FactorialSum
