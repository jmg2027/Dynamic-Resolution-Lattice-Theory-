import E213.Term.Tactic.QuadNorm

/-!
# Tests: `quad_norm` on Diophantus-style identities

Imports only the tactic; verifies the macro independently of
the slow Raw.lean build (compiles in seconds).

The tests target exactly the polynomial-identity shape used by
`Math/CayleyDickson/{ZIDomain,ZSqrt2Domain}.normSq_mul`.  Other polynomial
identities (e.g. expansions like `(a+b)² = a²+2ab+b²`) are NOT
in `quad_norm`'s intended scope — `omega`'s atom-handling for
constant multipliers `2*x` differs from constant binding
`a*(b*2)` after simp normalisation.
-/

open E213.Tactic

/-- Gaussian-integer Diophantus identity (ZI norm). -/
example (a b c d : Int) :
    (a*c - b*d)*(a*c - b*d) + (a*d + b*c)*(a*d + b*c)
  = (a*a + b*b) * (c*c + d*d) := by quad_norm

/-- `ℤ[√-2]` Diophantus identity (Z2 norm with factor 2). -/
example (a b c d : Int) :
    (a*c - 2*(b*d))*(a*c - 2*(b*d))
      + 2*((a*d + b*c)*(a*d + b*c))
  = (a*a + 2*(b*b)) * (c*c + 2*(d*d)) := by quad_norm
