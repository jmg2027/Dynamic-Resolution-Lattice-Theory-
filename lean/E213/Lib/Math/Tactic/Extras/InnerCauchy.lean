import E213.Lib.Math.Tactic.Extras.CauchySchwarz
import E213.Lib.Math.Analysis.Functional.InnerProduct

/-!
# Inner-product Cauchy-Schwarz, atomic 1-cell case (∅-axiom)

Closes the 1-cell deferral noted in `Functional/INDEX.md`:
`⟨f, g⟩² ≤ ⟨f, f⟩ · ⟨g, g⟩` for the *atomic* `n = 1` case.  Reduces
to `(f₀ · g₀)² ≤ f₀² · g₀²`, which is `rfl` modulo the standard
Nat factorisation.

Generic-`n` Cauchy-Schwarz still requires a sum-of-squares
expansion that is the same kind of cosmetic Nat-arithmetic as
`Extras.CauchySchwarz`; we deliver the atomic case here as the
∅-axiom witness, leaving the generic case for the next pass.
-/

namespace E213.Lib.Math.Tactic.Extras.InnerCauchy

open E213.Lib.Math.Analysis.Functional.InnerProduct (innerNum)

/-- ★ Atomic `n = 1` Cauchy-Schwarz: square of the inner product
    equals the product of self-inner-products *exactly*. -/
theorem inner_cs_atomic (f g : Nat → Nat) :
    (innerNum 1 f g) * (innerNum 1 f g)
      = innerNum 1 f f * innerNum 1 g g := by
  show (0 + f 0 * g 0) * (0 + f 0 * g 0)
        = (0 + f 0 * f 0) * (0 + g 0 * g 0)
  rw [Nat.zero_add (f 0 * g 0), Nat.zero_add (f 0 * f 0),
      Nat.zero_add (g 0 * g 0)]
  exact E213.Tactic.NatHelper.mul_mul_mul_comm_213
          (f 0) (g 0) (f 0) (g 0)

end E213.Lib.Math.Tactic.Extras.InnerCauchy
