import E213.Lib.Math.Modulus.HasModulus

/-!
# Real213: framework-internal Real number type

*Type-level* formulation of Cauchy completeness:
real number = (sequence + modulus) pair.

## Definition

`Real213 := { xs : Nat → Raw // ∃ N : Nat → Nat → Nat, ... }`

Each element = constructive Cauchy sequence with explicit modulus.
Reified form of HasModulus.

## Significance

- Type definition of *constructive ℝ* within the 213 framework.
- No external axioms (inherits axiom-free property of HasModulus).
- Equivalence relation: two sequences produce the same limit decision
  at *every (m, k) cut*.

## Blocked point

Equivalence relation + quotient — Lean's quotient depends on Quot.sound.
Workaround: setoid-style approach or raw subtype.
-/

namespace E213.Lib.Math.Real213.Core.Core

open E213.Theory E213.Lens
open E213.Lib.Math.Modulus.HasModulus

/-- Constructive Cauchy real: sequence + explicit modulus. -/
structure Real213 where
  xs : Nat → Raw
  modulus : HasModulus xs

/-- Two reals are equivalent if they have same eventual orderProj
    decisions at every (m, k) threshold. -/
def Real213.equiv (r r' : Real213) : Prop :=
  ∀ m k, k ≥ 1 →
    ∃ N, ∀ i, i ≥ N →
      E213.Lib.Math.Cauchy.Archimedean.orderProj m k
        (E213.Lens.Instances.AB.abLens.view (r.xs i)) =
      E213.Lib.Math.Cauchy.Archimedean.orderProj m k
        (E213.Lens.Instances.AB.abLens.view (r'.xs i))

end E213.Lib.Math.Real213.Core.Core
