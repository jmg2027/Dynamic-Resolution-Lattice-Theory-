import E213.Lib.Math.Cauchy.Archimedean

/-!
# HasModulus: Constructive Cauchy modulus typeclass

Canonical Bishop-style infrastructure bypassing the LEM-bound
`∀ (m, k), ∃ N` closure from PAPER1 §6.4: an explicit modulus
is required as *data*.

## Core

`HasModulus xs`: typeclass embedding of an explicit
N : Nat → Nat → Nat (per-(m, k) modulus) for the sequence
`xs : Nat → Raw`.  Once data is provided, isOrderCauchy is
derived without LEM.

## Significance

- The canonical constructive-analysis pattern where the *sequence
  supplier also provides the modulus* (Bishop 1967).
- `HasModulus → isOrderCauchy` holds trivially — possessing the
  typeclass is the mechanical replacement for bypassing LEM.
- Concrete instances (Pell, Euler, Wallis) are future work; constructing
  the explicit N function for each is non-trivial (Pell: closed form
  via bound y_n ≥ k iff n ≥ k; Euler/Wallis: irrationality of e/π/2
  must be elevated to a framework-internal lemma — separate arc).
-/

namespace E213.Lib.Math.Modulus.HasModulus

open E213.Theory E213.Lens
open E213.Lens.Instances.AB
open E213.Lib.Math.Cauchy.Archimedean

/-- **Constructive Cauchy modulus**: carries the stabilization of
    orderProj as data via an explicit per-(m, k) modulus N.
    The canonical pattern of Bishop-style constructive analysis. -/
structure HasModulus (xs : Nat → Raw) where
  N : Nat → Nat → Nat
  cauchy_at : ∀ m k, k ≥ 1 → ∀ i j, i ≥ N m k → j ≥ N m k →
    orderProj m k (abLens.view (xs i)) = orderProj m k (abLens.view (xs j))

/-- **Modulus implies isOrderCauchy** — trivial extraction. -/
theorem isOrderCauchy_of_hasModulus (xs : Nat → Raw)
    (h : HasModulus xs) : isOrderCauchy xs := by
  intro m k hk
  exact ⟨h.N m k, h.cauchy_at m k hk⟩

end E213.Lib.Math.Modulus.HasModulus
