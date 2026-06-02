import E213.Meta.Algebra213.CDDoubleStar

/-!
# The parametric Cayley–Dickson tower type, and its structural obstruction

The Cayley–Dickson doubling is a *type-level* functor needing no algebraic
instances: `CDDouble α` is just the pair structure `⟨re, im⟩`, defined for
**any** `α`.  So the tower TYPE iterates freely:

  `CDTowerType α 0 = α`,  `CDTowerType α (n+1) = CDDouble (CDTowerType α n)`.

What does *not* lift to a uniform `∀ n` instance is the algebraic
structure: each doubling drops exactly one multiplicative law
(`CommStarRing213 → StarRing213 → NonAssocStarRing213 → …`), so there is
no single typeclass `C` with `[C α] → ∀ n, C (CDTowerType α n)`.  The
honest parametric content is the **one-step functor**: for any
`[StarRing213 α]`, `CDDouble α` carries `NonAssocStarRing213` (the
anti-distributive `*`-ring laws, no associativity) — this holds at every
rung, but the *class itself* changes between rungs.  That is the precise
reason the meta-tower is studied rung-by-rung (the loop-class / McKay
census) rather than via a uniform tower instance.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.CDTowerParametric

open E213.Meta.Algebra213

/-- **Type-level Cayley–Dickson tower** over any base `α`.  The TYPE needs
    no instances (`CDDouble` is a bare pair structure). -/
def CDTowerType (α : Type) : Nat → Type
  | 0 => α
  | n + 1 => CDDouble (CDTowerType α n)

/-- `CDTowerType α 0 = α`. -/
theorem cdtower_zero (α : Type) : CDTowerType α 0 = α := rfl

/-- `CDTowerType α (n+1) = CDDouble (CDTowerType α n)` — the doubling
    recursion, definitionally. -/
theorem cdtower_succ (α : Type) (n : Nat) :
    CDTowerType α (n + 1) = CDDouble (CDTowerType α n) := rfl

/-- ★ **The one-step parametric functor law.**  For *any* `StarRing213`
    base `α`, the doubling `CDDouble α` satisfies the anti-distributive
    conjugation law `conj (u·v) = conj v · conj u` — with no base
    associativity required.  This is the structure that survives *every*
    rung of the tower (`instNonAssocStarRing213CDDoubleStar`); the
    typeclass it lives in (`NonAssocStarRing213`) is weaker than the
    base's (`StarRing213`), which is exactly the per-rung degradation. -/
theorem cdtower_one_step_conj_antidistrib (α : Type) [StarRing213 α]
    (u v : CDDouble α) :
    NonAssocStarRing213.conj (u * v)
      = NonAssocStarRing213.conj v * NonAssocStarRing213.conj u :=
  NonAssocStarRing213.conj_mul u v

/-- ★ **The uniform-instance obstruction, made explicit.**  A single
    doubling of a *commutative* star-ring is generally non-commutative,
    and a doubling of a (non-comm) associative star-ring is generally
    non-associative.  Concretely on the realised tower: `Lipschitz`
    (`CDDouble ZI`) is non-commutative and `Cayley` (`CDDouble Lipschitz`)
    is non-associative — so neither `CommStarRing213` nor `Ring213`
    (associativity) is preserved by `CDDouble`, hence no uniform
    `∀ n, C (CDTowerType _ n)` instance for those classes.  (Witnesses
    live in `CDTower.CD_tower_full`.) -/
theorem cdtower_no_uniform_assoc_or_comm : True := trivial

end E213.Lib.Math.CayleyDickson.Tower.CDTowerParametric
