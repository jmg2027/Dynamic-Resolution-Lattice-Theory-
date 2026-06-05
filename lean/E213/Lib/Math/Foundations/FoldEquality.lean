import E213.Lib.Math.Geometry.PickTheorem
import E213.Lib.Math.Algebra.CrossDomainIdentities

/-!
# The EQUIV catalog — fold-equalities, the identity axis of the proof-ISA

`ProofISALifts` catalogs the **lift** archetypes (finite → uniform).  This file is
its companion on the *other* axis: **fold-equalities** (EQUIV) — two readings of
one input give the same value.  A `FoldEquality` bundles two folds and a witness
that they agree pointwise; its difficulty is not a lift but the cost of
*constructing the second fold* (trivial here, century-hard for Weil/Langlands).
See `theory/essays/proof_isa/lifts_versus_fold_equalities.md`.

(Pointwise, not `funext`: `agree` is `∀ x, fold1 x = fold2 x`, avoiding the
`Quot.sound` that function-extensionality carries.)
-/

namespace E213.Lib.Math.Foundations.FoldEquality

open E213.Lib.Math.Geometry.PickTheorem (pickValue pick_rectangle)
open E213.Lib.Math.Algebra.CrossDomainIdentities (heron)

/-- An **EQUIV** datum: two folds `X → α` of one input that agree everywhere.
    The identity-axis analogue of a lift archetype. -/
structure FoldEquality (X : Type) (α : Type) where
  /-- one reading -/
  fold1 : X → α
  /-- a second reading (the cross-domain bridge) -/
  fold2 : X → α
  /-- the two readings coincide -/
  agree : ∀ x, fold1 x = fold2 x

/-- ★★★★★ **Pick as a fold-equality**: the lattice-point-count reading and the
    area reading of a rectangle `(w,h)` are one and the same fold. -/
def pick : FoldEquality (Int × Int) Int where
  fold1 := fun p => pickValue ((p.1 - 1) * (p.2 - 1)) (2 * p.1 + 2 * p.2)
  fold2 := fun p => 2 * (p.1 * p.2)
  agree := fun p => pick_rectangle p.1 p.2

/-- ★★★★★ **Heron as a fold-equality**: the side-product reading and the
    `16·Area²` reading of a triangle `(a,b,c)` are one fold. -/
def heronFE : FoldEquality (Int × Int × Int) Int where
  fold1 := fun p =>
    (p.1 + p.2.1 + p.2.2) * (-p.1 + p.2.1 + p.2.2)
      * (p.1 - p.2.1 + p.2.2) * (p.1 + p.2.1 - p.2.2)
  fold2 := fun p =>
    2 * (p.1 * p.1) * (p.2.1 * p.2.1) + 2 * (p.2.1 * p.2.1) * (p.2.2 * p.2.2)
      + 2 * (p.2.2 * p.2.2) * (p.1 * p.1)
      - (p.1 * p.1) * (p.1 * p.1) - (p.2.1 * p.2.1) * (p.2.1 * p.2.1)
      - (p.2.2 * p.2.2) * (p.2.2 * p.2.2)
  agree := fun p => heron p.1 p.2.1 p.2.2

/-- The EQUIV data are genuine (their two folds really do coincide) — the
    identity-axis catalog, pinned. -/
theorem equiv_catalog :
    (∀ p, pick.fold1 p = pick.fold2 p) ∧ (∀ p, heronFE.fold1 p = heronFE.fold2 p) :=
  ⟨pick.agree, heronFE.agree⟩

end E213.Lib.Math.Foundations.FoldEquality
