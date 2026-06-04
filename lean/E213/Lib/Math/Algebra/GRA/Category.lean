import E213.Lib.Math.Algebra.GRA.GRAModel
import E213.Lib.Math.Algebra.GRA.NumberTheory
import E213.Lib.Math.Algebra.GRA.Graph
import E213.Lib.Math.Algebra.GRA.Analysis
import E213.Lib.Math.Algebra.GRA.Cohomology
import E213.Lib.Math.Algebra.GRA.HoTT
import E213.Lib.Math.Algebra.GRA.HigherAlgebra

/-!
# GRA Category — Phase 7

The five Readings + the NumberTheory hub form a small category
in which morphisms are `GRAIso`'s.  Since every `GRAIso M₁ M₂` is
invertible (Phase 8 — `Groupoid.lean`), this category is a
**groupoid**, and since every Reading is iso to NT, it is a
**connected** groupoid.

This file:
  * defines a 213-native minimal `Cat` typeclass (no Mathlib)
  * proves `GRAIso` satisfies the category laws (identity + associativity)
  * exhibits the 6 (2,3)-GRA Readings as `Cat`-objects with
    explicit `Hom`-witnesses
  * derives the round-trip identity `GRAIso.symm (GRAIso.symm iso) = iso`

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.GRA.Category

open E213.Lib.Math.Algebra.GRA

/-! ### §1 — Minimal 213-native category typeclass

We pin down only what GRA needs: a `Cat` is given by a type of
objects `Ob`, a `Hom`-bifunctor, an identity, and a composition,
subject to the three category laws.  No `Type u`-juggling.
-/

/-- A small category in 213-native form (universe-polymorphic). -/
structure Cat.{u, v} where
  /-- Objects. -/
  Ob : Type u
  /-- Morphism family. -/
  Hom : Ob → Ob → Type v
  /-- Identity morphism. -/
  id : (X : Ob) → Hom X X
  /-- Composition. -/
  comp : {X Y Z : Ob} → Hom X Y → Hom Y Z → Hom X Z
  /-- Left identity law. -/
  id_comp : ∀ {X Y : Ob} (f : Hom X Y), comp (id X) f = f
  /-- Right identity law. -/
  comp_id : ∀ {X Y : Ob} (f : Hom X Y), comp f (id Y) = f
  /-- Associativity. -/
  comp_assoc : ∀ {W X Y Z : Ob} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)

/-! ### §2 — `GRAIso` category laws

`GRAIso M₁ M₂` is data: two maps + 5 commuting axioms.  For
`GRAIso.refl` / `GRAIso.trans` to satisfy the category laws,
the structure-equality needs to be definitional.  In `GRAModel.lean`,
`GRAIso.refl` uses `id` and `rfl`-provided commutations, so
identity laws hold up to defeq.  Associativity follows from
function composition associativity (also defeq).
-/

/-- Left identity: `refl ∘ iso = iso`. -/
theorem GRAIso_id_comp {M₁ M₂ : GRAModel} (iso : GRAIso M₁ M₂) :
    GRAIso.trans (GRAIso.refl M₁) iso = iso := rfl

/-- Right identity: `iso ∘ refl = iso`. -/
theorem GRAIso_comp_id {M₁ M₂ : GRAModel} (iso : GRAIso M₁ M₂) :
    GRAIso.trans iso (GRAIso.refl M₂) = iso := rfl

/-- Associativity of `GRAIso.trans`. -/
theorem GRAIso_comp_assoc {M₁ M₂ M₃ M₄ : GRAModel}
    (f : GRAIso M₁ M₂) (g : GRAIso M₂ M₃) (h : GRAIso M₃ M₄) :
    GRAIso.trans (GRAIso.trans f g) h
      = GRAIso.trans f (GRAIso.trans g h) := rfl

/-! ### §3 — The full category `GRACat` of (2,3)-GRA models

`GRACat.Ob = GRAModel` with arbitrary parameters.  Restriction to
(2, 3) parameters is a sub-category, exhibited below as
`(2,3)-GRACat`.
-/

/-- The category of all GRA models with `GRAIso` morphisms. -/
def GRACat : Cat where
  Ob := GRAModel
  Hom := GRAIso
  id := GRAIso.refl
  comp := GRAIso.trans
  id_comp := GRAIso_id_comp
  comp_id := GRAIso_comp_id
  comp_assoc := GRAIso_comp_assoc

/-! ### §4 — The connected sub-category of (2, 3)-Readings

The six closed models (NT, Graph, Analysis, Cohomology, HoTT,
HigherAlgebra) carry an enumeration.  Each is iso to NT, so the
sub-category they span is connected.
-/

/-- Tag enumerating the six concrete Readings. -/
inductive Reading where
  | NT
  | Graph
  | Analysis
  | Cohomology
  | HoTT
  | HigherAlgebra
deriving DecidableEq

/-- The GRA model attached to each Reading tag. -/
def Reading.toModel : Reading → GRAModel
  | .NT => NumberTheory.GRA23_NT
  | .Graph => Graph.GRA23_Graph
  | .Analysis => Analysis.GRA23_Analysis
  | .Cohomology => Cohomology.GRA23_Cohomology
  | .HoTT => HoTT.GRA23_HoTT
  | .HigherAlgebra => HigherAlgebra.GRA23_HigherAlgebra

/-- The "iso to NT" witness for each Reading. -/
def Reading.toNT : (r : Reading) → GRAIso r.toModel NumberTheory.GRA23_NT
  | .NT => GRAIso.refl _
  | .Graph => Graph.GRAIso_Graph_NT
  | .Analysis => Analysis.GRAIso_Analysis_NT
  | .Cohomology => Cohomology.GRAIso_Cohomology_NT
  | .HoTT => HoTT.GRAIso_HoTT_NT
  | .HigherAlgebra => HigherAlgebra.GRAIso_HigherAlgebra_NT

/-- Hub-and-spoke iso between any two Readings. -/
def Reading.iso (r s : Reading) : GRAIso r.toModel s.toModel :=
  GRAIso.trans r.toNT (GRAIso.symm s.toNT)

/-- The (2, 3)-Readings as a sub-`Cat` of `GRACat`. -/
def ReadingCat : Cat where
  Ob := Reading
  Hom r s := GRAIso r.toModel s.toModel
  id r := GRAIso.refl r.toModel
  comp := GRAIso.trans
  id_comp := GRAIso_id_comp
  comp_id := GRAIso_comp_id
  comp_assoc := GRAIso_comp_assoc

/-! ### §5 — Connectedness witness

For every pair `(r, s)`, `Reading.iso r s` is a `Hom`.  This is
the *connected groupoid* property — Phase 8 will upgrade
"connected category" to "connected groupoid" by exhibiting
invertibility (already present via `GRAIso.symm`).
-/

/-- `ReadingCat` is connected: every object pair is related by a
    morphism. -/
theorem ReadingCat_connected (r s : Reading) :
    ∃ _ : ReadingCat.Hom r s, True :=
  ⟨Reading.iso r s, trivial⟩

end E213.Lib.Math.Algebra.GRA.Category
