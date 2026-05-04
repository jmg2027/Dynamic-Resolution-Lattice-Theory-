import E213.Math.CascadeCalculus

/-!
# 213 Pattern Catalog

The 213 codebase exhibits four dominant *language games*.  Survey
counts (2026-05-XX, 970 .lean files):

  | Game           | Marker                  | Frequency        |
  |----------------|-------------------------|------------------|
  | Locality       | `_at`/`_pure`/`_congr`  | 123 + 57 thms,   |
  |                |                         | 25 files         |
  | Aggregation    | `*_capstone*`           | 171 thms         |
  | Typeclass      | `structure`/`class`     | 72 + 7 decls     |
  | Catamorphism   | `Raw.fold`/`Raw.rec`    | 259 use sites    |

This file abstracts each game as a typeclass-style structure,
providing the *meta-vocabulary* for talking about 213 codebase
patterns inside 213 itself.

The four games are not orthogonal: they compose into the
**dependency-DAG / cascade-delete calculus** of `CascadeCalculus.lean`:

  - Locality nodes        ↔ leaf nodes      (most-imported)
  - Aggregation nodes     ↔ terminal nodes  (consumer-free)
  - Typeclass nodes       ↔ infrastructure  (provide fields)
  - Catamorphism morphism ↔ edges           (Raw → α direction)
-/

namespace E213.Math.PatternCatalog

open E213.Math.CascadeCalculus

/-- **Locality game**: a "global" function `f` plus a pointwise
    witness `f_at` that agrees with `f` at every test point.
    Captures `_at`/`_pure` parallel pattern. -/
structure LocalityWitness (Idx : Type) (Val : Type) where
  f      : Idx → Val
  f_at   : Idx → Val
  agrees : ∀ i, f i = f_at i

/-- **Aggregation game**: a bundle of `n` facts collected as
    Type-level conjunction.  Captures `*_capstone*` pattern.
    Concrete instances use Lean's `∧` directly; this records
    that the bundle has cardinality `n` for cataloging. -/
structure CapstoneBundle where
  arity   : Nat
  /-- Phase tag (e.g., "BA", "BH", "CM") for cross-reference. -/
  phase   : String
  deriving Repr

/-- **Typeclass game**: an interface providing two base values
    and a binary combine.  Captures the Lens `structure` pattern.
    Example instance: `Lens α` itself. -/
structure InterfaceWitness (α : Type) where
  base1   : α
  base2   : α
  combine : α → α → α

/-- **Catamorphism game**: the Raw → α direction.  Encoded as
    a function-shaped data record (no Raw dependency at this
    catalog level).  Concrete instance: `Lens.view`. -/
structure CatamorphismWitness (α : Type) where
  reduce : α → α → α
  base_a : α
  base_b : α
  /-- "View" is the catamorphism itself; abstracted as a
      function from a nat-encoded tree. -/
  view   : Nat → α

end E213.Math.PatternCatalog
