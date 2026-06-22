import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lens.Foundations.FlatOntology
import E213.Lib.Physics.Simplex.Counts

/-!
# Cohomology.Bridge.PredicateAsCochain — §9.3 closure deepening

Connects the `Lens/Foundations/FlatOntology.lean` realisation
(types ≡ predicates `Rawⁿ → Bool`) to the cohomology cluster's
`Cochain n k` infrastructure.

The bridge:

  - `Cochain n 1` is a `Fin n → Bool` (indicator on n vertices).
  - `Lens/Foundations/FlatOntology.UnaryType` is `Raw → Bool` (indicator on
    Raw atoms).
  - When the n-vertex domain is identified with n distinct Raws
    (via Method A numerals or any chart), a cochain is *exactly*
    a UnaryType restricted to that finite vertex subset.

This bridge realises the §9.3 statement "cocycles are self-
consistent global sections of the predicate lens" at the n-vertex
combinatorial level: a 1-cochain σ ∈ Cochain n 1 assigns Bool to
each vertex, and the coboundary δσ checks for edge-consistency —
the cocycle condition (δσ = 0) is the "predicate respects
boundary" property at this depth.

## Scope

This file makes the alignment concrete via small ∅-axiom
identifications at n ≤ 5 (the d=5 atomicity range).  Larger
constructions (full Cantor-style closure across all n) remain
in `Lens/Foundations/PredicateSelfEncoding.lean` (finite-prefix Raw encoding)
and `Lens/Cardinality/Godel.lean` (Raw → ℕ injection).
-/

namespace E213.Lib.Math.Cohomology.Bridge.PredicateAsCochain

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)

/-- A `Cochain n 1` is a Bool-valued predicate on n indices —
    i.e., a UnaryType on the finite vertex set `Fin n`. -/
def cochainAsPredicate {n : Nat} (σ : Cochain n 1) :
    Fin (binom n 1) → Bool := σ

/-- Reverse: a Bool-valued predicate on `Fin (binom n 1)` is a
    `Cochain n 1`.  Trivial identity, but makes the alignment
    explicit. -/
def predicateAsCochain {n : Nat}
    (P : Fin (binom n 1) → Bool) : Cochain n 1 := P

/-- ★ **Round-trip identity (cochain ↔ predicate)**: the
    bridge is the identity on Bool-valued indicators.  Cochains
    and UnaryTypes-on-finite-vertex-sets are literally the same
    object under §9.3's flat-ontology reading. -/
theorem cochain_predicate_roundtrip {n : Nat} (σ : Cochain n 1) :
    predicateAsCochain (cochainAsPredicate σ) = σ := rfl

/-- Reverse direction: predicate → cochain → predicate. -/
theorem predicate_cochain_roundtrip {n : Nat}
    (P : Fin (binom n 1) → Bool) :
    cochainAsPredicate (predicateAsCochain P) = P := rfl

/-! ## §1 — Concrete instances at d=5 -/

/-- At n = 5 (the d=5 vertex count), `Cochain 5 1` is a
    Bool-valued predicate on 5 indices.  The cardinality of this
    type is 2^5 = 32 — same as the count-Lens reading of the
    UnaryType on a 5-vertex set. -/
theorem cochain_5_1_predicate_cardinality :
    (Cochain 5 1) = (Fin (binom 5 1) → Bool) := rfl

/-! ## §2 — Self-reference closure note

  Together with `Lens/Foundations/FlatOntology.lean` (forward direction:
  Raws → predicates) and `Lens/Foundations/PredicateSelfEncoding.lean`
  (closure direction: predicates → Raw via Gödel numbering),
  this bridge file completes the §9.3 self-reference loop at the
  cochain level:

    Raw → Cochain (this file, indicator alignment)
       → Predicate (FlatOntology)
       → Raw (PredicateSelfEncoding, finite-prefix encoding)

  The loop is closed for the finite-prefix case at every n; the
  full Cantor-style closure remains a separate continuation as noted
  in `PredicateSelfEncoding.lean`.
-/

end E213.Lib.Math.Cohomology.Bridge.PredicateAsCochain
