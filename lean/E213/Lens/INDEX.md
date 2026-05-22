# lean/E213/Lens — Lens Ring

Lens is the **third ring** of the four-ring architecture (Term →
Theory → Lens → Lib).  Lens-projection plumbing: ~10 Expr nodes per
declaration (per ring-shape audit at `lean/E213/ARCHITECTURE.md`
§3.4).  Per CLAUDE.md naming: "Lens" denotes any distinguishability
output of `Raw.fold`.

## Sub-clusters

| Sub-cluster | Files | Theme |
|---|---:|---|
| `Algebra/` | 3 | Lens algebraic kernel (congruence, four-distinct, free audit) |
| `AxiomLenses/` | 7 | Axiom-lens family (Funext / Propext / QuotSound bridges) |
| `Bool213/` | 2 | Raw-encoded closed-universe `Bool` |
| `Cardinality/` | 9 | Cardinality observables (Cantor, Tower, BoolSpace, …) |
| `Compose/` | 7 | Composition operators (Factoring, OnLens, Morphism, …) |
| `Instances/` | 35 | Concrete Lens instances (AB, Bool, Cauchy, Path, Prism, Reach, …) + `Leaves/` |
| `Internal/` | 4 | Lens internals (Algebra/FreeAudit, GreatestPW, …) |
| `Lattice/` | 9 | Refines preorder + lattice (Join / Meet / IndexedJoin / FamilyJoin) |
| `Number/` | 17 | Raw-derived number systems (Nat213 — Raw chain + Peano + Bridge + Tower) |
| `Properties/` | 21 | Derived predicates + Diagonal + Characterisation + Morphism |
| `Universal/` | 13 | Universal flat / quot lens + Witnesses |

## Top-level files

  · `Lens.lean`                   — umbrella entry point (full index docstring)
  · `API.lean`                    — public surface
  · `LensCore.lean`               — Lens type + view/equiv
  · `Initiality.lean`             — initiality of the Lens category
  · `Congruence.lean`             — `Eqv ↔ L.equiv` bridge
  · `EqPW.lean`                   — pointwise Lens equality
  · `SemanticAtom.lean`           — semantic-atom characterisation
  · `SyntacticInternalization.lean` — 7-glyph Raw encoding
  · `FlatOntology.lean`           — flat-ontology realisation
  · `PredicateSelfEncoding.lean`  — closure of predicate ↔ Raw
  · `RawTopology.lean`            — K_∞ ≡ point bookend
  · `SelfCompletion.lean`         — self-completion lens

## Entry point

The full Lens sub-tree map with chapter-level pointers is the
docstring of `lean/E213/Lens.lean`.

## Companion narrative

  · `theory/lens/` — Lens chapter cluster (api, axiom_lenses, properties, …)
  · `theory/lens/INDEX.md` — book navigation

## Status

Per `STRICT_ZERO_AXIOM.md` §"Sealed-by-design categories": 56
theorems across 7 Lens sub-clusters use `propext` / `Quot.sound` /
`Classical.choice` for *structural* reasons — Prop-as-distinguishing
combine_sym fields, function-valued Lens.combine fields, and
JoinEquiv quotient-representative selection.  These are waived as
sealed-by-design.  Distribution:

  · `SemanticAtom.lean`            — 23  category (a) propext (Prop combine_sym)
  · `Properties/Morphism/BoolProp` — 10  category (a) propext (Bool↔Prop equating)
  · `Instances/Leaves/DepthJoin`   — 10  category (c) Classical.choice (5) + (b) Quot.sound (5)
  · `Universal/QuotLens`           —  5  category (b) Quot.sound (function-valued combine)
  · `Lattice/IndexedJoin`          —  4  category (b) Quot.sound
  · `Instances/Cauchy`             —  3  category (b) Quot.sound
  · `Instances/FunctionSpace`      —  1  category (b) Quot.sound

All other Lens modules are PURE.  Scanner reports zero unsealed
DIRTY.
