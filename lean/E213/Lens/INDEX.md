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
  · `SemanticAtom.lean`           — semantic-atom characterisation; **`raw_initial`** (the
                                     universal property: Raw is the initial distinguishing-structure,
                                     ∅-axiom, existence + uniqueness)
  · `SyntacticInternalization.lean` — 7-glyph Raw encoding
  · `FlatOntology.lean`           — flat-ontology realisation (`Object1` self-cover)
  · `FlatOntologyClosure.lean`    — `distinguishing_always_leaves_residue` (the residue is a theorem)
  · `ResidueReentry.lean`         — the residue re-enters; the cover never closes
  · `NoExteriorClosure.lean`      — naming is internal; distinguishing is downstream
  · `OneDiagonal.lean`            — one Lawvere fixed point generates Cantor / Russell / Liar / Tarski
                                     + the residue (the residue is the *engine* of the limitative thms)
  · `UniversalDistinguishing.lean`— the `DStr` schema: the distinguishing as a *classifier* (rivals
                                     are instances ≅ Raw, or fail a named clause). Uniqueness proven;
                                     existence leg open (partial-algebra engineering, no axiom needed)
  · `PredicateSelfEncoding.lean`  — closure of predicate ↔ Raw
  · `RawTopology.lean`            — K_∞ ≡ point bookend
  · `SelfCompletion.lean`         — self-completion lens

## Foundational reading order (for newcomers, incl. AI)

A plain-language guide to this whole layer — what `Raw`/`Lens` are, why `slash` carries `x ≠ y`
(forced by the axiom + the no-`Quot.sound` rule), and what is proven vs. open — is
`theory/essays/foundations/raw_and_lens_explained.md`.  Suggested path:
`LensCore` (what a Lens is) → `SemanticAtom.raw_initial` (the universal property, *already proven*)
→ `FlatOntologyClosure` (the residue) → `OneDiagonal` (residue = engine of the diagonal theorems)
→ `Number/Nat213/Generation` (number from the distinguishing) → `UniversalDistinguishing` (the
schema / rival-exclusion).  The encoding question ("is the technique causing the limit?") is answered
in `research-notes/frontiers/the_distinguishing_schema.md` §RESOLUTION.

## Entry point

The full Lens sub-tree map with chapter-level pointers is the
docstring of `lean/E213/Lens.lean`.

## Companion narrative

  · `theory/lens/` — Lens chapter cluster (api, axiom_lenses, properties, …)
  · `theory/lens/INDEX.md` — book navigation

## Status

Per `STRICT_ZERO_AXIOM.md` §"Sealed-DIRTY inventory" (canonical; rerun
`tools/scan_all_axioms.py` for the live count): the sealed-by-design
`propext` / `Quot.sound` / `Classical.choice` uses are *structural*
(Prop-as-distinguishing `combine_sym` fields; the axiom-exhibiting bridge
lenses; elaborator plumbing).  Whole-corpus census: **0 real DIRTY**.
Lens-side distribution (the live ones):

  · `SemanticAtom.lean`            — 23  category (a) propext (Prop combine_sym)
  · `Properties/Morphism/BoolProp` — 10  category (a) propext (Bool↔Prop equating)
  · `AxiomLenses/Bridges/{Funext,QuotSound}` — 2  axiom-exhibiting bridge lenses (by design)

The Lens-funext family previously listed here (`Instances/Leaves/DepthJoin`,
`Universal/QuotLens`, `Lattice/IndexedJoin`, `Instances/Cauchy`,
`Instances/FunctionSpace`) is now **fully PURE** (the sealed class shrank;
see `STRICT_ZERO_AXIOM.md`).  All other Lens modules are PURE; scanner
reports zero unsealed DIRTY.
