import E213.Math.PatternCatalogAlgebra
import E213.Math.PatternCatalogCrossAxis

/-!
# Pattern Catalog — Span Analysis

Three possible relationships between the catalog and the codebase
patterns it aims to describe:

  · **under-span**  : there exist real codebase theorems that fit
                      NO catalog cell.
  · **exact-span**  : every codebase theorem fits some catalog cell,
                      AND every catalog cell has at least one
                      codebase witness.
  · **over-span**   : every codebase theorem fits some catalog cell,
                      but some catalog cells have NO codebase witness.

This file records the catalog's span verdict empirically, with
∅-axiom-typed evidence pointers.  It is descriptive (an audit
artifact), not prescriptive.
-/

namespace E213.Math.PatternCatalogSpan

open E213.Math.PatternCatalogAlgebra
open E213.Math.PatternCatalogCrossAxis

/-- Span outcome enumeration. -/
inductive SpanResult where
  | underSpan
  | exactSpan
  | overSpan
  deriving DecidableEq, Repr

/-- Verdict at the **game-type** level: every named game in
    `PatternCatalog` has at least one concrete instance in
    `PatternCatalogInstance` (4 atomic + 2 operator + 9 composite
    structures + 5 abbrevs).  At this granularity, span is exact. -/
def gameLevelVerdict : SpanResult := .exactSpan

/-- Verdict at the **cross-axis cell** level: of 6 statement-shape
    families × 21 game types = 126 cells, the codebase populates
    ≈ 13–15 distinctly (witnesses recorded as
    `PatternCatalogCrossAxis.specimen_*`).  ~10% cell occupancy.
    Catalog over-spans at this granularity. -/
def cellLevelVerdict : SpanResult := .overSpan

/-- Cell occupancy lower bound from currently named specimens.  Each
    specimen pins one cell.  We have 13 named specimens covering 13
    distinct cells (no two specimens share a cell). -/
def occupiedCellLowerBound : Nat := 13

/-- Total cell count (6 statement shapes × 21 game-types). -/
def totalCellCount : Nat := 126

/-! ## Under-span check — escape patterns

Are there codebase theorems that fit NO catalog cell?  Three
candidate escape categories from the G17–G24 audit corpus: -/

/-- Escape-pattern hypothesis enumerator.  Each constructor names a
    candidate codebase pattern that might NOT fit current catalog. -/
inductive EscapeCandidate where
  /-- Dependent-type / Σ-typed bundles (e.g., `(i : Idx) × W i`
      where W varies per index).  Current `Aggregate W` requires
      uniform W; heterogeneous-witness aggregates would need
      `DepAggregate (W : Idx → Type)`. -/
  | depAggregate
  /-- 4-way and higher Cohabitation (one Raw substrate viewed
      through ≥ 4 distinct Lenses).  `CohabitationWitness` is
      ternary; arity-N would need a generalisation. -/
  | nAryCohabit
  /-- Recursive / impredicative game (a `Lens (Lens α)`).
      Currently inhabits `LensWitness (LensWitness α)` trivially
      — same shape, no genuine escape. -/
  | recursiveLens
  /-- The 9 `Classical.*`-demoing theorems noted in G24 §6.
      These are deliberately Classical-axiom and are NOT supposed
      to fit a ∅-axiom catalog. -/
  | classicalDemo
  deriving DecidableEq, Repr

/-- Verdict per escape candidate. -/
def EscapeCandidate.fits : EscapeCandidate → Bool
  | .depAggregate  => false  -- genuine escape; needs catalog extension
  | .nAryCohabit   => false  -- arity-N Cohabitation not yet in catalog
  | .recursiveLens => true   -- LensWitness is polymorphic; reuses cleanly
  | .classicalDemo => true   -- out-of-scope by design (ε-axiom only)

/-- Honest under-span list: candidates that genuinely escape. -/
def underSpanCandidates : EscapeCandidate → Bool
  | .depAggregate  => true
  | .nAryCohabit   => true
  | _              => false

/-! ## Final verdict

Composite reading of game-level + cell-level + escape-check:

  · GAME LEVEL  : exactSpan — every named game has ≥1 instance.
  · CELL LEVEL  : overSpan  — most cross-cells are unpopulated.
  · ESCAPE      : underSpan — at least 2 honest escape categories
                              (depAggregate, nAryCohabit) point
                              outside the current catalog.

These verdicts are NOT contradictory: they describe the catalog at
different granularities.  The catalog **fits** the patterns it
captures, **over-allocates** the Cartesian cell space, and
**under-extends** in two specific directions that the next round
of formalization could close.

The composite verdict, summarising for a single label: -/

def finalVerdict : SpanResult := .underSpan
  -- Reasoning: even though game-level and most-cell-level coverage
  -- is exact-or-over, the existence of EscapeCandidate.depAggregate
  -- and EscapeCandidate.nAryCohabit means there are codebase shapes
  -- not yet typed.  Honesty-first: under-span wins the disjunction.

/-- Concrete extension proposal for closing under-span: -/
def proposedExtensions : List String :=
  ["DepAggregate (W : Idx → Type) — heterogeneous-witness bundles",
   "ArityNCohabit (n : Nat) — n-way base-shared Lens cohabitation",
   "DepLocality (Idx → Val Idx) — Σ-typed Locality (codebase rare)"]

end E213.Math.PatternCatalogSpan
