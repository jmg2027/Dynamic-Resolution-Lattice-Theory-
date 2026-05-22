# Pattern Catalog — 213 recurring structural patterns

**Status**: Closed (5 file catalog, all PURE).
**Promoted from research-notes**: 2026-05-22.

Pattern 1 (multi-note absorption).  G28 + G30 → 1 chapter; archived.

## Overview

The pattern catalog is the **metaformalization** of recurring
algebraic / structural patterns across 213's sub-trees.  Per the
G27 → G28 → G30 audit arc (213 has every stateable pattern), the
catalog organizes these into a small set of named combinators:

- **Algebra**: algebraic pattern (closure / inverse / etc.)
- **CrossAxis**: NS × NT cross-axis pattern
- **Instance**: pattern-instance scaffolding
- **Span**: span pattern
- **Core**: base pattern combinator

These names appear repeatedly across `Lib/Math/` sub-trees; the
catalog gives them one canonical home.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/PatternCatalog/` (5 files)
- **Umbrella**: `lean/E213/Lib/Math/PatternCatalog.lean`
- **∅-axiom status**: PURE

### Files

| File | Purpose |
|---|---|
| `Core.lean` | Base pattern combinator |
| `Algebra.lean` | Algebraic-pattern catalog entry |
| `CrossAxis.lean` | Cross-axis pattern (NS × NT, 3 × 2) |
| `Instance.lean` | Pattern-instance scaffolding |
| `Span.lean` | Span pattern |

## The narrative

### From G27 to G28: "every pattern present"

The G17-G27 pattern audit arc analyzed 6125 declarations and found
that 213's existing infrastructure realizes essentially **every**
stateable algebraic pattern.  G28 made this precise:

> **Every operationally-stateable pattern lives in 213** — not as a
> conjecture, but as a derivable theorem given the 4-clause axiom +
> Lens framework.

G28 corrects G27: the previous note treated patterns as "imposed
classifications".  The corrected reading: patterns *emerge* from the
axiom + Lens application, and the catalog records what has emerged.

### G30: metaformalization synthesis

G30 closes the arc by formalizing the catalog as **Lean code** —
not as documentation but as actual `def`s and `theorem`s that other
sub-trees instantiate.  `Lib/Math/PatternCatalog/` is the formal
realization.

The five named patterns are the minimal generating set: every
recurring 213 pattern is built from `Core ∘ {Algebra, CrossAxis,
Instance, Span}` compositions.

### Catalog usage

Other sub-trees cite the catalog rather than reinventing patterns:
- `Lib/Math/CayleyDickson/` instantiates `Algebra` for CD-doubling
- `Lib/Physics/AlphaEM/` uses `CrossAxis` for NS × NT decompositions
- `Lib/Math/Cohomology/` uses `Span` for cup-product spans
- Marathon domain capstones use `Instance` for the paradigm
  typeclass scaffolding (companion to C6 cross-domain unification)

## Key results

| Theorem / Def | Module | Statement |
|---|---|---|
| `Pattern` core combinator | `Core` | Base combinator type |
| `AlgebraPattern` | `Algebra` | Algebraic pattern entry |
| `CrossAxisPattern` | `CrossAxis` | NS × NT cross-axis entry |
| `InstancePattern` | `Instance` | Instance scaffold |
| `SpanPattern` | `Span` | Span entry |

(Pattern catalog is small by design — five named entries.  The
content is in their *use* across other sub-trees, not in their
own depth.)

## Research-note provenance

Two notes (`G28`, `G30`) — archived to
`research-notes/archive/pattern_catalog/`:

| Note | Theme |
|---|---|
| `G28_every_pattern_present.md` | Operational primitives: every stateable pattern lives in 213 (corrects G27) |
| `G30_pattern_catalog_synthesis.md` | Pattern catalog metaformalization (Lean realization) |

The G27 → G28 correction (patterns as emergent, not imposed) is
the canonical reading.

## Open frontier

Pattern catalog is **closed** at the 5-entry level.  Open extensions:
- Adding new patterns is incremental — each new pattern is a small
  `Core` extension.
- The catalog's relationship to `Lib/Math/ParadigmDomain*` (C6
  cross-domain unification) is implicit; an explicit bridge theorem
  ("every paradigm domain instantiates a pattern catalog entry") is
  conceivable but not yet written.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.PatternCatalog
python3 tools/scan_axioms.py Lib/Math/PatternCatalog
```

## Citation guidance

- ✅ `theory/math/pattern_catalog/pattern_catalog.md` (narrative)
- ✅ archived notes for the audit arc:
  `research-notes/archive/pattern_catalog/G##_*.md`
