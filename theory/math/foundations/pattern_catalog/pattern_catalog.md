# Pattern Catalog — 213 recurring structural patterns

**Status**: Closed (5 file catalog, all PURE).

## Overview

The pattern catalog is the **metaformalization** of recurring
algebraic / structural patterns across 213's sub-trees.  Per the
pattern-presence audit → every-pattern-present theorem → pattern-catalog metaformalization audit arc (213 has every stateable pattern), the
catalog organizes these into a small set of named combinators:

- **Algebra**: algebraic pattern (closure / inverse / etc.)
- **CrossAxis**: NS × NT cross-axis pattern
- **Instance**: pattern-instance scaffolding
- **Span**: span pattern
- **Core**: base pattern combinator

These names appear repeatedly across `Lib/Math/` sub-trees; the
catalog gives them one canonical home.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Foundations/PatternCatalog/` (5 files)
- **Umbrella**: `lean/E213/Lib/Math/Foundations/PatternCatalog.lean`
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

### From pattern-presence audit to every-pattern-present theorem: "every pattern present"

The pattern-presence audit-pattern-presence audit pattern audit arc analyzed 6125 declarations and found
that 213's existing infrastructure realizes essentially **every**
stateable algebraic pattern.  Every-pattern-present theorem made this precise:

> **Every operationally-stateable pattern lives in 213** — not as a
> conjecture, but as a derivable theorem given the 4-clause axiom +
> Lens framework.

Every-pattern-present theorem corrects pattern-presence audit: the previous note treated patterns as "imposed
classifications".  The corrected reading: patterns *emerge* from the
axiom + Lens application, and the catalog records what has emerged.

### pattern-catalog metaformalization: metaformalization synthesis

pattern-catalog metaformalization closes the arc by formalizing the catalog as **Lean code** —
not as documentation but as actual `def`s and `theorem`s that other
sub-trees instantiate.  `Lib/Math/Foundations/PatternCatalog/` is the formal
realization.

The catalog is organized as five modules — `Core` (witness
combinators), `Algebra` (operator-word algebra), `CrossAxis`,
`Instance` (concrete demos), and `Span` — each recording the
declarations other sub-trees instantiate.

### Catalog usage

Other sub-trees cite the catalog rather than reinventing patterns:
- `Lib/Math/Algebra/CayleyDickson/` instantiates `Algebra` for CD-doubling
- `Lib/Physics/AlphaEM/` uses `CrossAxis` for NS × NT decompositions
- `Lib/Math/Cohomology/` uses `Span` for cup-product spans
- Domain capstones use `Instance` for the paradigm
  typeclass scaffolding (companion to C6 cross-domain unification)

## Key results

| Declaration | Module | Statement |
|---|---|---|
| `LocalityWitness`, `CapstoneBundle`, `InterfaceWitness`, `CatamorphismWitness`, `DynamicalWitness`, `ForcedValueWitness`, `CohabitationWitness`, `Aggregate` | `Core` | Base witness combinators |
| `OpWord`, `Primitive`, `GameAnchor` | `Algebra` | Operator-word algebra + primitive anchors |
| `CrossAxisCell`, `CrossAxisSpecimen` | `CrossAxis` | NS × NT cross-axis entries |
| (instance demos) | `Instance` | Concrete witness instances |
| `SpanResult`, `EscapeCandidate` | `Span` | Span verdict + escape candidates |

(The content is in their *use* across other sub-trees, not in their
own depth.)

## ParadigmDomain bridge — closed (ParadigmBridge.lean)

`Lib/Math/Foundations/PatternCatalog/ParadigmBridge.lean` (15 PURE) makes the
relationship between the abstract catalog and the applied
ParadigmDomain explicit:

**Bridge thesis**: `ParadigmDomain` ≅ `Aggregate ∘ Forced` applied
to `ParadigmWitness`.  Reading: the 9 paradigm-domain instances
are bundled into one `Aggregate ParadigmWitness` (arity 9, phase
"BB" = Both-Bound); each entry's `truncation_grade` is Forced to 5,
`truncation_holds` Forced to true, `atom_decidable` Forced to true.

Operator-word reading: the catalog algebra (`OpWord`) expresses
this as the 2-letter word `A · F` — Aggregate-of-Forced.  Length 2,
`aggCount = 1`, `forCount = 1`.

Capstone: `paradigm_pattern_bridge_capstone` packages (a) arity 9,
(b) uniform grade / holds / decidability across all 9 entries, and
(c) operator-word stats in a single ∅-axiom theorem.

The bridge confirms C6 cross-domain unification is a *PatternCatalog
instantiation*, not a parallel construction — the same Aggregate +
Forced operator pair that classifies generic 213 patterns (per the
`OpWord` algebra) captures the 9-domain unification at the typeclass
level.

## Open frontier

Pattern catalog is **closed** at the 5-entry level.  Open extensions:
- Adding new patterns is incremental — each new pattern is a small
  `Core` extension.
- ~~Bridge to `ParadigmDomain`~~ — CLOSED via
  `PatternCatalog/ParadigmBridge.lean` (15 PURE).

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Foundations.PatternCatalog
python3 tools/scan_axioms.py Lib/Math/Foundations/PatternCatalog
```

## Citation guidance

- ✅ `theory/math/foundations/pattern_catalog/pattern_catalog.md` (narrative)
