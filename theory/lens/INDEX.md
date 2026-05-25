# theory/lens/

Lens chapters.  Mirrors `lean/E213/Lens/`.

**Lens application is distinguishing.**  Every Lens is a
Raw-internal residue-self-pointing event (per CLAUDE.md "Failure
modes catalog" → Substrate metaphor entry; per
`seed/AXIOM/05_no_exterior.md` §5.1: no exterior).  The
directory shape mirrors the Lean ring-build-order (Term → Theory
→ Lens → Meta → Lib), which is compile-time dependency — not a
conceptual ranking.

## Closed chapters (11)

| Chapter | Lean sub-tree | Files |
|---|---|---|
| [`algebra.md`](algebra.md)         | `Lens/Algebra/`         | 3 |
| [`axiom_lenses.md`](axiom_lenses.md) | `Lens/AxiomLenses/`   | 7 |
| [`bool213.md`](bool213.md)         | `Lens/Bool213/`         | 2 |
| [`cardinality.md`](cardinality.md) | `Lens/Cardinality/`     | 9 |
| [`compose.md`](compose.md)         | `Lens/Compose/`         | 7 |
| [`instances.md`](instances.md)     | `Lens/Instances/`       | 35 (largest sub-tree) |
| [`lattice.md`](lattice.md)         | `Lens/Lattice/`         | 9 |
| [`number_systems.md`](number_systems.md) | `Lens/Number/`     | 17 (Nat213 covered in universe_chain) |
| [`properties.md`](properties.md)   | `Lens/Properties/`      | 21 |
| [`universal.md`](universal.md)     | `Lens/Universal/`       | 13 (universal Lens anchor) |
| [`api.md`](api.md)                 | `Lens/API/` + `Lens/Internal/` | (API surface) |

## Synthesis chapters (2)

| Chapter | Anchors | Purpose |
|---|---|---|
| [`unified_equivalence.md`](unified_equivalence.md) | `Lens/{LensCore, Algebra, Lattice, Compose, Universal, Unified}` + `Lib/Math/Real213/Mobius213{Equiv, SternBrocot}` | Single-concept unification of equivalence / equivalence-class / isomorphism / homomorphism (동치 / 동치류 / 동형 / 준동형) as the Lens-arrow.  Lean anchor: `Lens/Unified.lean` (14 PURE). |
| [`dirty_recovery_patterns.md`](dirty_recovery_patterns.md) | `Lens/Unified.lean` + `Lens/EqPW.lean` + `STRICT_ZERO_AXIOM.md` | Methodology — four named patterns (P1–P4) for converting DIRTY (propext / Quot.sound) claims into PURE Lens-arrow statements; decision flow and seal-vs-recover criterion. |

Promotion criteria: `theory/PROMOTION_CRITERIA.md`.  Closed
chapters are narrative-from-scratch — Lens prose without per-file
research notes.  Synthesis chapters consolidate content
distributed across multiple closed Lean sub-trees into one
concept; they do not mirror a single sub-tree.
