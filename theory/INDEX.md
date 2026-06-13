# theory/

Human-readable narrative of formalized DRLT-213.  Mirrors
`lean/E213/` so a reader can navigate between code (truth) and
prose (explanation) by path.

## What 213 says (1 paragraph)

Pointing leaves a residue (Raw).  Lens application IS distinguishing —
not a tool acting on Raw from outside (per `seed/AXIOM/05_no_exterior.md` §5.1: no exterior).  Self-consistency forces atomicity
**(NS, NT, c, d) = (3, 2, 2, 5)** uniquely.  From this the algebra
tower, K_{3,2}^{(c=2)} cohomology (gauge content = 8 gluon
channels), and α_em to **0.09 ppb** all derive — without
external parameters, all PURE in Lean.

## Vocabulary (read before chapters)

| Term | Meaning |
|---|---|
| **Raw** | The residue of pointing.  Free magma on 2 generators.  Not "raw data below derivations" — Raw IS what 213 says. |
| **Lens** | A `Raw → α` distinguishing.  Lens application = residue self-pointing event.  Not a tool above Raw. |
| **Lens-arrow** | `Lens.refines L M` — the single 213-native concept underlying equivalence / equivalence-class / isomorphism / homomorphism (동치 / 동치류 / 동형 / 준동형).  See `theory/lens/unified_equivalence.md`. |
| **Distinguishing** | The primitive act 213 names.  Per `seed/AXIOM/01_residue.md`. |
| **(NS, NT, c, d)** | Atomic 4-tuple = (3, 2, 2, 5).  Uniquely forced (see `physics/foundations/atomic_constants.md`). |
| **K_{m,n}^{(c)}** | Bipartite multigraph with m S-vertices, n T-vertices, c edges per (s, t) pair.  213's canonical Lattice. |
| **Δⁿ** | n-simplex on (n+1) vertices.  Δ⁴ pairs with K_{3,2}^{(2)} as dual fillings. |
| **configCountD d n = d^(d^n)** | Parametric configuration count (`lean/E213/Lib/Math/Cohomology/Fractal/ConfigCount.lean`); a count-Lens readout, **no level privileged** — not a universe constant. |
| **Cup-ring** | Cochain cup-product structure.  Closure form for K_{3,2}^{(c=2)} observables. |
| **Cochain n k** | `Fin (binom n k) → Bool` — free ℤ/2-module on k-subset basis of Δⁿ⁻¹. |
| **Modulus** | Explicit `Nat → Nat` replacing ε-δ existentials.  Per `theory/math/analysis/modulus.md`. |
| **∅-axiom (PURE)** | `#print axioms <thm>` returns empty.  No `propext`, no `Classical`, no Mathlib. |
| **Closure Form** | Every K_{3,2}^{(c=2)} observable = R(NS,NT,d,c)·Π(1+κ·αⁿ).  Per `rust-engine/docs/closure-algorithm.md`. |

## Suggested first-pass (4 chapters, real prerequisite chain)

Per round-2 multi-agent debate finding: chapters 1-4 form a genuine
dependency chain (concrete test in `archive/`).  After chapter 4
the reading order is taste — branch into whichever area you came
for.

1. **[`00_axioms_summary.md`](00_axioms_summary.md)** — vocabulary anchor; bridge to `seed/AXIOM/`.
2. **[`lens/universal.md`](lens/universal.md)** — G1 universal lens: the single distinguishing move other chapters compose.
3. **[`lens/algebra.md`](lens/algebra.md)** — Lens kernel algebra; promotes vocabulary to computable object.
4. **[`physics/foundations/atomic_constants.md`](physics/foundations/atomic_constants.md)** — (NS,NT)=(3,2) uniqueness; the first forced number.

From there, branch:
- **Physics observables** → `physics/symmetry/c3_chain.md` (gauge emergence) → `physics/alpha_em/precision_derivation.md` (the 0.09 ppb result)
- **Algebra side** → `math/cayley_dickson/algebra_tower.md` → `math/universe_chain.md`
- **Cohomology side** → `math/cohomology/hodge_conjecture.md`
- **Equivalence concept side** → `lens/unified_equivalence.md` (single-concept synthesis: 동치 / 동치류 / 동형 / 준동형 as the Lens-arrow)

## Three-tier discipline

| Tier | Where | Purpose |
|---|---|---|
| 1. Scratchpad | `research-notes/` | Working memos |
| 2. Source of truth | `lean/E213/` | PURE-verified Lean |
| 3. This book | `theory/` | Narrative + Lean references |

Chapter exists when the Lean sub-tree closed per
[`PROMOTION_CRITERIA.md`](PROMOTION_CRITERIA.md).  Patterns:
[`lean/E213/docs/PROMOTION_PATTERNS.md`](../lean/E213/docs/PROMOTION_PATTERNS.md).

## Top-level orientation

  · [`THEORY_BOOK.md`](THEORY_BOOK.md) — **single linearised
    reading path** from `seed/AXIOM/` through atomic forcing,
    number systems, cohomology, GRA universality, physics
    deployment, and foundational-frameworks-as-Readings.
    Recommended starting point for new readers.
  · [`STATE.md`](STATE.md) — current framework state (closed
    programmes, open frontiers, entry points)
  · [`RESEARCH_PLAN.md`](RESEARCH_PLAN.md) — ranked roadmap
    across five tiers (mechanical closures, cross-chapter
    integration, narrative depth, physics deployment,
    architecture)

## Current chapters (~250 total, incl. 100 essays)

| Area | Chapters | Sub-INDEX |
|---|---:|---|
| `math/`    | 100 | [`math/INDEX.md`](math/INDEX.md) |
| `physics/` | 19 | [`physics/INDEX.md`](physics/INDEX.md) |
| `lens/`    | 14 | [`lens/INDEX.md`](lens/INDEX.md) |
| `meta/`    |  7 | [`meta/INDEX.md`](meta/INDEX.md) |
| `essays/`  | 100 | [`essays/INDEX.md`](essays/INDEX.md) |

Every closed Lean sub-tree has a corresponding `theory/` chapter.
**Synthesis chapters** — consolidating content distributed across
multiple closed sub-trees into one concept — live alongside the
mirror chapters; the per-sub-tree INDEX flags them.  See
`theory/lens/INDEX.md` "Synthesis chapters" for the current list
(currently: `lens/unified_equivalence.md`).

## Active research (not promoted)

`research-notes/` holds the boot-sequence **anchors** at top level (the
residue, semantic atom, ouroboros, universal lens, trajectory, chiral/phase,
sublanguage, layered-API, algebra catalog, lens-emergence) and the **live
open frontiers** under `research-notes/frontiers/` — grouped by topic
(π non-holonomicity, Markov/Lagrange, spiral-axis, completability,
sequence-depth, + standalone geometrization / p-adic / Eisenstein agendas).
See `research-notes/frontiers/INDEX.md` for the open board and
`research-notes/INDEX.md` for the cycle.  Closed material lives in
`research-notes/archive/<topic>/`.

## Companion specs

Foundational spec corpus:

- `seed/THEOREM_METHODOLOGY_SUITE.md` — §TH-1 proof-shape fingerprinting (companions `theory/meta/scanner_suite.md` §1), §TH-2 Raw-derivation taxonomy (companions `theory/meta/raw_derivation_levels.md`), §TH-3 falsifier-surface spec, §TH-4 L1 parametric methodology
- `seed/META_SCAN_ARCHETYPES.md` — 11 reusable scanner archetypes
- `seed/CLOSED_FORM_SPEC.md` — 3-domain projection catalogue + Bishop subsumption + bridges

Catalogs/:

- `catalogs/abstraction-candidates.md` — abstraction roster
- `catalogs/cross-domain-identifications.md` — cross-domain identifications
- `catalogs/falsifier-roster.md` — 135-falsifier catalog
- `catalogs/internal-hubs.md` — internal hub catalog
- `catalogs/recursor-inventory.md` — full recursor inventory

## Layer-ordering vocabulary

`Term` / `Theory` / `Lens` / `Lib` / `Meta` are `import`-resolution
rings, not infrastructure layers below Math / Physics.  Per
`seed/AXIOM/05_no_exterior.md` §5.1 (no exterior) + CLAUDE.md
"Substrate metaphor" failure mode, the rings express
build-time dependency only — Lens application is itself a
residue-internal event, not a substrate beneath Raw.  See
`theory/lens/api.md` for the canonical statement.

## Standalone treatise

`book/` — **The Lens Tower: From the Residue to the Discriminant, and the Descent Home.**
A 6-chapter book reading the orbit/axis/discriminant structure in 213-native primitives: the
number tower as Lens bundlings (residue → count `+` → iterated `×` → difference-Lens `ℤ`), the
Cassini as readout layer (with the genus category-error caught and corrected), the native/imported
separation of `{2,4,6}`/discriminants, and the descent of "disc −2 skipped" to one count-Lens fact
— `leaves(a/b) = 1+1 = NT` is non-square. Every claim cites a PURE Lean theorem. See `book/README.md`.

`book/foundations/` — **The Founding of the Number Tower.**  The companion working treatise that
*founds* the tower the main book applies: is `ℕ → ℤ → ℚ → ℝ` a complete tower (yes — `ℝ` is a
Cauchy fixpoint), one axis or many (hybrid — one unit, many readings), and forced (only at its
seams)?  Mirrors the `Lens/Number/Founding` sub-tree; see `theory/lens/number_systems.md`.
