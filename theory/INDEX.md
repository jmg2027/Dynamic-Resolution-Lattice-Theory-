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
| **Distinguishing** | The primitive act 213 names.  Per `seed/AXIOM/01_residue.md`. |
| **(NS, NT, c, d)** | Atomic 4-tuple = (3, 2, 2, 5).  Uniquely forced (see `physics/foundations/atomic_constants.md`). |
| **K_{m,n}^{(c)}** | Bipartite multigraph with m S-vertices, n T-vertices, c edges per (s, t) pair.  213's canonical Lattice. |
| **Δⁿ** | n-simplex on (n+1) vertices.  Δ⁴ pairs with K_{3,2}^{(2)} as dual fillings. |
| **N_U = d^(d²) = 5²⁵** | Count-Lens output at fractal level 2.  Resolution limit per `seed/RESOLUTION_LIMIT_SPEC.md`. |
| **Cup-ring** | Cochain cup-product structure.  Closure form for K_{3,2}^{(c=2)} observables. |
| **Cochain n k** | `Fin (binom n k) → Bool` — free ℤ/2-module on k-subset basis of Δⁿ⁻¹. |
| **Modulus** | Explicit `Nat → Nat` replacing ε-δ existentials.  Per `theory/math/modulus.md`. |
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

## Three-tier discipline

| Tier | Where | Purpose |
|---|---|---|
| 1. Scratchpad | `research-notes/` | Working memos |
| 2. Source of truth | `lean/E213/` | PURE-verified Lean |
| 3. This book | `theory/` | Narrative + Lean references |

Chapter exists when the Lean sub-tree closed per
[`PROMOTION_CRITERIA.md`](PROMOTION_CRITERIA.md).  Patterns:
[`lean/E213/docs/PROMOTION_PATTERNS.md`](../lean/E213/docs/PROMOTION_PATTERNS.md).

## Current chapters (115 total, incl. 20 essays)

| Area | Chapters | Sub-INDEX |
|---|---:|---|
| `math/`    | 68 | [`math/INDEX.md`](math/INDEX.md) |
| `physics/` | 18 | [`physics/INDEX.md`](physics/INDEX.md) |
| `lens/`    | 11 | [`lens/INDEX.md`](lens/INDEX.md) |
| `meta/`    |  6 | [`meta/INDEX.md`](meta/INDEX.md) |
| `essays/`  | 20 | [`essays/INDEX.md`](essays/INDEX.md) |

Every closed Lean sub-tree has a corresponding `theory/` chapter.

## Active research (not promoted)

Top-level `research-notes/` registries:

| Class | Notes | Purpose |
|---|---|---|
| Foundational anchors | `G29_residue.md`, `G1-G5`, `G12`, `75`, `76` | Boot-sequence, thesis anchors, semantic atom, ouroboros |
| Methodology & catalogs | `G35` (algebra catalog) | Cross-session tooling references |
| Open conjectures | `G85, G87` (cup-Δ observations), `G86` (Cup-Leibniz ∀(k,l)) | Conjecture catalog |
| Open research directions | `G121` (Geometrization R1+ — chapter active, side-observations open) | Active scratch — chapter handles R1; note hosts the open marathon front |
| Synthesis / deep-dive | `G108-G116`, `G135-G137` | Tier-2 analytical scans annotating already-promoted chapters |
| Lens emergence | `2026-05-18_lens_emergence_path.md` | Specification |

Deep-dive synthesis notes annotate already-promoted chapters per the
`essay` skill protocol — they are analytical scans, not closure
narratives, so do not become chapters themselves.

## Companion specs

Foundational spec corpus alongside `seed/RESOLUTION_LIMIT_SPEC.md`:

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
