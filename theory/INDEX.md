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

## Current chapters (94 total)

| Area | Chapters | Sub-INDEX |
|---|---:|---|
| `math/`    | 60 | [`math/INDEX.md`](math/INDEX.md) |
| `physics/` | 18 | [`physics/INDEX.md`](physics/INDEX.md) |
| `lens/`    | 11 | [`lens/INDEX.md`](lens/INDEX.md) |
| `meta/`    |  4 | [`meta/INDEX.md`](meta/INDEX.md) |
| `essays/`  |  1 | [`essays/cut_off_marathon.md`](essays/cut_off_marathon.md) |

Every closed Lean sub-tree has a corresponding `theory/` chapter.

## Active research (not promoted)

Foundational baseline (top-level `research-notes/`):
- `G29_residue.md` — boot-sequence
- `G1-G5, G12` — foundational thesis anchors (universal lens / trajectory / chiral / sublanguage / layered API)
- `75, 76` — semantic atom + ouroboros
- `G35` — 213-Algebra field catalog (§0.5 tracks promotions; all 6 conjectures C1-C6 promoted)
- `G85, G87` — cup-Δ closed observations
- **`G86` — Cup-Leibniz general ∀(k,l) (OPEN conjecture; HANDOFF Part 2 §A)**
- `2026-05-18_lens_emergence_path.md` — lens emergence spec
- `G107_action_items_registry.md` — meta-scan live tracker
- **`G121_dim4_self_pointing_axis.md` — Geometrization conjecture
  research direction (R1 closed; R1+ partial; G122 4-mfd exotic
  enumeration OPEN).  R1 closure promoted to
  `theory/math/geometrization_conjecture.md`; G121 stays active for
  G122-G125 marathon candidates + M3/M4 knots.**

2026-05-22 merge from `claude/lean4-ast-patterns-g1gWN` brought
additional active research notes — Tier-2 deep dives + research
directions, NOT promoted (deep dives are analytical scans, not
closure narratives; per `essay` skill protocol).  All annotate
already-promoted chapters:

- `G108_real213_analysis_deep_dive.md` — Tier-2 precise analysis (annotates `theory/math/real213.md`, `theory/math/analysis/*.md`)
- `G109_cross_domain_identification_scan.md` — cross-domain identifications scan
- `G110_fluxmvt_deep_dive.md` — annotates `theory/math/analysis/flux_m_v_t.md`
- `G111_cohomology_deep_dive.md` — annotates `theory/math/cohomology/*.md`
- `G112_hodge_conjecture_deep_dive.md` — annotates `theory/math/cohomology/hodge_conjecture.md`
- `G113_dyadic_fsm_deep_dive.md` — annotates `theory/math/dyadic_fsm.md`
- `G114_cayley_dickson_deep_dive.md` — annotates `theory/math/cayley_dickson/algebra_tower.md`
- `G115_lib_physics_deep_dive.md` — annotates `theory/physics/*.md`
- `G116_pattern_catalog_deep_dive.md` — annotates `theory/math/pattern_catalog/pattern_catalog.md`
- `G118_marathon_deferred_items.md` — *archived* (closure log; absorbed
  into `theory/math/dyadic_fsm.md` G119 marathon section + this INDEX)
- `G119_pisano_pell5_research_direction.md` — *archived* (universal-prime
  closure achieved; absorbed into `theory/math/dyadic_fsm.md` G119
  marathon section + `theory/math/modular_arithmetic.md` G119 section)

`claude/lean4-ast-patterns-g1gWN` merge (2026-05-22 late) brought:
- G119 marathon (Phase 3.2/3.3/4 universal Pisano closure) — promoted
  to `theory/math/dyadic_fsm.md` + `theory/math/modular_arithmetic.md`
- G122 (Real213-p-adic) research direction — STARTER + plan only,
  not yet promotable

## Companion seed/ specs (2026-05-22 merge)

Foundational specs added alongside `seed/RESOLUTION_LIMIT_SPEC.md`:

- `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-2 — formal Raw-derivation taxonomy (companions `theory/meta/raw_derivation_levels.md`)
- `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-1 — proof-shape fingerprinting (companions `theory/meta/scanner_suite.md`)
- `seed/META_SCAN_ARCHETYPES.md` — meta-scan archetype catalog
- `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-3 — falsifier surface spec (DRLT Validation Standard depth)
- `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-4 — L1 parametric methodology (G106 / `theory/meta/scanner_suite.md` §1)
- `seed/CLOSED_FORM_SPEC.md` §"Bishop subsumption" — Bishop comparison doctrinal subsumption

## Companion catalogs/ (2026-05-22 merge)

- `catalogs/abstraction-candidates.md` — abstraction roster (G107 §2-§5 promoted)
- `catalogs/cross-domain-identifications.md` — G109 deliverable
- `catalogs/falsifier-roster.md` — 135-falsifier catalog (G100 deliverable)
- `catalogs/internal-hubs.md` — internal hub catalog (G102 deliverable)
- `catalogs/recursor-inventory.md` — full recursor inventory (G105 deliverable)

## Note on framing (2026-05-22 revision)

Earlier draft used OS-stack analogy ("Firmware", "Hypervisor",
"second 213 layer") in some `lens/` files.  Per
`seed/AXIOM/05_no_exterior.md` §5.1 (no exterior) + CLAUDE.md
"Substrate metaphor" failure mode, those framings have been
replaced with build-time ring ordering language.  Lens / Theory
/ Term are not infrastructure below Math / Physics — the ring
ordering is `import`-resolution only.  See `theory/lens/api.md`
for the canonical statement.
