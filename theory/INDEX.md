# theory/

Human-readable narrative of formalized DRLT-213.  Mirrors
`lean/E213/` so a reader can navigate between code (truth) and
prose (explanation) by path.

## What 213 says (1 paragraph)

Pointing leaves a residue (Raw).  Lens application IS distinguishing —
not a tool acting on Raw from outside (per `seed/AXIOM/07_self_reference.md`
§8.1: no exterior).  Self-consistency forces atomicity
**(NS, NT, c, d) = (3, 2, 2, 5)** uniquely.  From this the algebra
tower, K_{3,2}^{(c=2)} cohomology (gauge content = 8 gluon
channels), and α_em to **0.09 ppb** all derive — without
external parameters, all PURE in Lean.

## Vocabulary (read before chapters)

| Term | Meaning |
|---|---|
| **Raw** | The residue of pointing.  Free magma on 2 generators.  Not "raw data below derivations" — Raw IS what 213 says. |
| **Lens** | A `Raw → α` distinguishing.  Lens application = residue self-pointing event.  Not a tool above Raw. |
| **Distinguishing** | The primitive act 213 names.  Per `seed/AXIOM/00_nature.md`. |
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

## Current chapters (89 total)

| Area | Chapters | Sub-INDEX |
|---|---:|---|
| `math/`    | 58 | [`math/INDEX.md`](math/INDEX.md) |
| `physics/` | 18 | [`physics/INDEX.md`](physics/INDEX.md) |
| `lens/`    | 11 | [`lens/INDEX.md`](lens/INDEX.md) |
| `meta/`    |  2 | [`meta/INDEX.md`](meta/INDEX.md) |

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

## Note on framing (2026-05-22 revision)

Earlier draft used OS-stack analogy ("Firmware", "Hypervisor",
"second 213 layer") in some `lens/` files.  Per
`seed/AXIOM/07_self_reference.md` §8.1 (no exterior) + CLAUDE.md
"Substrate metaphor" failure mode, those framings have been
replaced with build-time ring ordering language.  Lens / Theory
/ Term are not infrastructure below Math / Physics — the ring
ordering is `import`-resolution only.  See `theory/lens/api.md`
for the canonical statement.
