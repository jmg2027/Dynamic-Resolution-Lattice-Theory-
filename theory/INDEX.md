# theory/

Human-readable narrative of the formalized DRLT-213 results.  Mirrors
the directory shape of `lean/E213/` so a reader can navigate
between code (truth) and prose (explanation) by path.

## Role in the three-tier discipline

| Tier | Where | Purpose |
|---|---|---|
| 1. Scratchpad | `research-notes/` | Working memos |
| 2. **Source of truth** | `lean/E213/` | PURE-verified Lean |
| 3. **This book** | `theory/` | Narrative + Lean references |

A chapter in `theory/` exists only when the corresponding Lean
sub-tree has **closed** per `PROMOTION_CRITERIA.md`.

## Reading order

1. `00_axioms_summary.md` — bridge from `seed/AXIOM/` to chapters.
2. `math/INDEX.md` — 49 math chapters.
3. `physics/INDEX.md` — 17 physics chapters.
4. `lens/INDEX.md` — 11 Lens-ring chapters.
5. `meta/INDEX.md` — 2 meta-analysis chapters.

## Current chapters (79 total)

| Area | Count |
|---|---:|
| `math/` | 49 |
| `physics/` | 17 |
| `lens/` | 11 |
| `meta/` | 2 |

Every closed Lean sub-tree has a corresponding theory chapter.

## How promotion works

See `PROMOTION_CRITERIA.md` for the H1-H4 + S1-S3 gates and
`lean/E213/docs/PROMOTION_PATTERNS.md` for the three operational
patterns + destination variants.

## Active research (not promoted)

The following research-notes top-level files remain **active scratch**:

- `G29_residue.md` — boot-sequence foundational read
- `G1-G5, G12` — foundational thesis (anchors universal_lens / trajectory / chiral / sublanguage / layered API)
- `75, 76` — semantic atom + ouroboros
- `G35` — 213-Algebra field catalog (17 domains, §0.5 tracks promotions; all 6 conjectures C1-C6 now promoted)
- `G85, G87` — cup-Δ Lens mismatch + emergence audit (closed observations)
- **`G86` — Cup-Leibniz general ∀(k,l) conjecture (OPEN, see HANDOFF Part 2 §A)**
- `2026-05-18_lens_emergence_path.md` — lens emergence spec (12 citations from lean/seed)
- `G107_action_items_registry.md` — meta-scan action items (live tracker)
