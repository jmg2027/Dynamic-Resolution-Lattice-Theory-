# Session Handoff — 2026-05-23

## Branch

`claude/research-notes-promotion-1BsIr` — multi-session marathon
pushing active `research-notes/` items to promotion level per
`theory/PROMOTION_CRITERIA.md`.

## Wave 2 — G37-G87 cluster consolidation (9 absorbed)

| Note | Target chapter | Section added |
|---|---|---|
| `G59_generic_CDDouble_starring_lift.md` | `theory/math/cayley_dickson/algebra_tower.md` | "Generic-lift functor — type-level CD doubling" |
| `G60_tower_ascent_fixed_point.md` | `theory/math/cayley_dickson/algebra_tower.md` | "Three concurrent fates of the tower" — algebraic loss / Order-4 ascent / {±1} fixed point |
| `G61_213_tower_research_candidates.md` | — | Superseded by G62/G63/G64 closures; archived without absorption |
| `G62_nat_to_int_orthogonal.md` | `theory/math/universe_chain.md` | "Orthogonal-axis tower" — `ℕᵏ → ℤᵏ⁻¹` + property losses |
| `G63_orthogonal_axis_tower_synthesis.md` | `theory/math/universe_chain.md` | "Orthogonal-axis tower" — Eisenstein discovery at k = 3 |
| `G64_zero_as_emergent_artifact.md` | `theory/math/universe_chain.md` | "Orthogonal-axis tower" — `0` as diagonal-collapse artifact |
| `G85_cup_delta_lens_mismatch.md` | `theory/math/cohomology/cup.md` | Already absorbed via the wave-1 Lens-recipe catalog section |
| `G86_self_referential_lex_cup_leibniz.md` | `theory/math/cohomology/cup.md` | Already absorbed via the wave-1 Lens-recipe catalog section (`fin_level_leibniz_general` is the chapter's core capstone) |
| `G87_raw_native_emergence_audit.md` | `theory/physics/foundations/atomic_constants.md` | "Raw-side derivation — Clause 4 recursive atomicity" + dual-emergence Eisenstein-dual signature |

INDEX.md trimmed: top-level "Number systems + topology" row removed
(G37-G50 had already been moved to `archive/discrete_geometry/` in
earlier sessions but the INDEX still listed them).

## Wave 1 (carry-over from this branch)

| Note | Target chapter |
|---|---|
| `G125_lens_recipe_cup_catalog.md` | `theory/math/cohomology/cup.md` (Lens-recipe catalog) |
| `G124_n_u_family_cross_field_connections.md` | `theory/math/cohomology/fractal.md` Open frontier |
| `G127_base_5_wieferich.md` | `theory/math/cohomology/fractal.md` Open frontier |
| `G128_affine_plane_K25.md` | `theory/math/cohomology/fractal.md` Open frontier |
| `G127_promotion_readiness_audit.md` | CLOSED — all 5 tracked marathons promoted |

## Build + purity

  · `cd lean && lake build` → clean.
  · No Lean modifications this wave — only theory-chapter
    narrative additions + archive moves.

## Remaining active research-notes (top-level)

| Class | Notes |
|---|---|
| Foundational anchors | `G29_residue.md`, `G1-G5`, `G12`, `75`, `76`, `2026-05-18_lens_emergence_path.md` |
| Methodology catalog  | `G35_chiral_cup_ring_catalog.md` |
| Geometrization open-marathon hub | `G121_dim4_self_pointing_axis.md` — chapter Citation guidance keeps this active |
| Synthesis / deep-dive | `G123_padic_next_directions.md`, `G135_padic_closure_synthesis.md`, `G136_kplus1_marathon_insights.md`, `G137_post_g134_merge_synthesis.md`, `G138_post_merge_corpus_synthesis.md` |

The synthesis notes are explicitly **not** promotion candidates
(per `theory/INDEX.md` "Active research" classification — they
annotate already-promoted chapters per the `essay` skill protocol,
they are not closure narratives).

The foundational anchors stay active by design (boot-sequence
references); they are not closure narratives either.

## Promotion log (this branch)

| Wave | Notes absorbed | Chapters extended |
|---|---|---|
| 1 | G124, G125, G127_wieferich, G127_audit, G128 | `cup.md`, `fractal.md` |
| 2 | G59, G60, G61, G62, G63, G64, G85, G86, G87  | `algebra_tower.md`, `universe_chain.md`, `atomic_constants.md` |

**Total**: 14 research notes pushed to promotion level + archived
across the branch.

## Anchor docs (next session)

| Doc | Purpose |
|---|---|
| `seed/AXIOM/05_no_exterior.md` §5 | Boot sequence |
| `research-notes/G29_residue.md` | Foundational text |
| `theory/INDEX.md` | Book map (103 chapters) |
| `theory/PROMOTION_CRITERIA.md` | H1-H4 + S1-S3 gates |
| `research-notes/INDEX.md` | Updated promotion log |
| `theory/math/cohomology/cup.md` | Lens-recipe catalog (wave 1) |
| `theory/math/cohomology/fractal.md` | Open frontier (wave 1) |
| `theory/math/cayley_dickson/algebra_tower.md` | Three fates + generic lift (wave 2) |
| `theory/math/universe_chain.md` | Orthogonal-axis tower (wave 2) |
| `theory/physics/foundations/atomic_constants.md` | Raw-side derivation (wave 2) |
| `lean/E213/ARCHITECTURE.md` | Layer spec |
| `STRICT_ZERO_AXIOM.md` | PURE catalog |
