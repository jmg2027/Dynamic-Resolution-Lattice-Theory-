# Session Handoff — 2026-05-23

## Branch

`claude/research-notes-promotion-1BsIr` — multi-session marathon
to push active `research-notes/` top-level items to promotion
level per `theory/PROMOTION_CRITERIA.md`.

## This session — promotion wave (4 absorbed + 1 audit closed)

### Absorbed into theory chapters

| Note | Target chapter | Section added |
|---|---|---|
| `G125_lens_recipe_cup_catalog.md` | `theory/math/cohomology/cup.md` | "Lens-recipe catalog — finite enumeration of admissible cups" — Mirror / Sym / Catalog recipes + `catalog_dispatch` universal closure (8 PURE across 3 files) |
| `G124_n_u_family_cross_field_connections.md` | `theory/math/cohomology/fractal.md` | Open frontier: "Cross-field cross-imports at `(d, n) = (5, 2)`" — seven independent readings, 10 concrete extension directions |
| `G127_base_5_wieferich.md` | `theory/math/cohomology/fractal.md` | Open frontier: "Base-5 Wieferich primes" — `{20771, 40487}` (OEIS A123693); Lean-deferred (kernel-impractical) |
| `G128_affine_plane_K25.md` | `theory/math/cohomology/fractal.md` | Open frontier: "Affine-plane reading at `(d, n) = (5, 2)`" — `F_5[x, y] / (x^5 − x, y^5 − y)` sub-ideal correspondence question |

All four source notes moved to `research-notes/archive/`.

### Audit closed

`G127_promotion_readiness_audit.md` — all five tracked marathons
(G122 / G126 / G128 / G129 / G130) promoted in prior sessions.
Closure summary added at the top of the doc; archived.

## Build + purity check

  · `cd lean && lake build` → clean.
  · `tools/scan_axioms.py` on the three Cup files (`LeibnizMirror`,
    `LeibnizSym`, `LeibnizCatalog`) → 8 PURE / 0 DIRTY.

## Remaining active research-notes (top-level)

After this wave the top-level scratchpad holds only the
foundational anchors + synthesis notes + the Geometrization
open-marathon hub:

| Class | Notes |
|---|---|
| Foundational anchors | `G29_residue.md`, `G1-G5`, `G12`, `75`, `76`, `2026-05-18_lens_emergence_path.md` |
| Methodology catalog  | `G35_chiral_cup_ring_catalog.md` |
| Number-systems / topology cross-cutting | `G37-G50`, `G59-G64`, `G62-G64`, `G87`, `G85`, `G86` |
| Cup-Δ open conjecture | `G86_self_referential_lex_cup_leibniz.md` |
| Geometrization open-marathon hub | `G121_dim4_self_pointing_axis.md` — chapter `theory/math/geometrization_conjecture.md` Citation guidance explicitly sanctions this note as the active R1+ / open-frontier / side-observation record |
| Synthesis / deep-dive | `G123_padic_next_directions.md`, `G135_padic_closure_synthesis.md`, `G136_kplus1_marathon_insights.md`, `G137_post_g134_merge_synthesis.md`, `G138_post_merge_corpus_synthesis.md` |

The synthesis notes are explicitly **not** promotion candidates
(per `theory/INDEX.md` "Active research" classification — they
annotate already-promoted chapters per the `essay` skill protocol,
they are not closure narratives).

## Citation surface — no breakage

Citations from Lean docstrings / other notes referencing the
archived notes still resolve via `research-notes/archive/` paths.
`theory/INDEX.md` "Open research directions" row trimmed to leave
only `G121` (which intentionally remains active per chapter
Citation guidance).

## Recently closed (carry-over from prior sessions)

See git log + prior HANDOFFs for the §7 cardinality cut-off
marathon (291 PURE / 0 DIRTY across 10 Fractal files), the G132
K_{3,2}^{(c=2)} higher cohomology chapter family (19 files / 231 PURE),
the G134 cardinality-cut-off-applications chapter, the G130
modulus-structure standalone chapter, and the post-merge audit /
purity passes.

## Anchor docs (next session)

| Doc | Purpose |
|---|---|
| `seed/AXIOM/05_no_exterior.md` §5 | Boot sequence |
| `research-notes/G29_residue.md` | Foundational text |
| `theory/INDEX.md` | Book map (103 chapters) |
| `theory/PROMOTION_CRITERIA.md` | H1-H4 + S1-S3 gates |
| `research-notes/INDEX.md` | Updated promotion log |
| `theory/math/cohomology/cup.md` | Lens-recipe catalog section (this session) |
| `theory/math/cohomology/fractal.md` | Open frontier (3 new sub-items this session) |
| `theory/math/geometrization_conjecture.md` | G121 open-marathon hub chapter |
| `lean/E213/ARCHITECTURE.md` | Layer spec |
| `STRICT_ZERO_AXIOM.md` | PURE catalog |
