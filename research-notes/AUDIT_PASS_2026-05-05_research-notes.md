# AUDIT_PASS 2026-05-05 — research-notes/

Directory survey of `research-notes/` for the audit pass following the
RESOLUTION_LIMIT_SPEC + AUDIT_PASS prompt.  Records what is active,
what is closed, and what is a candidate for archive.  No content is
deleted in this pass — only classified.

## Top-level files (active, closed-but-cited, archive-candidate)

| File | Theme | Status | Recommendation |
|---|---|---|---|
| `G29_residue.md` | The residue of pointing — minimum-commitment foundational text | **Active** (boot-sequence read) | Keep as-is |
| `G28_every_pattern_present.md` | Every stateable pattern lives in 213 (corrects G27) | **Active** | Keep as-is |
| `G30_pattern_catalog_synthesis.md` | Pattern catalog synthesis (metaformalization arc closure) | **Active** | Add to INDEX (currently unindexed) |
| `75_semantic_atom.md` | 213 as the atom of meaning + existence | Foundational thesis | Keep as-is |
| `76_ultimate_ouroboros.md` | `Prop` instance via `propAsDistinguishing` | Formalization companion to 75 | Keep as-is |
| `G1_universal_lens.md` | Universal-lens unification | Closed in `Meta/UniversalLens*.lean` | Keep as record |
| `G2_trajectory_principle.md` | 4-insight unification on Raw trajectory | Foundational principle (partially formalised) | Keep as-is |
| `G3_raw_as_universal_trajectory.md` | Raw = free magma on 2 generators | Foundational; formal anchor in `Firmware/Raw.lean` | Keep as-is |
| `G4_chiral_phase_duality.md` | d=5 dual views (chiral / phase) | Foundational; anchor in `Math/Trajectory/PhaseChiralBridge.lean` | Keep as-is |
| `G5_213_as_sublanguage.md` | 213 as the sublanguage of mathematics | Meta-principle | Keep as-is |
| `G6_hodge_213_translation.md` | Hodge translation strategy | Closed in `Math/Cohomology/HodgeConjecture/Foundation/*` | Keep as record |
| `G7_lens_initiality_cup_blueprint.md` | Lens initiality + cup-product blueprint | Closed in `Foundation/LensCata.lean` | Keep as record |
| `G8_hodge_213_bridge_to_standard_math.md` | Bridge to standard cohomology | Hodge work | Keep as record |
| `G9_hodge_conjecture_complete.md` | Hodge conjecture closure narrative | Hodge work | Keep as record |
| `G10_post_hodge_program.md` | Post-Hodge program (17 classical theorems formalised) | Closed (138+ strict ∅-axiom theorems) | Keep as record |
| `G11_galois_at_eighty.md` | Galois angle | Historical-philosophical note | Keep as record |
| `G12_layered_api_classification.md` | Layered API classification (Hypervisor) | Architecture deliverable | Keep as-is |
| `anthropic_outreach_draft.md` | Outreach draft (not sent) | Draft (Mingu Jeong author) | Keep as-is, leave unindexed (private draft) |

## Cluster-merge candidates

The Hodge cluster (G6, G7, G8, G9, G10) is six separate notes (~1000+
total lines) all describing one closed program (`Math/Cohomology/
HodgeConjecture/`).  Per CLAUDE.md "Sub-cluster as soon as 3+
thematically-related files appear" + "INDEX.md per non-trivial
sub-tree (≥ 5 files)":

  **Recommendation**: introduce `research-notes/hodge/` sub-tree
  collecting G6-G11 (six files) + an `INDEX.md` summarising the
  closed program.  Title in top-level INDEX as a single line
  "Hodge program closure (six notes)" instead of six separate rows.

  Status: **deferred** — would touch the file paths cited from Lean
  modules (cite-chain audit needed first).  Logged here for the
  follow-up architecture session.

## INDEX.md gaps to fix in this pass

  1. `G30_pattern_catalog_synthesis.md` is missing from
     `research-notes/INDEX.md`'s top-level table.
  2. `archive/INDEX.md` heading was renamed in this audit pass
     ("Finitism conviction" → "Resolution-limit early framing");
     other archive entries are fine.

## Subdirectory status

  - **`audit/`** — G17 empirical audit + G18-G27 classification
    iterations.  Conceptually superseded by G28+G29; raw audit data
    + tactic catalogues retained as evidence base.  See
    `audit/INDEX.md` for navigation.  No action needed.

  - **`archive/`** — closed historical drafts (pre-G era 17/19/30,
    A1/B/C/D/E/F series + diamond brainstorm trio).  All formalised
    or superseded; preserved as record of path.  No action needed in
    this pass.

## Wording compliance (post sweep)

After the 2026-05-05 wording sweep:

  - `G6_hodge_213_translation.md` (lines 53, 255) — UPDATED to point
    at `seed/RESOLUTION_LIMIT_SPEC.md`.
  - `G12_layered_api_classification.md` (line 486) — UPDATED with
    resolution-limit framing.
  - `INDEX.md` (line 48) and `archive/INDEX.md` (line 24) — UPDATED.

Outstanding G-note text that still uses ZFC-fluent vocabulary
("infinite-dimensional", "completed-infinity", etc.) is acceptable
when the surrounding text is *describing* the standard-math object
that 213 routes around (e.g. G6 §1-§7 introduces standard Hodge
machinery before discussing 213's translation).  No mass replacement
required.
