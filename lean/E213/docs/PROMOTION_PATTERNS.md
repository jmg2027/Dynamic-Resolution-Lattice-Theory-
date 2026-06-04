# PROMOTION_PATTERNS.md — three shapes of `research-notes/` → `theory/` promotion

Operational reference for promoting a Lean sub-tree to a `theory/`
chapter per `theory/PROMOTION_CRITERIA.md`.  Companion document to
`CONSOLIDATION_PROTOCOL.md` (leaf cleanup) and `HIERARCHICAL_PLACEMENT.md`
(directory placement).

PROMOTION_CRITERIA defines **when** a promotion is valid (H1-H4 hard
+ S1-S3 soft criteria).  This document classifies **how** the work is
done, identifying three distinct shapes the source state can take.

## The three patterns

| # | Pattern | Source state | Outcome | Example chapter |
|---|---|---|---|---|
| 1 | **Multi-note absorption** | One or more closed G-notes covering one topic | Combine into one chapter; `git mv` originals to `research-notes/archive/<topic>/` | `theory/math/cohomology/hodge_conjecture.md` (6 notes G6-G11 → 1) |
| 2 | **Narrative-from-scratch** | Lean tree closed without source research notes | Read the Lean tree; write narrative; nothing to archive | `theory/physics/symmetry/c3_chain.md` (Lean-only 18-phase work) |
| 3 | **Mixed-status absorption** | Active multi-topic catalog where only some sub-topics are closed | Extract closed sub-topics; the catalog **stays active** with a status tracker | `theory/physics/alpha_em/precision_derivation.md` (G35 §C1+§C5 extracted; G35 itself stays) |

These three exhaust the cases observed to date.  New cases that
don't fit go through `AskUserQuestion` before acting.

---

## Pattern 1 — Multi-note absorption

### When

- A `research-notes/G##_*.md` cluster (≥ 1 note, usually 3+) all
  describe one Lean sub-tree that is now closed.
- The notes are **scratch + closure narrative for that sub-tree
  only** — they don't double as broader catalog reference.
- No active conjectures remain in the notes.

### Steps

1. Survey the source notes (read first ~40 lines of each + headers).
2. Verify all H1-H4 criteria pass on the target Lean sub-tree.
3. Write `theory/<mirror-path>/<chapter>.md` synthesizing the notes
   + Lean tree state.
4. `git mv research-notes/<cluster>/* research-notes/archive/<topic>/`
   (create the archive subdirectory if needed).
5. Update the archived `INDEX.md` (if any) with a "promoted to
   `theory/<path>`" header.
6. Bulk sed Lean docstring citations:
   `research-notes/<cluster>/G##` → `research-notes/archive/<topic>/G##`
   (keep deep-dive citations) AND optionally add primary pointer
   to `theory/<path>`.
7. Update the Lean sub-tree's `INDEX.md` companion section to
   point at the theory chapter as **primary narrative**, archived
   notes as **deep-dive reference**.
8. Update `theory/INDEX.md` and the relevant `theory/<area>/INDEX.md`.

### Example trace (Hodge, commit `905c09a2`)

```
research-notes/hodge/ (6 G-notes + INDEX)
  → research-notes/archive/hodge/
  + theory/math/cohomology/hodge_conjecture.md (new, 253 lines)
  + 12 Lean docstrings updated via bulk sed
  + lean/E213/Lib/Math/Cohomology/HodgeConjecture/INDEX.md "Companion narrative" added
```

### Pitfalls

- **Don't archive prematurely**: if any note describes work that is
  still open (e.g., a still-active conjecture), pattern 3 applies
  instead.  Check for "open", "deferred", "Step N+ open" markers.
- **Don't drop content**: the chapter must cover what the notes covered.
  Compress, don't omit.  If a note has historical-only material,
  keep it in the archived note + reference from the chapter's
  "Research-note provenance" section.

---

## Pattern 2 — Narrative-from-scratch

### When

- A Lean sub-tree is closed but has **no source research notes**.
  Work was done directly in Lean across one or more sessions, with
  only HANDOFF.md / commit messages as contemporaneous narrative.
- Common for marathon-style multi-phase work where the user
  prioritized Lean over notes.

### Steps

1. Verify H1-H4 on the Lean sub-tree.
2. Read the Lean sub-tree's `INDEX.md` (if any) + key phase files +
   master capstone(s).
3. Read HANDOFF.md sections describing the work + relevant commit
   messages (`git log --oneline -- <sub-tree>`).
4. **Recover the narrative** by synthesizing: what the master theorem
   says, how the phases compose, what physical/mathematical
   interpretation each phase carries.
5. Write `theory/<mirror-path>/<chapter>.md`.
6. Update the Lean sub-tree's `INDEX.md` to point at the chapter as
   primary narrative.
7. No archive step — nothing to move.
8. Update `theory/INDEX.md` and the relevant `theory/<area>/INDEX.md`.

### Example trace (C3 chain, commit `3f9d1942`)

```
research-notes/ (no source notes for C3 chain)
lean/E213/Lib/Physics/Symmetry/ (24 files; INDEX was stale at 6 files!)
  → theory/physics/symmetry/c3_chain.md (new, 313 lines)
  + Symmetry/INDEX.md rewritten (6 → 24 file listing in 3 sub-sections)
  + C3ChainCapstone.lean docstring adds theory pointer
```

### Pitfalls

- **The Lean tree's `INDEX.md` is often stale** — it was written
  before the new phases were added.  Rewrite it as part of the
  promotion; don't trust it as a complete source.
- **Master capstone explains less than narrative needs**: the
  capstone is a 12-conjunct AND of decidable facts; the narrative
  must explain why each conjunct matters + how they compose.
- **HANDOFF.md is volatile**: by the time you read it, the relevant
  section may have been compressed.  Read git log of HANDOFF if needed.

---

## Pattern 3 — Mixed-status absorption

### When

- A research note covers a **multi-topic catalog or framework**
  with several open + closed sub-topics.
- The framework note has value **beyond any single sub-tree** —
  archiving it would lose context that future work still needs.
- Closure is **per-conjecture** or **per-step**, not whole-document.

### Signature artifacts

- The note has section structure `§C1`, `§C2`, ..., `§C6` (or `§A`,
  `§B`, ...) indexing distinct topics/conjectures.
- Lean docstrings cite specific sections of the note (`§C##`), not
  the whole note.
- Multiple Lean sub-trees cite the same note from different angles.

### Steps

1. Identify exactly **which** sub-topic(s) are closed.  List them.
2. Verify H1-H4 on the **closed** Lean sub-tree(s) corresponding to
   those sub-topics.  Other sub-topics' status is irrelevant for
   THIS promotion.
3. Write `theory/<mirror-path>/<chapter>.md` covering only the
   closed sub-topics, with an **explicit "Open frontier" section**
   listing the deferred Step N+ work within those sub-topics.
4. **Do NOT archive the source note.**  Update it with a new
   `§0.5 Promotion status` section (or extend existing) tracking
   per-sub-topic destination:

   ```
   | §C1 | Closed Steps 1-4 | theory/<path>/<chapter>.md |
   | §C2 | Open Steps 5+    | (still in this note)        |
   | §C3 | Closed elsewhere | theory/<other-path>          |
   ```

5. Add explicit "Research-note provenance" section in the new
   chapter listing what was absorbed + what stays + cross-links
   to other chapters that absorbed other sub-topics.
6. Lean docstring citations to specific sections (`§C##`) of the
   note **remain valid** — they reference the conjecture statement,
   not the closure proof.  Add the chapter as *primary derivation*
   reference if the file is part of the closed work.

### Example trace (α_em, commit `a3f2b585`)

```
research-notes/G35_chiral_cup_ring_catalog.md (stays active, 17 domains)
  + §0.5 Promotion status (new) — tracks C1/C5 (→ chapter), C3 (→ other), C2/C4/C6
lean/E213/Lib/Physics/AlphaEM/ (23 files)
  → theory/physics/alpha_em/precision_derivation.md (new, 261 lines)
  + Open frontier: C1 Step 5+, C5 Step 7+ (within chapter)
  + AlphaEM/INDEX.md narrative pointer added
  + G35 citations in Lean docstrings UNCHANGED (still valid)
```

### Pitfalls

- **Don't archive the catalog note**: it still serves uses beyond
  the chapter.  The chapter's scope is narrower than the note's.
- **Don't list out-of-scope sub-topics as "open"**: they may be
  closed elsewhere (e.g., G35 §C3 is closed in `theory/physics/
  symmetry/c3_chain.md`).  Cross-link to the right destination.
- **Maintain the §0.5 tracker** as further sub-topics get
  promoted; otherwise the catalog drifts out of sync.

---

## Decision tree

```
Is the Lean sub-tree closed (H1-H4 pass)?
├── No → not promotion-eligible
└── Yes
    ├── Are there source research notes for this sub-tree?
    │   ├── No → Pattern 2 (narrative-from-scratch)
    │   └── Yes
    │       ├── Do the notes describe only this sub-tree?
    │       │   ├── Yes (notes are scratch for the closure)
    │       │   │   → Pattern 1 (multi-note absorption)
    │       │   └── No (notes span multiple topics/sub-trees)
    │       │       → Pattern 3 (mixed-status absorption)
```

## Destination variants

The three patterns assume the chapter destination is
`theory/<math|physics>/<mirror-of-lean/E213/Lib/path>/<chapter>.md`.
In rare cases, the closed work doesn't live in `lean/E213/Lib/`:

### Variant A — `theory/meta/` for tools-mirror chapters

When the closed work is a **Python tool suite** under `tools/`
analyzing the Lean tree (rather than a Lean library), the chapter
goes to `theory/meta/<topic>.md`.

H1 / H2 adapt:
- H1' (instead of `scan_axioms.py` on Lean module): scanners pass
  `--help` / produce expected reports
- H2' (instead of Lean module build): `lake build` still clean
  (scanners can be re-run without regression)

H3 / H4 + S1-S3 stay the same.

**Example**: `theory/meta/scanner_suite.md` — 11 Python scanners +
1 Lean meta file; ~1,800 LOC Python; mirrors
`tools/{ast_*,syntax_*,falsifier_*}.py`.

The pattern (1, 2, or 3) used within the variant is the same; only
the destination directory changes.  Document the variant in the
chapter's "Lean source" section (rename to "Source" or "Tools /
Lean source").

### Boundary case — `lean/E213/docs/` for operational meta-docs

Documents like `CONSOLIDATION_PROTOCOL.md` and this file
(`PROMOTION_PATTERNS.md`) are operational meta-references, not
chapters.  They live in `lean/E213/docs/`, NOT `theory/`, because
they describe how to **maintain** the tree, not what it **contains**.

## When none of the patterns fit

If a case arises that doesn't match patterns 1-3 (any destination
variant), **stop and ask via `AskUserQuestion`**.  Do not invent a
fourth pattern silently.  Document the new case + outcome in this
file (extend the table at
top, add a new section) so future agents have the precedent.

## Cross-reference

- `theory/PROMOTION_CRITERIA.md` — H1-H4 + S1-S3 gate spec
- `theory/INDEX.md` — current chapter list (kept up-to-date)
- `CLAUDE.md` "Three-tier discipline" — high-level rule
- `lean/E213/docs/CONSOLIDATION_PROTOCOL.md` — sibling: leaf cleanup
- `lean/E213/docs/HIERARCHICAL_PLACEMENT.md` — sibling: directory shape

## Provenance

Three patterns were extracted from three sequential promotions
completed 2026-05-21 / 2026-05-22 on branch
`claude/research-notes-organization-Gr3Tp`:

- Commit `905c09a2`: Hodge (pattern 1)
- Commit `3f9d1942`: C3 chain (pattern 2)
- Commit `a3f2b585`: α_em (pattern 3)

Future promotions should reference this file by pattern number in
their commit messages.
