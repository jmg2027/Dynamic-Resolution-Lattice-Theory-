# CONSOLIDATION_PROTOCOL.md — leaf-directory consolidation procedure

Procedure for cleaning up a Physics/ (or Math/) leaf directory that
contains exploration-trace files: V1/V2/V3 variants, Phase3*, Tight/
Tighter/Sharp progressions, Milestone, WithTail, Unified, etc.

Derived from the 2026-05-05 `Physics/FamousCoincidences/` consolidation
(commits `396585c` rename + `623e377` absorption).  The same procedure
applies to all subsequent leaves.

## Core insight (don't forget)

*"Naming pattern alone does NOT determine what to do."*  V137 might be
a version-number progression OR a "1/137" digit-start workaround.
Phase3* might be a stale exploration trace OR a meaningful sub-topic.
**Read the actual statements + check destinations before deciding.**

The most common state: the file's content is *already absorbed
elsewhere in a more natural form* — the leaf is a deep-research
exploration trace that survived past its absorption.  Default
expectation: most leaf-directory variant content is redundant.

## 13-step procedure

### Phase A — inventory

1. **List files**: `ls <leaf>/*.lean`.  Note total count + naming
   patterns (V*, Phase*, *Tight*, *Sharp*, *Milestone*, *V2*).

2. **Read headers** (~25 lines each): identify per-file topic.
   Cluster by apparent role (variant? supplement? canonical?
   exploration trace?).

3. **Theorem inventory**: `grep -E "^theorem |^def " <files>`.
   Capture every public name + its statement line.

### Phase B — destination discovery

4. **Statement-level grep**: for each substantive theorem
   statement (e.g. `NS * NT = 6`, `d^(d²)`, `NT² = 4`), count
   other files that state the same:

       grep -rl "<statement-pattern>" lean/E213/ --include="*.lean"

   High count (10+) means widely-duplicated atomic identity → likely
   already canonicalized in `Kernel/MonomialAxioms.lean` or
   `Physics/AtomicCorrespondences/AtomicSuperCatalog.lean`.

5. **Theorem-name grep**: for each theorem name (e.g. `koide_atomic`),
   find other files using the same name:

       grep -rln "<thm-name>" lean/E213/ --include="*.lean"

   Hit in another file ⇒ name conflict OR canonical absorption already
   exists.  Both are signals to delete the duplicate.

6. **Caller / import discovery**:

       grep -rln "import E213.<leaf-namespace>" lean/E213/ --include="*.lean"

   List all consumers.  For each, check whether the import is
   actually used (theorem references) or just transitive.

### Phase C — classification

7. For each theorem in the leaf, classify into one of:

   - **(a) Redundant — already absorbed**: same statement (or
     stronger) exists in a natural topical file.  → Delete.
   - **(b) Unique with natural destination**: rare statement that
     belongs in a specific topical file (e.g. SU(5) reps in
     `YangMills/SU5Roots`).  → Move + delete.
   - **(c) Unique multi-reading capstone**: bundled `∧` of multiple
     atomic readings (no single natural home).  → Absorb into
     `Physics/AtomicCorrespondences/AtomicSuperCatalog.super_catalog`
     (or a designated cluster catalog).
   - **(d) Real version-progression artifact**: stale Tight/Sharp/
     Phase3 form genuinely superseded by a Master/Capstone in the
     same dir.  → Delete the older, keep the canonical.

8. **Read destination files** (Phase C-(b),(c)) tail-end to confirm
   the namespace structure + check there's no name collision.

### Phase D — execution (single atomic commit)

9. **Absorb** content per the classification:
   - Append theorems to chosen destination file (preserve the
     statement text; rename if there's a collision).
   - Update the destination's docstring/header to mention the
     absorption (optional but helpful for navigation).
   - Extend any `super_catalog` capstone with the new conjuncts.

10. **Delete leaf files**: `git rm <file>` for each.  If the
    entire directory becomes empty, the directory is auto-removed
    by git.

11. **Update callers**: rewrite `import` lines to point at the new
    destination (or delete the import if no actual usage).

12. **Update navigation docs**:
    - `lean/E213/INDEX.md` — sub-tree list, file counts
    - `lean/E213/ARCHITECTURE.md` — sub-cluster list
    - `CAPSTONE_INDEX.md` — old leaf entries → new destination entries
    - `README.md` (root) — Physics sub-tree mention if present
    - `research-notes/AUDIT_PASS_<date>_lean.md` — file-count table
    - per-directory INDEX.md if exists

### Phase E — verification

13. **Build + axiom invariants**:

       cd lean && lake build              # must report "Build completed successfully."
       python3 tools/scan_all_axioms.py   # PURE/DIRTY/sealed counts

    Real DIRTY count must not increase.  Sealed-by-design count
    may shift if seal entries reference paths that moved.

14. **Single atomic commit** with message structure:

        Leaf N — <leaf>/ <action: rename | absorb | delete>

        <user directive verbatim if pivotal>
        Investigation outcome: <one-paragraph finding>
        Destinations + classifications: <table>
        Removed: <list>
        Updated: <list>
        Build clean.  No theorem signatures changed.

## Common patterns observed

| Pattern | Likely meaning | Action |
|---|---|---|
| `V137`, `V137Tight`, `V137Tighter` | progressive precision attempts toward 1/α_em | usually consolidate into `MasterCapstone` (or whichever holds full term-stack) |
| `Phase3Derivation`, `Phase3Sharp`, `Phase3Manifesto` | stale Phase-3 marathon trace | check whether absorbed; if yes, delete |
| `Bound`, `BoundTight` | tight bound progression | keep tighter version, delete looser if not cited |
| `Mass`, `MassFinitist` | finitist re-derivation of same observable | check semantic equivalence; consolidate |
| `MagicNumbers`, `MagicNumbersAtomic`, `MagicNumbersFalsifier`, `MagicNumbersPhase3Derivation` | observable + atomic reading + falsifier + phase trace | typically: atomic + falsifier are real artifacts, Phase3 is trace |
| `V1`, `V2`, `V3`, `V4` (no number-encoding role) | could be sub-topics OR variants | inspect each file's actual content |
| `WithTail`, `WithoutTail`, `Unified` | term-coverage variants | usually `MasterCapstone` is the canonical with all terms |

## What NOT to do (lessons from FamousCoincidences/)

  - Do NOT rename V1-V4 to topic names without first checking
    whether content is absorbed elsewhere.  (Did this in commit
    `396585c` — had to revert/re-do via `623e377`.)
  - Do NOT preserve a "deep research artifact" file just because
    its statements are correct.  If the statements are absorbed,
    the file is dead weight.
  - Do NOT skip the destination grep — relying on filenames alone
    misses the `koide_atomic` (same theorem name in two files,
    one a duplicate).
  - Do NOT do this in multiple commits — atomic single commit
    keeps revertability + git mv history clean.

## When to ask the user

  - Theorem statement is unique AND has no obvious natural home
    (genuinely orphan).
  - Destination decision is between two roughly-equal candidates.
  - Deletion would lose information that nothing in the codebase
    ever recomputes.
  - The leaf encodes a *physical claim* that you suspect is wrong
    (e.g., a Phase3 derivation that contradicts the corrected spec).

## Cross-reference

  - 2026-05-05 audit pass: `research-notes/AUDIT_PASS_2026-05-05_*.md`
  - First leaf execution: commits `396585c` (rename) + `623e377`
    (absorption + deletion).
