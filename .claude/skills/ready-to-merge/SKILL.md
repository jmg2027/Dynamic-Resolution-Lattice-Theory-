---
name: ready-to-merge
description: Comprehensive pre-merge audit of the entire DRLT-213 repo —
  logical consistency, layer architecture, stale references, deprecated
  content deletion, build cleanliness, and final commit hygiene.  Goes
  beyond verify-consistency by also reorganizing files, deleting
  superseded artifacts, and ending with a "merge-ready" verdict.
  Triggered by "ready to merge" / "ready to merge", "merge ready",
  "pre-merge", "final audit", "ready audit".
---

# Ready-to-Merge — Comprehensive Pre-Merge Audit

A merge-readiness pass that fuses every directional principle Mingu has
established across sessions.  Output: a branch that is *actually* ready
to merge into main — not just "tests pass" but "every claim, every
file location, every cross-reference is right, and nothing deprecated
is still in the working tree."

This skill is **mutating** — it edits, moves, deletes.  Every action
gets a commit.  No silent changes.

---

## Directional principles (load these into context first)

Before running any check, internalize these from `CLAUDE.md` +
`lean/E213/ARCHITECTURE.md` + prior-session memory:

  1. **One vertical axis** — Kernel/Firmware/Hypervisor/Meta/App.
     Every `.lean` file lives at one layer mechanically determined by
     its import closure.  Run `tools/layer_audit.py` for the truth.
  2. **Math/ and Physics/ only** as topical roots.  No Research/,
     Infinity/, Tactic/, Tools/ at top level — those were dissolved.
     If they reappear, demote them.
  3. **Path = namespace, ideally.**  `tools/sync_namespaces.py`
     enforces.  Intentional exceptions (e.g., `namespace E213.Tactic`
     short-form for the omega213 macro at `Kernel/Tactic/Omega213.lean`)
     must be documented.
  4. **Sub-cluster early** (≥3 thematically-related files), not late.
     Don't merge files just to reduce count.
  5. **Delete deprecated content with no active dependents.**  But
     preserve a README marker pointing to the recovery commit.
  6. **0 sorry, 0 axiom (≤ {propext, Quot.sound})**, 0 Mathlib import,
     0 Classical, 0 native_decide.  `purity-check` skill covers this.
  7. **Theory-side three-pillar uniqueness** (AXIOM.md §1.1/§1.2/§1.3):
     minimality below, universality sideways, forced-shape above.
  8. **Self-correct on misclaims.**  If a previous commit said "X was
     deleted" but X exists, fix the claim, don't fix the file.

---

## Phase 0: Context absorption (do not skip)

  - Read root `HANDOFF.md` for current branch state.
  - Read `lean/E213/ARCHITECTURE.md` (canonical layer doc).
  - Read `CLAUDE.md` "Repository Organization Philosophy".
  - `git log --oneline -20` to see recent intent.
  - `git status` — there must be no uncommitted clutter.

If the working tree is dirty, **stop and ask** — don't sweep over
unfinished work.

---

## Phase 1: Mechanical layer audit

```bash
python3 tools/layer_audit.py
```

  - **Violations** (`path_layer < natural_layer`): MUST be 0.  If not,
    fix them.  Either move the file to its natural layer, or move the
    dependency back down (delete dead imports first — they often hide
    the real layer).
  - **Downgrade hints** are informational unless a sub-cluster span
    becomes obviously incoherent.
  - **Topical-cluster depth (§6.2)**: WIDE-span sub-folders (≥15) are
    sub-clustering candidates.  Don't sub-cluster aggressively; only
    if the span signals genuinely separable topics.

---

## Phase 2: Stale path / ref sweep

Search-and-destroy across the entire repo for references that no
longer resolve:

```bash
# Top-level dirs that should NOT exist anymore:
test -d lean/E213/Research && echo "STALE: Research/ still exists"
test -d lean/E213/Infinity && echo "STALE: Infinity/ still exists"
test -d lean/E213/Tactic   && echo "STALE: Tactic/ still exists"
test -d lean/E213/Tools    && echo "STALE: Tools/ still exists"
test -d lean/E213/OS       && echo "STALE: OS/ still exists"

# Deprecated marker dirs anywhere inside the tree:
find lean/E213 -type d -name Research && echo "STALE Research/ marker"

# Phase{N}/ session-numbered names (per CLAUDE.md philosophy):
find lean/E213 -type d -regex '.*/Phase[0-9].*' && echo "STALE Phase{N}/"
```

For every match, distribute the contents into the correct topical
sub-cluster of the natural layer.  Use `git mv` + tree-wide
`grep -rl ... | xargs sed -i 's/old/new/g'`.

Also sweep `.md` docs for dead path refs:

```bash
grep -rln "Phase[2-4]/" *.md guide/ catalogs/ books/ blueprints/ seed/
grep -rln "/OS/" *.md guide/ catalogs/ books/ blueprints/ seed/
grep -rln "AUDIT_GUIDE\.md" *.md guide/ lean/E213/
grep -rln "CLAUDE-213\.md" *.md seed/ lean/E213/
grep -rln "book/chapters/" *.md seed/      # book/ has no chapters/ now
grep -rln "papers/[a-z].*\.tex" *.md       # papers/ holds only README.md
grep -rln "E213\.Research\." lean/         # post-reorg: 0
grep -rln "E213\.Infinity\." lean/         # post-reorg: 0
grep -rln "E213\.Tools\." lean/            # post-reorg: 0
```

Each non-zero result = a stale ref.  Fix the doc to reference the
current location, OR remove the dead reference.  Distinguish between:

  - **Renamed/moved** — fix the path
  - **Truly deleted** — note the deletion + git commit hash

Do **NOT** silently delete a reference; if a doc claims something
exists, verify it.  If you previously made a misclaim about deletion,
correct the claim *first*.

---

## Phase 3: Build & purity

```bash
cd lean
rm -rf .lake/build && lake build 2>&1 | tail -5     # forced fresh build
```

Result must be `Build completed successfully.`  If build fails:

  - **Source error in a moved file** → fix imports/opens
  - **Source error pre-existing** but masked by olean cache → fix it
    NOW (often the reorg surfaces these).  Common patterns:
    - `unknown identifier 'X'` from `open E213.Y.X` partial-resolution
      — replace with the actual full namespace
    - `unknown namespace` from a file that was renamed but its
      consumers still reference the old name

After build clean:

```bash
bash tools/kernel_regress.sh           # Kernel/ stays 0-axiom
python3 tools/audit_axioms.py          # tree-wide axiom survey
```

Validation Standard target: every public theorem ≤ {propext, Quot.sound}.

---

## Phase 4: Doc cross-check

Three documents must agree at all times:

  - `lean/E213/ARCHITECTURE.md` (canonical)
  - `CLAUDE.md` "Repository Architecture" + "Lean Library Structure"
  - `HANDOFF.md` "Architecture" summary

For each, verify:

  - Top-level dirs listed match `ls lean/E213/`
  - Layer descriptions match what `tools/layer_audit.py` reports
  - File-count rows match `find lean/E213/X -name "*.lean" | wc -l`
  - "Where the old top-level dirs went" map (if present) is current

Then check seed/ ↔ Lean alignment:

  - `seed/AXIOM/09_lean_correspondence.md` §9 path references point to files that exist
  - `lean/E213/AUDIT.md` cross-refs are at current paths
  - `lean/E213/AUDIT.md` recommendation status reflects whether each
    has been done / superseded / deferred
  - `seed/INDEX.md` table rows match `ls seed/`
  - `seed/PAPER1.md` archival header (if present) is honest about
    what's been re-built post-deletion vs. still archival

If a seed/ doc claims something is "deleted" or "moved", verify with
`find` / `git log -- <path>`.  Self-correction over self-confidence.

---

## Phase 5: Catalog & narrative sync

  - `catalogs/*.md` — every `import E213.X.Y.Z` line must resolve
  - `books/{math,physics}/*.md` — same
  - `blueprints/{math,meta,physics}/*.md` — same
  - `guide/*.md` — Lean theorem refs use current paths
  - `CAPSTONE_INDEX.md` (root) — every theorem path resolvable
  - `STRICT_ZERO_AXIOM.md` (root) — every theorem path resolvable
  - `theory/**/*.md` — every Lean module / theorem citation resolves;
    every `research-notes/G##` provenance pointer hits an existing
    file (now in `research-notes/archive/` for promoted topics)

For each broken ref: fix the path or remove the line.

### Phase 5.5: Three-tier alignment (per `CLAUDE.md` "Three-tier
discipline" + `theory/PROMOTION_CRITERIA.md`)

For each closed Lean sub-tree (PURE + categorically closed):

  - Does a `theory/<mirror-path>/<chapter>.md` exist?
  - If NO + sub-tree satisfies H1-H4 + S1-S3 → flag as a promotion
    candidate (do NOT block merge; record in verdict's "Outstanding"
    section).  Promotion is best done in a dedicated commit, not
    folded into a merge audit.
  - If YES → verify the chapter's "Lean source" section file paths
    + theorem names still resolve.

For each `research-notes/G##` cited from Lean docstrings:

  - Is the note still at `research-notes/G##_*.md` (active scratch)
    or moved to `research-notes/archive/`?
  - If archived → Lean citation must use the `archive/` path.  If
    a `theory/<mirror>` chapter exists for the same topic → update
    the Lean citation to point at the chapter (primary) with optional
    parenthetical archive reference (deep-dive).

  ```bash
  # Find Lean citations to research-notes that no longer exist at top level:
  for ref in $(grep -rhoE "research-notes/G[0-9]+_[A-Za-z0-9_]+\.md" lean/ | sort -u); do
    [ ! -f "$ref" ] && echo "STALE: $ref"
  done
  ```

Action: bulk sed for each stale path (`research-notes/G##_*.md` →
`research-notes/archive/<subdir>/G##_*.md` OR
`theory/<mirror>/<chapter>.md`).

---

## Phase 6: Deprecated content deletion

Per CLAUDE.md: *"Deprecated content with no active dependents should
be deleted, not kept just in case."*

For each candidate (use `git log --diff-filter=D --summary` to
discover history of deletions), check:

  1. Are there active dependents?  `grep -rln "<basename>" .` or
     specific `import <ns>` checks.
  2. If yes — leave it (or update the dependents).
  3. If no — delete with `git rm`, but leave a README/marker if the
     directory itself is being preserved as a recovery pointer
     (per CLAUDE.md "preserve a README pointing to the recovery
     commit").

Common keep-anyway exceptions:

  - `seed/PAPER1.md` — cited from ~25 Lean files via `PAPER1 §X.Y`
    markers; never delete
  - `papers/README.md` — historical marker for deleted archive

---

## Phase 7: Naming + sync_namespaces

```bash
python3 tools/sync_namespaces.py            # dry-run
python3 tools/sync_namespaces.py --apply --include-rust
```

After the apply, all namespaces should match their paths.  Intentional
exceptions (Tactic short-form for omega213, etc.) are listed in
`ARCHITECTURE.md`.

---

## Phase 7.5: Narrative tightness pass

Per Mingu's directive: documents should read as a coherent
current-state narrative, not as duct-taped accumulation of
session-by-session additions.  Four sub-checks:

### 7.5.a Narrative coherence (body text)

Read the body of each long-lived `.md` (`HANDOFF.md`,
`theory/**/*.md`, `STRICT_ZERO_AXIOM.md`, `seed/*.md`, etc.) end
to end.  Ask: does it read as a thesis being explained, or as a
log of additions?

Symptoms of duct-tape accumulation:
  - Sections labelled "this stretch", "this session", "(added)",
    "(originally proposed as ...)", "retained for reference"
  - Sub-totals tied to a specific point in time ("17 PURE",
    "Phase 1 partial") that no longer match current state
  - Multiple parallel "status" paragraphs from different sessions
  - Tables ordered by creation time instead of by topical structure
  - Process-flow language ("we then derived...", "in the next phase
    we...") that belongs in commit messages, not narrative

Fix by rewriting affected sections to read as a current-state
exposition.  The git history preserves the process; the document
shouldn't try to.

### 7.5.b Archive / change-history / old-tech residue

Search for body-text references to deprecated structure that
*should* live only in git history or archive directories:

```bash
grep -rln "this stretch\|this session\|in progress\|IN PROGRESS\|Phase [0-9]\+ partial\|retained for reference\|originally proposed" \
  *.md theory/ seed/ guide/ catalogs/ blueprints/ books/ 2>/dev/null
grep -rln "previously named\|formerly called\|was renamed\|used to live" \
  *.md theory/ seed/ guide/ 2>/dev/null
```

Each hit: decide if it's
  - a genuine historical pointer (e.g., "originally proposed as
    G120, renumbered to G122") — OK to keep if the *current*
    statement is clear and the history is one-line
  - duct-tape residue — delete or rewrite

### 7.5.c Completed-item deletion

Per CLAUDE.md "delete deprecated with no active dependents":
items that are done (closed campaigns, completed phase outlines,
"next-session start" instructions for sessions that finished, etc.)
should be **gone**, not preserved as comments.  In particular:

  - HANDOFF.md's "Next-session start" sections from sessions that
    already happened → delete
  - "Phase outline" lists where every phase is done → delete the
    outline, leave only the closure summary
  - "Open frontier" / "TODO" / "Pending" items that have been
    closed → remove from the document (the closure should be
    visible elsewhere in the same document, e.g. in the Key
    results table)
  - Per-session "this stretch added X, Y, Z" notes once the items
    are reflected in the main structure

The git log is the change history; the document is the current
state.

### 7.5.d Split / merge structural review

For each multi-file sub-tree and each large single file (>1000 lines):

**Split candidate questions**:
  - Does the file mix two conceptually distinct stories
    (e.g., inverse story + sqrt story + concrete instances)?
  - Would a reader looking for X have to scroll past unrelated Y?
  - Are the two halves used by mostly disjoint downstream consumers?

If yes to several: propose split (do not necessarily execute —
record as a deferral if there's no downstream need yet).

**Merge candidate questions**:
  - Are two adjacent small files (< 200 lines each) doing the
    same kind of work?
  - Is one file effectively a single-purpose extension of another?
  - Would merging reduce import lines without producing a
    sprawling >1500-line monster?

If yes: propose merge.  Default-no unless the case is strong;
"sub-cluster early" (per CLAUDE.md) usually wins over "consolidate
late."

Symptoms of a directory needing reorganisation:
  - Files with topically-overlapping names (`Foo.lean`, `FooExt.lean`,
    `FooMore.lean`) → merge or sub-cluster
  - One file is the "everything else" bucket → identify a sub-theme
    to extract
  - File count is large (≥ 15) and the natural sub-themes haven't
    been split out yet → sub-cluster

For this audit, **record findings, don't execute splits/merges**
unless they're trivially clarifying.  Significant restructuring
deserves its own commit chain after the merge.

## Phase 8: Final commit hygiene

  - Commit messages of recent work explain WHY, not just WHAT
  - No "wip" / "tmp" / "test" commits sitting around
  - No commits with `--no-verify`, `--no-gpg-sign`, or `--amend`
    against pushed history
  - Working tree clean
  - `git fetch && git status` shows branch is ahead-only of origin

If everything passes, the final summary commit (if anything was
fixed) ends with the verdict.

---

## Phase 9: Verdict

Produce a summary report (post in chat, do NOT write to disk unless
user asks).  Format:

```
## Pre-merge audit — <branch>

Checks passed:
  ✓ tools/layer_audit.py: 0 violations / N files
  ✓ rm -rf .lake/build && lake build: clean
  ✓ tools/kernel_regress.sh: K/K theorems 0-axiom
  ✓ Stale-path sweep: 0 hits
  ✓ ARCHITECTURE / CLAUDE / HANDOFF cross-check: aligned
  ✓ seed/ ↔ Lean: consistent
  ✓ Catalogs / books / blueprints / theory/: 0 broken refs
  ✓ Three-tier alignment: 0 stale research-notes/ citations,
                          0 broken theory/ → Lean refs
  ✓ Working tree clean, branch ahead-only

Fixes applied this pass:
  - <list of commits>

Outstanding (informational, NOT blockers):
  - <e.g. 19 downgrade hints, 1 WIDE sub-cluster Cohomology>
  - <e.g. 3 promotion candidates: X/Y/Z PURE-closed sub-trees
    awaiting theory/ chapter>

Verdict: READY TO MERGE
```

If any check fails:

```
Verdict: NOT READY — <count> blocker(s)

Blockers:
  ✗ <description>

Recommended next action: <concrete step>
```

---

## Edge cases

  - **lake build cached but source broken.**  Always `rm -rf
    .lake/build` first; otherwise stale oleans hide source-level
    errors that would surface on someone else's machine.
  - **Korean / English mixed user instructions.**  Mingu mixes both;
    parse intent, not literal phrasing.  Examples seen in this repo:
    "지울거 있음 지우던가 해주삼" = delete deprecated content;
    "쓸모없어지거나 잘못된건 지워" = delete useless or wrong content;
    "수평은 매스/피직스만 냅두고" = keep only Math/Physics horizontal.
  - **Don't introduce abstractions to "make it cleaner".**  Per
    CLAUDE.md: "Three similar lines is better than a premature
    abstraction."
  - **Always commit each phase separately** so the audit trail is
    reviewable.  Don't squash 9 phases into one giant commit.
  - **If you find a misclaim from a prior session** (e.g., "notes/
    deleted" when it's actually `research-notes/` renamed), fix the
    claim immediately — that's a self-correction commit, not a
    structural change.
  - **80-line hook**.  This repo enforces a 80-line limit on Write.
    For larger files use Write (≤80) + Edit append pattern in
    smaller chunks (~30 lines per Edit).

---

## Skills this composes with

  - `verify-consistency` — narrower scope (numerical / notational);
    ready-to-merge runs it as a sub-step in Phase 4
  - `purity-check` — feeds Phase 3 axiom-budget verification
  - `doc-sync` — runs after structural moves to update READMEs
  - `lake-build-verify` — Phase 3 build sub-step
  - `handoff` — produce HANDOFF.md *after* ready-to-merge passes,
    not during

Sequence in a typical session:
```
... structural work ...
ready-to-merge      ← this skill (audit + fix + verify)
handoff             ← only if merge actually happens
```

---

## Why this skill exists (provenance)

Across ~10 sessions Mingu established a consistent meta-pattern:
"don't just make tests pass — verify the whole repo is logically
consistent, every claim verified, every misplacement corrected,
every stale ref cleaned, deprecated content deleted, structural
philosophy preserved."  Examples that trained this skill:

  - OS/ retired session (Firmware/Atomicity/ + Math/Pigeonhole)
  - Phase{2,3,4}/ retirement (topical Physics/* sub-clusters)
  - layer_audit.py introduction (mechanical layer derivation)
  - Research/ marker removal (full distribution by topic)
  - notes/ → research-notes/ misclaim self-correction
  - seed/ ↔ Lean ↔ guide/ cross-doc audits

Each was a one-off application of the same underlying discipline.
This skill makes that discipline a first-class operation.
