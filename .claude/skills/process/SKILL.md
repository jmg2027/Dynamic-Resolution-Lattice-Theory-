---
name: process
description: Audit and enforce the repository's tier discipline — the directory roles, the sink rule (no permanent tier cites a research-notes file), and the frontier-recording rule (every open frontier lives in research-notes/frontiers/). Promotes closed frontiers, decouples canonical→research-notes citations, records/organizes open frontiers, and prunes process-artifacts from archive/. Canonical statement is PROCESS.md. Triggered by "process", "tier discipline", "decouple", "sink check", "role audit", "frontier check", "프로세스", "디커플링", "research cycle", "프론티어".
---

# process — tier discipline + the research cycle

Canonical statement: **`PROCESS.md`** (repo root).  This skill *applies and
audits* it.  Read `PROCESS.md` first; it defines every directory's role and
the one rule below.

## The two rules being enforced

**Sink rule (closing side):**

> **No permanent tier cites a `research-notes/` file.**
> `seed/`, `lean/`, `theory/`, `catalogs/`, `book/` are permanent and may
> cite each other; `research-notes/` is a volatile sink — it cites anything,
> nothing canonical cites into it.

When content a permanent tier needs lives in a research note, **promote it**
(`theory/PROMOTION_CRITERIA.md`) into the permanent tier, then the note
records only the path, cited by nothing.

**Frontier-recording rule (opening side):**

> **Every open frontier is recorded in `research-notes/frontiers/`.**
> No open problem / conjecture / deferred direction lives only in chat, a
> commit message, or a `theory/` chapter tail — it has a note under
> `frontiers/<topic>/`, listed in `frontiers/INDEX.md`.

A chapter's "Open frontier" section may *name* the residual work, but the
frontier **lives** in `frontiers/` (where it is tracked and worked).
Together the two rules make `research-notes/` the single home of work in
motion: a frontier enters via `frontiers/`, closes in `lean/`, and is
decoupled out by promotion.

**Two things are NOT violations** (do not "fix" them):
- **Role/structure references** — a doc may name `research-notes/`,
  `research-notes/frontiers/`, `research-notes/archive/<topic>/`, or
  `research-notes/INDEX.md` to *describe the structure*.  Only specific
  **note-file** citations (`research-notes/.../<note>.md`, basename ≠
  `INDEX.md`) are violations.
- **Process tooling** — `.claude/skills/` that operate on research-notes
  (autonomous-research, handoff) are the machinery of the cycle.

## Procedure

### Step 1 — Audit the sink rule
List every permanent-tier file that cites a research-notes **note file**
(exclude directory refs and INDEX.md):
```bash
python3 - <<'EOF'
import os,re,subprocess
out=subprocess.run("grep -rn 'research-notes/[A-Za-z0-9_./-]*\\.md' --include=*.md --include=*.lean "
  "seed theory catalogs book blueprints lean rust-engine CLAUDE.md README.md "
  "STRICT_ZERO_AXIOM.md LESSONS_LEARNED.md CAPSTONE_INDEX.md 2>/dev/null",
  shell=True,capture_output=True,text=True).stdout
v=[l for l in out.splitlines()
   if (lambda m: m and os.path.basename(m.group(0))!="INDEX.md")(re.search(r'research-notes/[A-Za-z0-9_./-]+\.md',l))]
print(f"{len(v)} violations"); [print(" ",l[:140]) for l in v]
EOF
```

### Step 2 — Fix each violation (PROSE-SAFE — hard-won lessons)
For each citation, drop the `research-notes/...md` pointer and make the
sentence stand on its own.  The canonical content already exists (or should
be promoted); the note is recoverable from git.

- **DO** edit prose per-sentence so it reads cleanly ("X lives in `note`." →
  "X." or repoint to the permanent home, e.g. a `seed/`/`theory/`/`lean/`
  path or theorem name).
- **DO** delete pure-citation bullet lines / provenance bullets.
- **DO** remove pure-citation parentheticals `(`note`)` whole.
- **NEVER** run a whole-file whitespace collapse (`[ \t]{2,}→ `) — it
  destroys Lean indentation and breaks the build.
- **NEVER** strip directory/INDEX refs (Step-1 rule already excludes them).
- Boot anchors (CLAUDE.md) repoint to the permanent home, e.g.
  `research-notes/G29_residue.md` → `seed/AXIOM/01_residue.md`.

Safe automation for the mechanical subset (bullets + multi-line pure-cite
parentheticals only; never whitespace-collapse): adapt the verified script
pattern in this repo's history (commit messages "process: …decouple…").
Hand-edit the inline-sentence cases.

### Step 3 — Run the cycle (promotion = decoupling)
When a `research-notes/frontiers/<topic>/` arc closes ∅-axiom in `lean/`:
1. Promote per `theory/PROMOTION_CRITERIA.md` (write the `theory/` chapter
   /essay, update `catalogs/`, land quantitative results in
   `STRICT_ZERO_AXIOM.md` / `catalogs/`).
2. Confirm Step 1 reports **no** permanent-tier citation of the source notes.
3. `git mv` the source notes to `research-notes/archive/<topic>/`; remove the
   topic from `research-notes/frontiers/INDEX.md`.

### Step 3.5 — Audit the frontier-recording rule
Every open frontier must have a home in `frontiers/`.  Two cheap checks:
```bash
# (a) theory chapter "Open frontier" sections — each should correspond to a
#     frontiers/ topic group (the chapter names it; frontiers/ tracks it):
grep -rlE "^#+ .*Open frontier" theory --include=*.md
# (b) HANDOFF open problems that name no frontier note → must be recorded:
sed -n '/^## Open Problems/,/^## /p' HANDOFF.md | grep -iE "open|conjecture|frontier" | head
```
For any open direction stated in a chapter tail, a handoff, a commit
message, or surfaced in this session that is **not** in `frontiers/`:
record it — create `frontiers/<topic>/<note>.md` (or append a section to the
right topic's note) and register it in `frontiers/INDEX.md` with its core
open problem + the closure record (where the proven side lives, if any).
Do not leave an open frontier homeless.

### Step 4 — Keep research-notes/ a clean sink
- **Top-level** holds only boot-sequence anchors + `INDEX.md` + `frontiers/`.
- **`frontiers/`** = the live open board, grouped by topic (`frontiers/INDEX.md`).
- **`archive/`** = closed material, grouped by topic.
- **Prune** pure-process artifacts that don't even warrant archiving (dated
  audit snapshots, resolved-build-gate records, promotion checklists,
  non-research drafts) — but KEEP anything a permanent tier or seed spec
  still cites by path (verify before deleting: `grep -rl <name> seed catalogs lean`).

### Step 5 — Verify + commit
```bash
cd lean && lake build E213 2>&1 | tail -2        # green (Lean unaffected by doc edits, but confirm)
cd .. && python3 -c "import subprocess,re,os; ..."  # re-run Step 1 → 0 in the tier you cleaned
git add -A && git commit -m "process: <what was decoupled/promoted/pruned>

https://claude.ai/code/<session-url>"
git push -u origin <current-branch>
```

### Step 6 — Report
Print: sink-rule violations found → fixed (by tier), any frontiers recorded
(open directions that had no `frontiers/` home), any promotions run, any
archive prunes (with the kept-because-cited exceptions). If a tier is fully
decoupled, say so; if inline-sentence sites remain, report the count for the
next iteration.
