---
name: handoff
description: "Generate HANDOFF.md for the next session. Gathers branch, recent work, open problems, precision table, and file map into a structured document. The session-start hook auto-detects this file. Triggered by: 'handoff' / 'handoff', 'handoff', 'hand off', 'session wrap-up' / 'session wrap-up', 'session wrap', 'wrap up session'."
---

# Generate HANDOFF.md

Create a handoff document that lets the next session resume with full
context. The session-start hook (`.claude/hooks/session-start.sh`)
auto-detects `HANDOFF.md` and alerts Claude to read it.

## Procedure

### Step 1: Gather context (read-only)

Collect ALL of the following. Do NOT skip any.

```
1. git branch --show-current          → current branch name
2. git log --oneline -20              → recent work summary
3. git status                         → any uncommitted changes
4. CLAUDE.md "Open Problems" section  → what's unsolved
5. CLAUDE.md "Key Precision Results"  → current precision table
6. CLAUDE.md "Experiment Catalog"     → latest experiment numbers
7. git diff --stat HEAD~5..HEAD       → files changed recently
```

For each experiment created/modified this session:
```
results/EXP_NNN_*.txt  → read last 15 lines (summary)
```

For any research notes created/modified:
```
research-notes/*.md    → read first 30 lines (key findings)
```

### Step 2: Write HANDOFF.md

Write to the repo root. Use EXACTLY this structure:

```markdown
# Session Handoff — YYYY-MM-DD

## Branch
`branch-name` (pushed/not pushed, ahead by N commits)

## What Was Done This Session
### 1. [Major achievement] (EXP_NNN, X/Y ✓)
- Key finding 1
- Key finding 2

### 2. [Second achievement]
...

(List ALL meaningful work. Be specific about numbers and results.)

## Current Precision Results (0 free parameters)
| Observable | DRLT | Observed | Error |
|-----------|------|----------|-------|
(Copy from CLAUDE.md, include any NEW results added this session)

## Open Problems (Priority Order)
### 1. [Highest priority problem]
Description. Current status. Suggested approach.

### 2. ...
(Copy from CLAUDE.md, update status based on this session's work)

## Unresolved from This Session
(Anything attempted but not completed. Dead ends discovered.
 Hypotheses that were tested and failed.)

## Next Experiment
EXP_NNN (available).

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: theory/<path> ← research-notes/<source>
  (or "none")
- **Promotion candidates**: PURE-closed Lean sub-trees lacking
  theory/ chapters.  Check `theory/PROMOTION_CRITERIA.md`.
- **Active scratchpad**: top-level research-notes/G## still
  in-progress.

## File Map
```
path/to/new_file    ← description
path/to/modified    ← what changed
```
```

### Step 3: Ensure everything is committed

```bash
git add HANDOFF.md
# Also add any other uncommitted files from this session
git status  # verify clean
git commit -m "Handoff: [1-line summary of session]"
git push
```

### Step 4: Verify the loop

Confirm that CLAUDE.md contains the "Session Start" section:
```markdown
## Session Start
- **If HANDOFF.md exists, read it FIRST** before doing anything else.
```

If missing, add it at the top of CLAUDE.md (after `# CLAUDE.md`).

## Rules

- **Be honest about failures.** If something was attempted and didn't
  work, document it so the next session doesn't repeat the attempt.
- **Include specific numbers.** "0.11% error" not "good match".
- **List files, not concepts.** Every new/modified file should appear
  in the File Map with its purpose.
- **Open problems must be actionable.** "Higgs mass 3% gap" is good.
  "Things to think about" is not.
- **The handoff must be self-contained.** Reading ONLY HANDOFF.md
  (without any other context) should give enough information to
  resume productive work.
