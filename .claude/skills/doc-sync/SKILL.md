---
name: doc-sync
description: Full documentation sync — verify and fix HANDOFF.md / CLAUDE.md against actual repo state. Checks file counts, branch name, residual Korean in artifacts, and constant/precision tables. Triggered by "doc sync", "document sync", "sync docs", "문서 싱크".
---

# doc-sync skill

Verify and fix `HANDOFF.md` / `CLAUDE.md` (and other top-level docs)
against the actual repo state.  Lean + narrative repo: `lean/E213/` is
the source of truth, `theory/` + `catalogs/` mirror it.

## What This Skill Does

1. **Count actual files** in each documented directory
2. **Diff against HANDOFF.md and CLAUDE.md** stated counts
3. **Scan for residual Korean** in English-only artifacts (Lean / commits)
4. **Report discrepancies** and fix them in-place
5. **Commit + push** all fixes

## Procedure

### Step 1 — Gather actual counts
```bash
# Lean subdirs (the source of truth)
find lean/E213 -name "*.lean" | sed 's|lean/E213/||' | cut -d'/' -f1 \
  | sort | uniq -c
find lean/E213 -name "*.lean" | wc -l            # total

# Docs / specs / scratch
for d in blueprints/meta blueprints/math blueprints/physics \
          seed catalogs research-notes theory tools; do
  echo "$d: $(find $d -name '*.md' 2>/dev/null | wc -l) md"
done
ls books/ papers/ 2>/dev/null                    # papers/ = README.md only now
```

### Step 2 — Scan for residual Korean in artifacts
Repo artifacts (Lean, commits) are English-only; chat may be KO/EN.
Korean prose quotes in `.md` are allowed *with* translation.
```bash
grep -rlP "[\x{AC00}-\x{D7A3}]" --include="*.lean" lean/   # Lean = English only
```
If any `.lean` file matches → translate comments to English (never touch code).

### Step 3 — Check HANDOFF.md currency
- Branch name matches `git branch --show-current`
- File counts / module map match Step 1
- Precision / open-problems reflect the latest commits (volatile doc)

### Step 4 — Check CLAUDE.md currency
- Boot sequence + "Entry points" paths all resolve (`ls` each)
- "Repository organization" + three-tier sections match actual dirs
- Hard-rules table matches the wired hooks in `.claude/settings.json`
- Key constants / DRLT Validation Standard up to date
- Respect the ≤ 220-line budget (size-guard hook)

### Step 5 — Fix and commit
Edit the docs to correct any discrepancies found.
```bash
git add -A
git commit -m "doc-sync: update HANDOFF.md + CLAUDE.md to match repo state

https://claude.ai/code/<session-url>"
git push -u origin <current-branch>
```

### Step 6 — Report
Print a two-column table: **Was** vs **Now** for every item changed.
If nothing changed, print "All docs in sync."
