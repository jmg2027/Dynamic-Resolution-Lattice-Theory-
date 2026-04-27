# doc-sync skill

description: Full documentation sync — verify and fix HANDOFF.md / CLAUDE.md
  against actual repo state. Checks file counts, Korean text, branch name,
  sub-project structure. Triggered by "doc sync", "document sync",
  "sync docs", "문서 싱크".

## What This Skill Does

1. **Count actual files** in each documented directory
2. **Diff against HANDOFF.md and CLAUDE.md** stated counts
3. **Scan for remaining Korean** text in all tracked files
4. **Report discrepancies** and fix them in-place
5. **Commit + push** all fixes

## Procedure

### Step 1 — Gather actual counts
```bash
# Lean subdirs
find lean/E213 -name "*.lean" | sed 's|lean/E213/||' | cut -d'/' -f1 \
  | sort | uniq -c

# Docs
for d in blueprints/meta blueprints/math blueprints/physics \
          seed research-notes catalogs tools; do
  echo "$d: $(ls $d/*.md 2>/dev/null | wc -l) md"
done
ls papers/*.tex | wc -l   # tex count
ls papers/*.md  | wc -l   # extra md in papers/
ls books/       | wc -l
```

### Step 2 — Scan for Korean text
```bash
grep -r --include="*.lean" --include="*.md" --include="*.tex" \
     --include="*.py" -P "[\x{AC00}-\x{D7A3}]" . --exclude-dir=.git -l
```
If any files found → translate comments/prose to English (never touch code).

### Step 3 — Check HANDOFF.md currency
- Branch name matches `git branch --show-current`
- File counts match Step 1 results
- Precision table matches CLAUDE.md Key Precision Results

### Step 4 — Check CLAUDE.md currency
- Repository Architecture section matches actual dirs
- Sub-project table: mark dirs that do not exist with `(planned)`
- Key Constants / Key Precision Results up to date

### Step 5 — Fix and commit
Edit HANDOFF.md and CLAUDE.md to correct any discrepancies found.
```bash
git add -A
git commit -m "doc-sync: update HANDOFF.md + CLAUDE.md to match repo state

https://claude.ai/code/session_014iVdG5BRNSBagdWbWhvfEG"
git push
```

### Step 6 — Report
Print a two-column table: **Was** vs **Now** for every item changed.
If nothing changed, print "All docs in sync."
