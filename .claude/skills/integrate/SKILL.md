# Branch Integration Skill

Merge a feature branch into the current working branch, verify experiments,
audit for consistency, and commit. Triggered by `/integrate <branch-name>`.

## Procedure

### Step 1: Fetch & Inspect

```bash
git fetch origin <branch-name>
git log --oneline origin/<branch-name> --not HEAD   # new commits
git diff HEAD...origin/<branch-name> --stat          # changed files
```

Report to user:
- Number of new commits
- Key changes (new experiments, book edits, lib changes)
- Potential conflict areas (CLAUDE.md, HANDOFF.md, lib/experiment.py)

### Step 2: Check Critical Changes

Before merging, READ and report any changes to:
- `book/chapters/*.tex` — flag content changes (not just formatting)
- `lib/drlt.py` — flag formula changes (new functions, modified constants)
- `lib/experiment.py` — flag infrastructure changes

### Step 3: Merge

```bash
git merge origin/<branch-name> --no-edit
```

If conflicts:
1. For CLAUDE.md / HANDOFF.md: combine both sides (ours has latest counts, theirs has new content)
2. For lib/experiment.py: prefer the version with `_get_results_dir()` auto-detect
3. For result files: re-run experiments to regenerate
4. For book chapters: read both versions, keep the more complete one

### Step 4: Verify Experiments

Run at least 2 experiments from the merged branch to confirm:
- Import paths work
- Auto-detect results dir works
- Checks pass

```bash
python <sub-project>/experiments/<latest>.py 2>&1 | tail -8
```

### Step 5: Consistency Audit (Quick)

Check for inconsistencies introduced by the merge:

1. **Numerical**: grep key values (η_B, Ω_Λ, α_GUT) across CLAUDE.md, README.md,
   sub-project CLAUDE.md — do they all match?
2. **Experiment counts**: does root CLAUDE.md sub-project table match actual file counts?
3. **Region II language**: does any new file use "0⁺ eigenvalue" or "eigenvalue leaking"?
   Correct language: "trace redistribution via representation-theoretic channels".
4. **Naming**: do new experiment files follow `{PREFIX}_{NNN}_{description}.py`?

### Step 6: Update Metadata

Update these files to reflect merged content:
- Root CLAUDE.md: experiment counts in sub-project table
- Root HANDOFF.md: sub-project status summaries, next experiment numbers
- Sub-project CLAUDE.md: if experiment map is outdated

### Step 7: Commit & Push

```bash
git add -A
git commit -m "Merge <branch-name>: <1-line summary>

<details of what was merged, conflicts resolved, audit fixes>

https://claude.ai/code/<session-url>"

git push -u origin <current-branch>
```

### Step 8: Close GitHub Issues (if any)

If the branch has associated GitHub issues:
```
mcp__github__list_issues → find related
mcp__github__add_issue_comment → report integration
mcp__github__issue_write → close if completed
```

## Rules

- **Never force-push or amend.** Always new commits.
- **Re-run experiments** after merge if lib/ files changed.
- **Report conflicts honestly.** Don't silently drop changes.
- **Update ALL metadata.** Stale counts are worse than no counts.
- **Flag Scenario B language.** Any "0⁺ eigenvalue magnitude" → fix to "trace redistribution".
- **Preserve sub-project HANDOFF.md.** Don't overwrite detailed sub-project handoffs with summaries.

## Output Format

After completion, report:

```
## <branch-name> 통합 완료

| 항목 | 결과 |
|------|------|
| **새 실험** | <list> |
| **충돌 해결** | <details or "없음"> |
| **감사 수정** | <details or "이상 없음"> |
| **검증** | <experiment checks> |
```
