---
name: integrate
description: Merge a feature branch into the current working branch, verify the Lean build + ∅-axiom purity, audit cross-references and numbers, update metadata, and commit. Triggered by "integrate", "branch integrate", "merge branch", "/integrate <branch-name>".
---

# Branch Integration Skill

Merge a feature branch into the current working branch, verify the build
and ∅-axiom purity, audit for consistency, update metadata, and commit.
Triggered by `/integrate <branch-name>`.

This is a **Lean + narrative** repo (source of truth `lean/E213/`,
mirrored by `theory/` + `catalogs/`, axioms/specs in `seed/`, volatile
scratch in `research-notes/`).  There is no Python `lib/` or
`experiments/` tree — verification means `lake build` + axiom scans,
not running scripts.  Never amend, never force-push.

## Procedure

### Step 1: Fetch & Inspect

```bash
git fetch origin <branch-name>
git log --oneline origin/<branch-name> --not HEAD   # new commits
git diff HEAD...origin/<branch-name> --stat          # changed files
```

Report to user:
- Number of new commits + 1-line summaries
- Key changes by tier: new/edited `lean/E213/*.lean`, `theory/` chapters,
  `catalogs/` entries, `seed/` specs
- Potential conflict areas: `CLAUDE.md`, `HANDOFF.md`,
  `STRICT_ZERO_AXIOM.md`, `catalogs/*.md`

### Step 2: Check Critical Changes

Before merging, READ and report any changes to:
- `lean/E213/**/*.lean` — flag new `sorry` / `axiom` / `import Mathlib` /
  `Classical` / `native_decide`, or any theorem dropping PURE → DIRTY.
- `theory/` — flag narrative that contradicts the Lean it mirrors
  (Lean wins).
- `catalogs/physics-constants.md` / `math-theorems.md` — flag changed
  numbers or new constants/results.
- `seed/AXIOM/*` — flag any change to the axiom set (= falsifiability
  event; surface loudly).

### Step 3: Merge

```bash
git merge origin/<branch-name> --no-edit
```

If conflicts:
1. `CLAUDE.md` / `HANDOFF.md`: combine both sides (keep latest status +
   newest content; respect CLAUDE.md ≤ 220-line budget).
2. `STRICT_ZERO_AXIOM.md` / `catalogs/*`: re-derive from Lean truth —
   after merge, regenerate with `tools/sync_strict_zero_axiom.py` rather
   than hand-merging rows.
3. `theory/` chapters: read both versions, keep the one consistent with
   the merged Lean; never keep narrative that the Lean contradicts.

### Step 4: Verify — build + purity (NOT scripts)

```bash
cd lean && lake build 2>&1 | tail -20      # must complete successfully
bash tools/kernel_regress.sh               # Term/ ring stays 0-axiom
python3 tools/scan_all_axioms.py           # tree-wide PURE/DIRTY survey
```

A merge that breaks the build or introduces an axiom-dirty theorem is
**not** integrated — fix on the session branch before continuing.

### Step 5: Consistency Audit (Quick)

Run the cheap cross-reference + number checks (see the
`verify-consistency` skill, Phases 2 + 4):

1. **Cross-refs**: scan for `lean/E213/...lean`, `theory/...md`,
   `seed/...md` paths introduced by the merge that don't resolve.
2. **Numbers**: grep key values (1/α_em, N_U = 5²⁵, α_GUT, η_B, Ω_Λ,
   Cabibbo λ = 5/22) across `catalogs/`, `README.md`, `CLAUDE.md` — all
   agree?
3. **Tier discipline**: did the merge park closed-topic narrative under
   `research-notes/G##` instead of `theory/`?  (promotion candidate)

### Step 6: Update Metadata

Update these to reflect merged content:
- `HANDOFF.md` — current state, open problems (or run the `handoff` skill).
- `STRICT_ZERO_AXIOM.md` — re-sync PURE/DIRTY catalog.
- `catalogs/*.md` — new atomic integers / constants / results (or run the
  `catalog-sync` skill).
- `INDEX.md` of any sub-tree that gained/lost files.

### Step 7: Commit & Push

```bash
git add -A
git commit -m "Merge <branch-name>: <1-line summary>

<what was merged, conflicts resolved, audit fixes>

https://claude.ai/code/<session-url>"

git push -u origin <current-branch>
```

### Step 8: Close GitHub Issues (if any)

If the branch has associated GitHub issues, use the `mcp__github__*`
tools: find related issues, comment with the integration result, close
if completed.

## Rules

- **Never force-push or amend.** Always new commits.
- **Build + purity gate the merge.** A red `lake build` or any new
  axiom-dirty theorem blocks integration until fixed.
- **Lean wins** over narrative on any disagreement introduced by the merge.
- **Report conflicts honestly.** Don't silently drop changes.
- **Update ALL metadata.** Stale catalogs / HANDOFF are worse than none.
- **Re-sync, don't hand-merge** `STRICT_ZERO_AXIOM.md` / `catalogs/` —
  use the sync tools so they match Lean truth.

## Output Format

After completion, report:

```
## <branch-name> Integration Complete

| Item | Result |
|------|--------|
| **New commits** | <count + summaries> |
| **Conflicts resolved** | <details or "none"> |
| **Build / purity** | lake build ✓ · 0 axiom-dirty ✓ |
| **Audit fixes** | <details or "no issues"> |
| **Metadata updated** | <HANDOFF / catalogs / INDEX> |
```
