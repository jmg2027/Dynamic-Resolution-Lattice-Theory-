---
name: autonomous-research
description: Continue 213 / DRLT research autonomously — audit stale references, supplement Lean theorems, discover ideas, develop new ∅-axiom results. Designed to be invoked repeatedly across sessions to keep momentum on the same branch. Triggered by "autonomous research", "auto research", "자율 연구", "자율적으로 진행", "자율 마라톤", "자율로 진행".
---

# Autonomous research session

Open-ended research mode.  Pick high-leverage targets without asking
for direction at each step.  The goal is to make the codebase
incrementally cleaner, more consistent, and richer in proven
theorems each invocation.

## Operating principles

  1. **Read first, write later.**  At session start: skim
     `HANDOFF.md` for recent work and open threads; skim
     `CLAUDE.md` for guardrails; check `git log --oneline -10`
     to see the branch trajectory.
  2. **Small, verified commits.**  Every change must build
     (`tools/full_build.sh` or at minimum `lake build E213`).
     Every new theorem must be ∅-axiom (verified by
     `#print axioms <name>`).
  3. **Commit each independent unit.**  Don't pile unrelated
     refactors into one commit.  Each commit should describe
     a single thought: a bugfix, a theorem, a sweep.
  4. **Update HANDOFF.md at the end.**  Always.

## Target hunting

Pick targets in order of decreasing leverage (do one per
invocation, or as many as fit before context pressure):

### Tier A: Latent bugs / broken state

  - `lake build E213.Lib.Math E213.Lib.Physics` (or
    `tools/full_build.sh`) — must build clean.  If anything
    breaks, fix BEFORE anything else.
  - `python3 tools/layer_audit.py` — report any layer violations.
  - Search for stale module paths: `grep -rn "deleted module" --include="*.lean" --include="*.md"`.
  - Files importing non-existent modules — script:
    ```bash
    find lean/E213 -name "*.lean" | while read f; do
      grep "^import E213\." "$f" | while read imp; do
        target=$(echo "$imp" | sed 's/^import //; s|\.|/|g')
        [ ! -f "lean/${target}.lean" ] && echo "BROKEN: $f -> $imp"
      done
    done
    ```

### Tier B: Stale documentation

  - `git grep "(2026-0[0-4]\|2025-)" -- '*.md' | head` — old date
    markers that may indicate stale claims.
  - `git grep "deferred\|defer\|≤ {propext"` — references to the
    deprecated tier or open work that may be done.
  - File count drift: re-run `find lean/E213/<Ring> -name "*.lean" | wc -l`
    against `INDEX.md`, `README.md`, `CAPSTONE_INDEX.md`.
  - Orphan sub-files: any `<X>.lean` umbrella missing imports of
    siblings under `<X>/`.

### Tier C: Theorem development

For each new theorem candidate:

  1. State it in terms of existing PURE primitives.
  2. Prove via 213-native tactics:
     - `Meta.Tactic.NatHelper.*` instead of propext-tainted core
     - `Meta.Tactic.List213.*` instead of `List.*`
     - `Option.noConfusion` instead of `simp` on impossible branches
     - `Nat.succ_pred_eq_of_pos` instead of `Nat.sub_add_cancel`
     - See `seed/CLOSED_FORM_SPEC.md` "Propext-avoidance trick set"
  3. Verify via `#print axioms <name>` (must be "does not depend
     on any axioms").
  4. Add to `CAPSTONE_INDEX.md` if it's a top-level result.

Productive theorem patterns from past sessions:

  - **Injectivity / surjectivity** of named functions
    (e.g. `numeral_injective`, `chartChain_injective`,
    `value_surjective_on_ge_one`).
  - **Bijection closures** — pair a forward direction with its
    reverse + injectivity (e.g. `parseTree_printTree` +
    `printTree_parseTree` + `printTree_injective`).
  - **Range characterisations** — formal "set X equals
    Range(function)" via surjectivity + co-domain restriction
    (e.g. `Lens.leaves_view_surjective_on_ge_one`).
  - **Universal/specific bridges** — generic statements then
    instantiated to concrete cases.

### Tier D: Ideas (open exploration)

Look for stated-but-not-yet-proven claims in:

  - `research-notes/2026-05-18_lens_emergence_path.md` §5 Options
  - `seed/AXIOM/09_chart_relativity.md` §9.{1, 2, 3, 4}
  - `seed/CLOSED_FORM_SPEC.md` "Future work"
  - `STRICT_ZERO_AXIOM.md` "Future cleanup"

If a claim is stated abstractly and a concrete Lean realisation
is missing, that's a candidate target.

## Workflow per invocation

```
0. Read HANDOFF.md  (1 message)
1. Tier A — audit; fix any breakage discovered
2. Tier B — pick 1–3 stale-doc items; fix
3. Tier C — pick 1–3 theorem candidates; prove + commit
4. Tier D — if context permits, develop one idea further
5. Update HANDOFF.md, push to branch
```

## Branch discipline

  - Stay on the current feature branch (per CLAUDE.md
    "Git Development Branch Requirements").
  - Don't create PRs unless explicitly asked.
  - Push at the end of each substantial unit of work.
  - Never amend, never force-push.

## Idle / context-budget mode

If context is getting tight (you can tell because tool calls are
recapping or you're losing track of earlier file states):

  - **STOP doing new work**.  Commit what's done.
  - Write a thorough HANDOFF.md entry naming exactly which thread
    was last in progress.
  - Push.
  - Reply to the user with a 5-line summary of the iteration.

The skill is most valuable when invoked **regularly** (every
session start) rather than as a one-shot.  The HANDOFF.md is the
baton.
