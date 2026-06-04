---
name: org-audit
description: Repository organization + narrative-hygiene audit. Strips dated migration/changelog/legacy-deletion cruft from docstrings and md bodies; checks INDEX accuracy (counts, missing entries); sweeps stale references to moved/renamed/deleted files; finds flat-directory clustering + orphan-file sorting opportunities (build-verified, path=namespace preserved); relocates generic infra theorems to the Meta layer and dedups duplicated lemmas. Triggered by "org audit", "tidy", "organization audit", "cleanup", "정리", "분류", "narrative hygiene", "relocate infra".
---

# org-audit — organization + narrative hygiene

Keep the corpus readable, navigable, and honestly-current.  Lean + narrative
repo: `lean/E213/` is truth, `theory/` mirrors it by path, `catalogs/`/`seed/`
support it.  See `PROCESS.md` for tier roles and `lean/E213/ARCHITECTURE.md`
for the ring + cluster layout.

## What this audits (and fixes)

### 1. Narrative hygiene (CLAUDE.md "Legacy-deletion narration" failure mode)
Docstrings and md **bodies** must describe the *current* state — no
changelog, no "previously X now Y", no dated migration narration, no "moved
from / promoted / 폴드 / 흡수 / consolidation note".  Provenance lives in git.
```bash
grep -rnE "20[0-9][0-9]-[0-9]{2}-[0-9]{2}|moved from|promoted from|formerly|previously|consolidation note|폴드|흡수|Phase [0-9]|Session [A-Z]" \
  --include=*.md --include=*.lean lean/E213 theory seed catalogs | grep -vi "git log" | head -60
```
Rewrite each to current-state-only.  Keep genuine attributions (originator
quotes, spec citations); drop dated cleanup narration.

### 2. INDEX accuracy
Every INDEX count + listing must match reality.
```bash
for d in theory/math theory/physics theory/lens theory/meta theory/essays; do
  echo "$d: $(find $d -name '*.md' ! -name INDEX.md | wc -l) chapters"
done
# then diff against the numbers/listings stated in each INDEX.md and theory/INDEX.md
```
Fix stale totals, group-counts ("Infrastructure (10)" but 20 listed), and add
chapters missing from the INDEX. Verify every INDEX link resolves.

### 3. Stale-reference sweep
After any move/rename/delete, no doc may point at the old path.
```bash
# example: a relocated module/file
grep -rn "Lib/Math/<OldName>\b" --include=*.md --include=*.lean . | grep -v "<NewPath>"
```
Repoint or drop each. (Cross-corpus markdown links: recompute the relative
path per source file — a per-file `os.path.relpath` script, not a blind sed,
since relative-link direction depends on the linking file's location.)

### 4. Flat-directory clustering + orphan sorting (build-verified)
A directory with many ungrouped files / loose content files is a smell.
Group sub-trees into thematic super-clusters and sort orphan files into
sub-trees. **theory/ mirrors lean/ by path**, so reorganize *both* together.

For `lean/E213/Lib/`: the path **is** the namespace. Moving a sub-tree under
a cluster is one uniform rename per module:
```bash
git mv Lib/Math/<X> Lib/Math/<Cluster>/<X>
git mv Lib/Math/<X>.lean Lib/Math/<Cluster>/<X>.lean   # the umbrella
# word-boundary-guarded so prefixes (Mobius213 vs Mobius213ModFive) don't collide:
grep -rlZ "E213\.Lib\.Math\.<X>\b" --include=*.lean --include=*.md . ../ \
  | xargs -0 -r sed -i "s/\bE213\.Lib\.Math\.<X>\b/E213.Lib.Math.<Cluster>.<X>/g"
grep -rlZ "Lib/Math/<X>\b" --include=*.lean --include=*.md . ../ \
  | xargs -0 -r sed -i "s#Lib/Math/<X>\b#Lib/Math/<Cluster>/<X>#g"
```
**Critical lessons:**
- The single dotted rename fixes imports + namespaces + opens + qualified
  refs together (Lean uses the same dotted name for all).
- Scope greps to the whole repo (incl. `lean/E213.lean` ROOT aggregator —
  it sits one level *above* `E213/` and is easy to miss).
- For name-collision clusters (Analysis, Cohomology, Geometry, Probability,
  Combinatorics, Tactic) the eponymous sub-tree stays at the cluster root;
  siblings fold under it (minimal churn).
- `cd lean && lake build E213` + `python3 tools/scan_axioms.py <module>` after
  **each** cluster; commit per cluster so each stage is green and reviewable.
- `theory/` cluster dirs are lowercase of the Lean CamelCase (e.g.
  `theory/math/numbersystems/` ↔ `Lib/Math/NumberSystems/`).

### 5. Split / merge — respect the mirror discipline
- **Do not merge/delete** a chapter that mirrors a distinct closed Lean
  sub-tree (verify `ls lean/E213/Lib/.../<Name>/`) — that breaks path-mirror.
- Genuine merges: same-topic-evolution files; near-duplicate INDEX stubs.
- Genuine splits: one file covering 2+ unrelated topics.
- Synthesis chapters (consolidating across sub-trees) legitimately coexist.

### 6. Infra-theorem relocation + dedup
Generic, domain-agnostic helpers buried in content files belong in `Meta/`.
```bash
# generic Nat/Int/List plumbing that should be in Meta/Nat, Meta/Int213, Meta/Tactic.List213
grep -rn "theorem nat_\|theorem int_\|length_append\|mul_assoc\|add_left_cancel" \
  --include=*.lean Lib/Math Lib/Physics | head
```
Move the whole file (or dedup a lemma against an existing canonical Meta one),
keeping names stable where consumers reference them; re-export rather than
rename when in doubt. Build + purity after each.

## Verify + commit
`cd lean && lake build E213` green; `scan_axioms.py` shows 0 dirty on touched
framework modules; all INDEX links + cross-refs resolve. Commit in coherent
batches (one cluster / one concern per commit). Report a Was→Now summary.
