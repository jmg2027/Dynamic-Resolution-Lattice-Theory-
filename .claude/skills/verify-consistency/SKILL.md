---
name: verify-consistency
description: Deep self-consistency audit of the entire repo. Checks build + ∅-axiom purity, cross-references, three-tier discipline, numbers, file organization, and documentation. Fixes all inconsistencies found. Triggered by "verify" / "verify", "consistency" / "consistency", "consistency check", "verify", "clean", "theorem verify" / "theorem verify", "audit".
---

# Self-Consistency Verification & Correction

Rigorous self-consistency audit of the DRLT 213 repo.  This is a
**Lean + narrative** repo: the source of truth is `lean/E213/`, mirrored
by `theory/` (narrative) and `catalogs/` (constants / results); `seed/`
holds the axiom + spec corpus; `research-notes/` is volatile scratch.
There is **no** `book/chapters/*.tex`, `lib/*.py`, or `experiments/`
tree — when narrative and Lean disagree, **Lean wins** (CLAUDE.md).

Every claim must be internally consistent, every cross-reference must
resolve, every number must match everywhere it appears, every file must
be in the right tier.  Fix everything found.

## Severity Levels

| Level | Meaning | Action |
|-------|---------|--------|
| **CRITICAL** | Axiom-dirty theorem, broken build, contradicts an axiom | Fix immediately |
| **ERROR** | Broken cross-reference, number mismatch, wrong file path | Fix in this pass |
| **WARNING** | Stale doc count, suboptimal organization, tier drift | Fix if easy |
| **INFO** | Minor suggestion, promotion candidate, future work | Log only |

---

## Phase 1: Build & ∅-axiom purity (the falsifiability contract)

```bash
cd lean && lake build 2>&1 | tail -20    # must end "Build completed successfully"
```

The ∅-axiom standard (CLAUDE.md "∅-axiom standard") is THE standard.
In `lean/E213/`:

```bash
# Source-level forbidden patterns (hooks block these on write; re-verify)
grep -rIn --include='*.lean' -wE 'sorry|admit'  lean/   # comments only OK
grep -rIn --include='*.lean' 'native_decide'    lean/   # comments only OK
grep -rIn --include='*.lean' 'open Classical|Classical\.' lean/
grep -rIn --include='*.lean' 'import Mathlib'    lean/   # must be 0
```

Any real (non-comment) hit = CRITICAL.  Then the canonical audits:

```bash
python3 tools/scan_axioms.py <module>     # single module #print axioms
python3 tools/scan_all_axioms.py          # tree-wide PURE/DIRTY survey
bash    tools/kernel_regress.sh           # Term/ kernel ring stays 0-axiom
```

- `STRICT_ZERO_AXIOM.md` is the canonical PURE/DIRTY catalog.  Re-sync
  with `tools/sync_strict_zero_axiom.py` and confirm no theorem silently
  dropped from PURE → DIRTY.
- "Strict ∅-axiom" = `#print axioms` → *"does not depend on any axioms"*
  (not even `propext` / `Quot.sound`).  Anything non-empty is
  `sorry`-equivalent for the DRLT Validation Standard.

---

## Phase 2: Cross-reference integrity (the most common rot)

Files move and rename; docstrings and specs lag.  Scan every permanent
tier for path references that no longer resolve.

```bash
# (a) Lean / docs → lean/E213/*.lean paths that don't exist
grep -rhoE "lean/E213/[A-Za-z0-9/_]+\.lean" --include='*.md' --include='*.lean' . \
  | sort -u | while read p; do [ ! -f "$p" ] && echo "STALE lean: $p"; done

# (b) docs → research-notes/*.md and theory/*.md that don't exist
grep -rhoE "research-notes/[A-Za-z0-9/_]+\.md" --include='*.md' --include='*.lean' . \
  | sort -u | while read p; do [ ! -f "$p" ] && echo "STALE rn: $p"; done
grep -rhoE "theory/[A-Za-z0-9/_]+\.md" --include='*.md' --include='*.lean' . \
  | sort -u | while read p; do [ ! -f "$p" ] && echo "STALE theory: $p"; done

# (c) seed/ spec references (CLAUDE.md, STRICT_ZERO_AXIOM.md, theory/ cite these)
grep -rhoE "seed/[A-Za-z0-9/_]+\.md" --include='*.md' --include='*.lean' . \
  | sort -u | while read p; do [ ! -f "$p" ] && echo "STALE seed: $p"; done
```

**Triage by where the reference LIVES**, not just the target:

- **Permanent tiers** (`lean/` docstrings, `theory/`, `seed/`, `catalogs/`,
  top-level `*.md`, `rust-engine/docs/`) → **fix**.  Resolve the real
  current location (`find lean -ipath '*Name*'`), then repoint.
- **Tier-1 volatile** (`research-notes/` incl. `archive/`) → frozen
  records; do **not** edit historical cross-refs (CLAUDE.md three-tier).
- **Planned-TODO / roadmap / instructional** targets (e.g. an "Action:
  add X.lean", a milestone deliverable, a create-then-delete probe file)
  → not stale; leave.

For closed topics, Lean docstrings should cite `theory/<mirror>`; only
active scratch cites bare `research-notes/G##`.  Archived notes →
`research-notes/archive/...` (fix the path, don't delete the citation).

---

## Phase 3: Three-tier discipline (CLAUDE.md "Three-tier discipline")

| Tier | Where | Lifetime |
|---|---|---|
| 1 | `research-notes/` | Volatile scratch |
| 2 | `lean/E213/` | Permanent source of truth |
| 3 | `theory/` | Permanent narrative, mirrors `lean/E213/Lib/` |

- Long-form narrative parked under `research-notes/G##_...md` for a topic
  already **closed** in Lean = tier mismatch (WARNING).  Promotion gate:
  `theory/PROMOTION_CRITERIA.md` (H1–H4 + S1–S3) → write
  `theory/<mirror>`, `git mv` source to `research-notes/archive/`.
- `theory/INDEX.md` is canonical for the narrative book.
- Closed Lean sub-trees lacking a `theory/` chapter → INFO (promotion
  candidate), don't block.

---

## Phase 4: Numerical & constant consistency

Every headline number appears in multiple permanent locations.  ALL must
agree (or be explicitly labelled observed-vs-DRLT):

```
Sources to cross-check:
  catalogs/physics-constants.md   (primary constants table)
  catalogs/math-theorems.md       (math results)
  README.md                       (key results table)
  CLAUDE.md                       (DRLT Validation Standard / boot)
  STRICT_ZERO_AXIOM.md            (per-theorem precision)
  theory/physics/...              (narrative)
```

Key values to grep and reconcile:

```
1/α_em ≈ 137.036   (DRLT 137.0359895 vs observed 137.0359991 = 0.07 ppm)
N_U   = 5²⁵ = d^(d²)   (d = 5, fractal level 2 — resolution-limit spec)
d = 5,  n_S = 3,  n_T = 2,  c = 2 = n_T
α_GUT = 6/(25π²) = 0.024317...
m_μ/m_e, m_p/m_e, η_B, Ω_Λ, Koide, Cabibbo λ = 5/22 = d/(d²−n_S)
```

For each: confirm the same value everywhere; confirm DRLT-vs-observed
columns yield the stated error/ppb; if a number differs across files,
that's an ERROR (fix to match the catalog, the primary source).  Per
CLAUDE.md: a Python/numerical-only agreement is a research note, **not**
validation — the standard is a strict ∅-axiom precision theorem or
falsifier in Lean.

---

## Phase 5: Documentation accuracy

- **`lean/E213/ARCHITECTURE.md`** — the "4 ring + Meta" spec
  (Term → Theory → Lens → Lib + Meta) and every per-directory file list /
  count matches actual `ls` (consolidated or deleted files removed; new
  files added).
- **INDEX.md per sub-tree** (≥5 files) — file tables current.
- **CLAUDE.md** — every path in boot sequence + "Entry points" + hard
  rules resolves; the hard-rules table matches the actually-wired hooks
  in `.claude/settings.json` (and `tools/FORBIDDEN.md`).
- **HANDOFF.md** — reflects the current branch / open problems (volatile;
  regenerate via the `handoff` skill if stale).
- **Author attribution** — "Mingu Jeong" only; never `Mingoo` / `Min-goo`;
  `\author{...Claude...}` forbidden in any paper artifact.
- **Repo artifacts English-only** (Lean, `.md`, commits); Korean quotes OK
  with translation.

---

## Phase 6: Fix & Report

### Fix protocol
1. Fix CRITICAL + ERROR immediately, via `Edit` (small, exact replacements).
2. Doc/docstring path fixes are comment-only → build stays clean; no
   rebuild needed.  Lean *code* edits → `lake build` + `scan_axioms`.
3. Commit each coherent batch (never amend); push to the session branch.

### Report format
```
## Consistency Audit Report
### Statistics — files scanned N · CRITICAL X (fixed) · ERROR Y (fixed) · WARNING Z · INFO I
### Fixes Applied
1. [ERROR] theory/THEORY_BOOK.md — GRA/HoTTEnrichment.lean → GRA/HoTT.lean
2. ...
### Remaining / Surfaced (needs user decision)
1. [ERROR] seed/RESOLUTION_LIMIT_SPEC.md cited by ~20 files but never committed
```

---

## Quick Mode vs Full Mode

**Quick mode** (default for "verify" / "verify" / "audit"):
- Phase 1 (build + purity spot-check) + Phase 2 (cross-ref scan) +
  Phase 4 (number reconcile).  ~5 minutes.

**Full mode** ("full verify" / "deep audit" / "전체 감사"):
- All 6 phases.  Use the `Explore` / `Agent` tool to fan-out scan large
  trees in parallel.  ~20 minutes.
