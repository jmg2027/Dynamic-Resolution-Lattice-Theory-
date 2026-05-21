# Abstraction Candidates — executor status

CAT-2 per `research-notes/G107_action_items_registry.md` §10.2.
Tracks per-item status of every abstraction candidate surfaced by
the G90-G106 meta scans.  Update when an item closes.

Source registry: `research-notes/G107_action_items_registry.md`
sections §2 (mechanical), §3 (mid-size), §4 (smaller).

Status keys:
  · **DONE** — abstraction committed, all sites refactored, PURE.
  · **PARTIAL** — abstraction committed, not all sites refactored.
  · **OPEN** — no work yet.
  · **DEFERRED** — see notes (usually awaiting infrastructure or
    deeper insight).

---

## §2 — Mechanical / immediate (low effort)

| ID | Title | Status | Branch/Notes |
|----|-------|:------:|--------------|
| L2 | `h_components_{α,β}` 4-sibling | **DONE** | `claude/handoff-part-3-marathon-0XWmn` — `LeibnizDecomp.lean` (8 PURE helpers); 4 sites collapsed. -147 lines net. |
| N7 | `caseElement` Prism truth-table generalisation | **DONE** | Same branch — `caseElement_preview_{self,other}` (2 PURE); 4 truth-table theorems as one-line corollaries. |
| N8 | `NatHelper.mul_left_comm` adoption | **DONE** | Same branch — 19 sites across 3 files (CutSumOne ×16, CutMidSelf ×2, Euler ×3). |
| N9 | `Nat.add_right_comm` adoption | **DONE** | Same branch — 6 sites across 7 files; helper was Lean-core PURE on its own. |
| Sub-2 | Tree slash-arm prologue tactic macro | OPEN | 5 Tree-induction siblings sharing 10-token prefix. |

## §3 — Mid-size consolidations

| ID | Title | Status | Notes |
|----|-------|:------:|-------|
| L1 | LeibnizAlgLift 4-sibling | OPEN | **Biggest single target** (G106): 6-layer byte-identical, ~6.6 M chars retired (50 % L1 mass).  Parametric form sketched in G106 §3.  Medium marathon. |
| C  | CutSumOne 8-sibling 3-component template | OPEN | 8 `cutSum_*` decls share 9-token opener.  G94 §7 has the template proposal.  Medium marathon. |

## §4 — Smaller consolidations

| ID | Title | Status | Notes |
|----|-------|:------:|-------|
| L3 | Pisano Predictor 14/17 | OPEN | 2 sibling 20-tactic ladders.  Predictor structure is incremental (P7→P11→P14→P17); abstracting may obscure the "+3 primes per step" story.  Low priority. |
| L4 | `addLDD` / `mulLDD` (Smooth.lean) | OPEN | 2 byte-identical 16-tactic ladders.  Parameterise over (aux, aux_congr, locality-bound) — non-trivial. |
| L5 | `CDDouble.I_mul_J` / `J_mul_I` | OPEN | 2 byte-identical 16-tactic ladders.  Cayley-Dickson basis non-commutativity witness pair. |
| M  | `Raw.recAux` / `RawBy.recAux` pair | OPEN | 2 siblings sharing 10-token prefix.  Recursor pair — deep infrastructure. |
| E  | `sqrt{2,3,5}_no_rational_aux` ×4 | OPEN | 4 byte-identical except for the perfect-square predicate. Needs `IsPerfectSquare N` infrastructure. |
| F  | Σ-fold cross-domain | OPEN | 5 fold + HAdd skeletons across math + physics.  Candidate `sigmaList` infrastructure. |
| Pell-FSM | `pellProperModN_period_*` 8+ | OPEN | Pattern #2 recursor skeleton × 8 moduli (11, 13, 17, 19, 23, 29, 31, 37). |
| ModArith | `mod3` / `mod5` family | OPEN | 9 decls sharing recursor skeleton modulo modulus. |

---

## Done summary (this branch)

  · **L2 + N7 + N8 + N9** — 4 of 5 mechanical-immediate items closed.
  · ~165 net lines removed from corpus; ~75 tactic tokens retired
    in the mechanical adoptions; one new module (8 PURE helpers).
  · Pattern #10 (adoption-gap detection) + Pattern #11 (Cup-Leibniz
    dichotomy collapse) added to `LESSONS_LEARNED.md`.

Still open from §2: **Sub-2** (Tree-induction tactic macro).

---

## Recommended next-marathon order

Following G107 §7 (mass × confidence / effort):

  1. **Sub-2** — finish §2 mechanical sweep.
  2. **L1** (G106) — biggest single mass-reduction; 6-layer evidence.
  3. **C** (G94 §7) — broadest by sibling count (8); medium marathon.
  4. **L4** / **L5** — small consolidations, low risk.
  5. **L3** — only if Pisano-step narrative reframing has been done.
  6. **E** — needs `IsPerfectSquare` predicate first.
  7. Pell-FSM + ModArith — medium-effort batches.

---

## Companion scanners

| Tool | Purpose | Re-run with |
|------|---------|-------------|
| `tools/syntax_tactic_scan.py` | tactic-token motifs (G91) | `python3 tools/syntax_tactic_scan.py` |
| `tools/ast_callgraph_scan.py` | Expr-level call graph (G102) | `python3 tools/ast_callgraph_scan.py` |
| `tools/ast_shape_scan.py` | shape density + L1 (G103) | `python3 tools/ast_shape_scan.py` |
| `tools/syntax_rw_cascade_scan.py` | adoption-gap k-grams (G99) | `python3 tools/syntax_rw_cascade_scan.py` |
| `tools/falsifier_mining_scan.py` | negation theorems (G100) | `python3 tools/falsifier_mining_scan.py` |

All TSVs gitignored; scanner code committed.  Rerun before any
new abstraction marathon to refresh candidate rankings.
