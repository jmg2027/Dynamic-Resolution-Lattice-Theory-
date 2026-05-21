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
| Sub-2 | Tree slash-arm prologue helper | **DONE** | Same branch — `Tree.canonical_slash_decompose` + `canonicalBy_slash_decompose`; 5 sites refactored (term-level, not macro). |

## §3 — Mid-size consolidations

| ID | Title | Status | Notes |
|----|-------|:------:|-------|
| L1 | LeibnizAlgLift 4-sibling | DEFERRED | **Blocked by Fin-index defeq** (same blocker as L2): `(a+1)+b-1 ≢ a+b` for abstract args.  G106 sketch assumes elaboration-level abstraction, but source-level requires casts.  Pursue via `Fin.cast` plumbing or via specific-degree helpers (4-helper approach, no count reduction). |
| C  | CutSumOne 8-sibling 3-component template | OPEN | 8 `cutSum_*` decls share 9-token opener.  G94 §7 has the template proposal.  Medium marathon. |

## §4 — Smaller consolidations

| ID | Title | Status | Notes |
|----|-------|:------:|-------|
| L3 | Pisano Predictor 14/17 | DEFERRED | Proofs aren't byte-identical at content level (different projection chains).  Incremental structure (P7→P11→P14→P17) would obscure on abstract. |
| L4 | `addLDD` / `mulLDD` (Smooth.lean) | DEFERRED | Substantial differences in concrete aux + locality bound; clean abstraction requires `BinaryOpLDD` typeclass — substantial design task. |
| L5 | `CDDouble.I_mul_J` / `J_mul_I` | DEFERRED | Not byte-identical at content level — compute different numeric witnesses for different `(α, β, γ, δ)` tuples. |
| M  | `Raw.recAux` / `RawBy.recAux` pair | **DONE** | `claude/handoff-part-3-marathon-0XWmn` — refactored to use Sub-2 helpers (Tree.canonical_slash_decompose / canonicalBy_slash_decompose). |
| E  | `sqrt{2,3,5}_no_rational_aux` ×4 | OPEN | 4 byte-identical except for the prime / perfect-square predicate.  Needs `IsPerfectSquare N` infrastructure as a prereq.  Substantial design. |
| F  | Σ-fold cross-domain | OPEN | 5 fold + HAdd skeletons across math + physics.  Candidate `sigmaList` infrastructure. |
| Pell-FSM | `pellModN_bits_period` 32+ | **DONE (partial)** | Same branch — `ArithFSM2.bits_period_of_run_period` helper (PURE); 27 sites refactored across ArithFSM.lean + ArithFSM/Mod{Small,Medium,Large}.lean + Pell/ProperMod.lean.  Doubled-period (`_2T`) variants kept; LensPairs BitFSM variants pending. |
| ModArith | `mod3` / `mod5` per-residue | **DONE** | Same branch — `mod5_five_mul_add` hoisted (already existed); `mod3_three_mul_add` added; 6 per-residue corollaries collapsed to 1-line term applications. |

---

## Done summary (this branch)

  · **§2 fully closed** — L2, N7, N8, N9, Sub-2 (5/5 items).
  · **§3** — C still open; L1 deferred (defeq blocker).
  · **§4** — M, Pell-FSM (partial), ModArith (3/8 items); L3/L4/L5
    deferred; E/F still open.

Net deliverables this branch:
  · 12 new PURE helpers across 5 new modules / additions.
  · ~250 net lines removed.
  · ~150 tactic tokens retired in mechanical adoptions.
  · Pattern #10 (adoption-gap) + #11 (Cup-Leibniz dichotomy) added.

Still open from §2: none.
Still open from §3: C (CutSumOne 8-sibling).
Still open from §4: E, F.
Doubled-period (`_2T`) variants of Pell-FSM intentionally kept.

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
