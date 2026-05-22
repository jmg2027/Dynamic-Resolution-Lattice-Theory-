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
| L1 | LeibnizAlgLift 4-sibling | **DONE (full)** | β-side: `LeibnizAlgLiftBeta.leibniz_via_β_decomp_general` (commit 0fabff84).  α-side: `LeibnizAlgLiftAlpha.leibniz_via_α_decomp_general` with `castA/castB` `Fin.cast` plumbing for the Nat.add asymmetry (commit a119b077).  All 4 siblings 1-line corollaries.  Methodology: `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-4. |
| C  | CutSumOne 8-sibling 3-component template | **DONE** | `cutSum_constCut_at (a₁ b₁ a₂ b₂ X Y m k) (forward) (backward)` extracts the bidirectional iff opener + `decide_eq_true` closer.  All 8 substantive `cutSum_*` refactored; 478→337 lines (commit 4984c9ad). |

## §4 — Smaller consolidations

| ID | Title | Status | Notes |
|----|-------|:------:|-------|
| L3 | Pisano Predictor extension steps | **DONE** | `pisano_period_lift {p pf N f}` PURE template absorbs per-prime `intro k; rw [h_p]; exact period_n k` boilerplate; 10 sites refactored across Predictor8/11/14/17 (commit fc105cd6). |
| L4 | `addLDD` / `mulLDD` (Smooth.lean) | **DONE** | `ldd_branch_via_maxRange (sf cx cy M hagree S R side_chain m' hm')` PURE template (in `Real213/Core/CutFnData.lean`) absorbs the inner `apply sf.prop; intro m'' k'' hm'' hk''; apply hagree; <chain>` block; 4 branches refactored across addLDD + mulLDD (commit 7c887e23).  Parameterized helper instead of typeclass. |
| L5 | `CDDouble.I_mul_J` / `J_mul_I` | **REMOVED** (no yield) | Per-instance numeric witnesses differ; `decide` ineffective.  Investigated in G118; not an abstraction candidate. |
| M  | `Raw.recAux` / `RawBy.recAux` pair | **DONE** | `claude/handoff-part-3-marathon-0XWmn` — refactored to use Sub-2 helpers (Tree.canonical_slash_decompose / canonicalBy_slash_decompose). |
| E  | `sqrt{2,3,5}_no_rational_aux` ×4 | OPEN | 4 byte-identical except for the prime / perfect-square predicate.  Needs `IsPerfectSquare N` infrastructure as a prereq.  Substantial design. |
| F  | Σ-fold cross-domain | OPEN | 5 fold + HAdd skeletons across math + physics.  Candidate `sigmaList` infrastructure. |
| Pell-FSM | `*FSMmod*_{run,bits}_period_T` 93 sites | **DONE (full sweep)** | Same branch — 7 generic helpers (`ArithFSM2/3.run_period_of_base`, `ArithFSM2/3.bits_period_of_run_period`, `bits_period_mul_of_period`, `toBitFSM_bits_period_lift`, `toBitFSM3_bits_period_lift`).  93 sites refactored across Pell + Lucas + Fib + Trib + CrossClass + LensPairs.  Run-period + bits-period + doubled/tripled + BitFSM lifts all covered. |
| ModArith | `mod3` / `mod5` per-residue | **DONE** | Same branch — `mod5_five_mul_add` hoisted (already existed); `mod3_three_mul_add` added; 6 per-residue corollaries collapsed to 1-line term applications. |

---

## Done summary (this branch, post Part 5 marathon)

  · **§2 fully closed** — L2, N7, N8, N9, Sub-2 (5/5 items).
  · **§3 fully closed** — L1 (β + α, 4/4 siblings, Part 5 commits
    0fabff84 + a119b077), C (CutSumOne 8/8, Part 5 commit 4984c9ad).
  · **§4** — M, Pell-FSM (93 sites), ModArith, L3 (Part 5 commit
    fc105cd6, 10 sites in Predictor8/11/14/17), **L4 DONE** (commit
    7c887e23 — ldd_branch_via_maxRange template); L5 deferred
    (no consolidation possible — see G118); E/F still open.
  · **Cross-tier (Part 5)** — G110 FLUX-1 (34 sites via
    CutMulOuterReduce + UnitBracketReduce/×2 + UnitBracketReduceSum),
    G111 COH-1+2+3 (Pattern10 + InvolutionTemplate +
    LeibnizUniversalLift), **REAL-1+REAL-2 DONE** (commit f7f00a98 —
    BoolOrLadder.bool_or_ladder_iff template, 3 theorems refactored,
    ~140K Expr nodes retired), TH-1/TH-4/G117 spec docs.

Net Lean deliverables this branch:
  · 20 new PURE helpers across 7 new modules / additions
    (LeibnizDecomp, LeibnizAlgLiftBeta, Prism N7, Tree decompose,
    canonicalBy decompose, ArithFSM2/3 run_period_of_base +
    bits_period helpers + BitFSM lift helpers + period multiplication,
    mod3 absorption).
  · ~730+ net lines removed.
  · ~200 tactic tokens retired in mechanical adoptions.
  · 130 sites absorbed via 20 PURE helpers.

Doc deliverables (G107 §10):
  · `LESSONS_LEARNED.md` Patterns #10, #11, #12, #13 added.
  · `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-2 — α/β/γ readings.
  · `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-3 — falsifier surface (quantitative §8.2).
  · `catalogs/recursor-inventory.md` — CAT-3.
  · `catalogs/internal-hubs.md` — CAT-4.
  · `catalogs/falsifier-roster.md` — CAT-1.
  · `catalogs/abstraction-candidates.md` (this file) — CAT-2.
  · `README.md` NAV-2 pointer + `seed/INDEX.md` NAV-1 entries.
  · `STRICT_ZERO_AXIOM.md` NAV-4 Lean-core PURE-bounded fact.
  · `lean/E213/ARCHITECTURE.md` NAV-3 empirical-verification note.

Still open from §2: none.
Still open from §3: none.
Still open from §4: E (sqrtN; needs IsPerfectSquare prereq), F
(Σ-fold; additive).  L4 **DONE** (commit 7c887e23).  L5 removed
(no yield — see G118).

Part 5 closures (cross-tier): G110 FLUX-1 (34 sites),
G111 COH-1+2+3, REAL-1+REAL-2 (commit f7f00a98),
FSM-1 (1) generic pellFSMmod, TH-1/TH-4/G117 spec docs.

Items removed from registry (no abstraction yield, see G118):
CD-1+2+3 (CayleyDickson), HC-1 (Hodge capstones),
PHYS-1 (FractalLevelZeta), PHYS-2 (bracket-containment), L5 (CDDouble).

One research direction remains (not a marathon item):
FSM-1 (2) Pisano period theorem for Pell-5 (5-10 sessions, number theory).

**See `research-notes/G118_marathon_deferred_items.md`** for the
final closure status.
Still open from §10: TH-1 (proof-shape fingerprint, key data already
in CAT-3 + ARCHITECTURE.md note), TH-4 (L1 methodology, partial via
LeibnizAlgLiftBeta).  Neither blocks; redundancy with already-shipped
content.  CL-1/CL-2 promoted to Patterns #12/#13 instead.

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
