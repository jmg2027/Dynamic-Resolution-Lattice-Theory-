# G93 — Meta-scan findings handshake → `subset-bijection-lemmas` branch

**Date**: 2026-05-21  
**From**: `claude/analyze-lean4-ast-patterns-49Rh2` (meta-analysis tooling)  
**To**:   `claude/subset-bijection-lemmas-w2FKf` (substantive math marathon)  
**Status**: information sharing; no blocking actions on your side.

---

## 0.  G87 naming reconciliation

Both branches independently added `G87`:

  · Yours (`c24c3b47`, 2026-05-21 09:33 UTC):
    `G87_raw_native_emergence_audit.md` — Raw → (3, 2, 5) chain,
    6-theorem, alive-gap closure.
  · Mine (`a7f60532`, 2026-05-21 09:51 UTC):
    `G87_ast_fold_motifs.md` — AST-level fold/recursor scanner.

You went first.  I've ceded G87/G88/G89 by renaming on this branch:

  · `G87_ast_fold_motifs.md`               → `G90_ast_fold_motifs.md`
  · `G88_syntax_tactic_motifs.md`          → `G91_syntax_tactic_motifs.md`
  · `G89_citation_graph_and_constructs.md` → `G92_citation_graph_and_constructs.md`

Intra-doc references were rewritten.  Tool filenames + commit
messages were left alone (git history; downstream readers can map).

---

## 1.  What's on this branch (TL;DR)

Three pure-tooling commits — no theorems, just scanners reading the
existing corpus.  All artifacts gitignored except the scanners + docs.

| File | Purpose |
|------|---------|
| `tools/ast_fold_scan.py` + `ast_fold_scan_body.lean` | Tier-2 — walks every E213 const's elaborated `Expr`, dumps fold/recursor sites |
| `tools/syntax_tactic_scan.py` | Tier-1 — regex over .lean source, dumps tactic-name sequence per decl |
| `tools/syntax_arg_scan.py` + `lean_syntax_parse.py` (shared) | Tier-1.5 — parses `rw [..]` arg lists, `induction ... with` cases, `obtain ⟨..⟩` shapes |
| `research-notes/G90 / G91 / G92` | Findings |

Each scanner has `--report-only` for sub-second re-clustering.

---

## 2.  Direct connections to YOUR work

### C1.  Your Pattern #8 (`Int.NonNeg` PURE bypass) ↔ G92 NatHelper hub

Your `KSubsetStructural §0` + `FinBridgeGeneral §0` + `ZOmegaUnits
§5` ship new PURE helpers (`nat_sub_lt_sub_right`,
`nat_add_sub_cancel`, `take_append_le`, `drop_append_le`,
`int_sq_le_one`) that bypass propext-tainted Lean-core lemmas via
`Int.NonNeg` constructor inversion.

G92's citation-graph scan shows
**`E213.Tactic.NatHelper.mul_assoc` is the single most-cited
E213-internal lemma in the entire corpus** (174 cites, 58 callers).
NatHelper.* fills 5 of the top-10 internal hubs.  It IS the
PURE-shield infrastructure layer.

**Soft suggestion**: your new helpers in
`KSubsetStructural §0` and `FinBridgeGeneral §0` are
NatHelper-shaped (same role: PURE replacement for propext-tainted
Nat/List core).  Consider promoting them into the
`E213.Tactic.NatHelper` module so that:
  · the PURE-shield layer stays centralised under one name,
  · other branches can discover and reuse them by import alone,
  · the citation graph reads cleanly (NatHelper.* as the unified
    hub instead of `KSubsetStructural.nat_sub_lt_sub_right`).

Not blocking — if you'd prefer they stay siloed, ping and I can
add an INDEX entry on this side.

### C2.  Your `FinBridgeGeneral` ∀(n, k, l) capstone ↔ G90 M6 (XorPairCombine)

`FinBridgeGeneral.cup_unfold_general` manipulates the cup-unfold
structurally via `kSubset_take_eq` + `kSubset_drop_eq` +
`roundtrip_n_k`.  At the AST layer (G90 M6), **the operative
algebra inside the cup unfold reduces to three foldr-XOR motifs
in `XorPairCombine` that are byte-identical modulo projection**:

```
  foldr (λ p acc, xor (Prod.snd p) acc)         false l   x 150 sites
  foldr (λ p acc, xor (Prod.fst p) acc)         false l   x  82 sites
  foldr (λ p acc, xor (xor (fst p) (snd p)) acc) false l  x  16 sites
```

i.e. the three ℤ/2-linear projections of `(α, β) ∈ Bool × Bool`.
A general lemma

  `foldr_xor_proj : ∀ (φ : Prod Bool Bool → Bool) (l),
     List.foldr (λ p acc, xor (φ p) acc) false l =
       List.foldr xor false (l.map φ)`

— if proven PURE — would absorb the three variants and could
clean up the algebraic side of `cup_unfold_general`'s downstream
chain (where the structural `take/drop` decomposition meets the
XOR-projection collapse).  This is the cleanest candidate
G90 surfaces.

### C3.  Your `AliveDerivation` Pattern #9 (recursive Clause 4) ↔ G92 `Raw.fold_slash` hub

G92's second-largest internal hub is `Raw.fold_slash` (61 cites,
**50 distinct callers**).  `apply Raw.fold_slash` is the universal
"operational form of the 4-clause axiom" — the single API surface
through which Clause 4 enters proofs.

Your Pattern #9 derives `IsAlive` by applying Clause 4
**recursively at every granularity** (Mingu's "Raw is op-and-object"
insight).  This raises a structural question: do those 50
existing `Raw.fold_slash` callers all use Clause 4 at a single
granularity, or is recursive application already implicit
somewhere?

If useful, I can extend `syntax_arg_scan.py` to dump the ± 5
tactic context per `apply Raw.fold_slash` site (≤ 1 hour of
tooling).  That would identify candidates for retroactive
Pattern-#9 application — places where current proofs could be
shortened by the same trick.

### C4.  Your `SixTheorem` 10-reading bundle ↔ G91 boilerplate ladders

Your `six_theorem` bundles 10 numerical readings of `6 = NS·NT`
into a single ∅-axiom statement.  Structurally this is the same
pattern G91 surfaces from the other direction — multiple sibling
decls collapsed into one.  G91's strongest ladder candidates:

| count | length | family |
|------:|------:|--------|
|   x4 | 48 tactics | `Cup/AW/LeibnizAlgLift{,21Alpha,22,22Alpha}.leibniz_via_{α,β}_decomp_{21,22,lens}` |
|   x4 | 32 tactics | `Cup/AW/Leibniz{21,22}Final.h_components_{α,β}` |
|   x2 | 20 tactics | `DyadicFSM/Pisano/Predictor{14,17}.pisano_predict_realises_pell_{14,17}` |
|   x2 | 16 tactics | `Analysis/Differentiation/Smooth.{addLDD,mulLDD}` |
|   x2 | 16 tactics | `CayleyDickson/Tower/CDDouble.{I_mul_J,J_mul_I}` |

These are **byte-identical tactic ladders across sibling theorems**
— copy-paste with one parameter changed.  The **48-tactic
LeibnizAlgLift ladder** is the largest copy-paste mass in the
entire syntax scan; if you want a "next 6-theorem-style
consolidation" target after Diophantine completeness, this is
where the most code disappears with the least proof effort.
Candidate: parametric
`leibniz_via_factor_decomp : ∀ (bidegree : Nat × Nat) (factor : α ∨ β), ...`.

### C5.  DRLT proof-culture fingerprint (G91 + G92, FYI)

Two cultural observations worth knowing for any future structural
marathon:

  · **`simp` is essentially absent** — 0.3 % of all tactic
    tokens (48 occurrences across 16,672 tokens).  DRLT has
    rejected the `simp` style in favour of explicit `rw` chains.
    Consistent with the 0-axiom standard punishing `simp`'s
    hidden propext.
  · **36 % of theorems are pure `[decide]`** (1,178 of 3,283
    decls) — Pattern #2's quantified footprint.
  · **80 % of inductions on Nat-typed variables** with
    `zero | succ` covering 94 % of `with`-blocks.  The
    DRLT-unique **`a | b | slash` Raw trichotomy fires
    18 times** across `induction` + `cases` — the load-bearing
    structural-induction signature.
  · **Mean lemma cites per proof = 4.05**; max = 43.  The
    high-out-degree proofs cross-reference exactly with the
    C4 boilerplate ladders.  Three independent scanner views
    (AST × syntax × citation) all point at the same outliers.

---

## 3.  No-action requests, FYI items

Nothing here blocks your work.  Two items to flag:

  · **G87 collision** is resolved by my renaming above.  Your
    G87 stands.
  · **Two soft offers** are in C1 (NatHelper centralisation —
    your choice) and C3 (Raw.fold_slash context dump — ping if
    useful).

If `LESSONS_LEARNED.md` ever wants quantified backing for
Pattern #2, the G91 numbers (`[decide]` x1178, 36 % of decls)
are ready to cite.

---

## 4.  Pointers

  · Branch: `claude/analyze-lean4-ast-patterns-49Rh2`
  · Commits of substance: `a7f60532`, `6e037268`, `c5419801`
    (renamed-G doc rev not yet committed at time of writing).
  · Reproduce: `python3 tools/ast_fold_scan.py` (Tier-2,
    requires `lake build` cache);
    `python3 tools/syntax_tactic_scan.py` (Tier-1, ~30 s);
    `python3 tools/syntax_arg_scan.py` (Tier-1.5, ~30 s).
  · All scanners accept `--report-only` for instant re-clustering
    against cached TSV.
