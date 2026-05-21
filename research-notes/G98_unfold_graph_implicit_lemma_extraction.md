# G98 — Unfold-graph chunk discovery: 6 chunks found, 1 implicit-lemma candidate

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Tool**: `tools/syntax_unfold_scan.py`  
**Question**: do co-occurrence patterns in `unfold` invocations
surface latent algebraic chunks whose joint computation isn't yet
named as a lemma?

---

## Method

For each tactic body, capture every `unfold name1 name2 ... [at h]`
invocation and the set of unfolded definitions per decl.  Then:

  · (B1) Per-definition frequency (most-unfolded names).
  · (B2) Co-occurrence: for each pair `(A, B)`, count decls
    unfolding both.  Jaccard = `|both| / |either|`.
  · (B3) High-Jaccard pairs become "computational chunk"
    candidates — pairs always unfolded together suggest a joint
    operational law that may or may not be lifted to a named
    lemma.

---

## Population

  · **152 decls use `unfold` at all** (4.6 % of the 3,283
    tactic-bodied decls).
  · **83 distinct definitions unfolded**, 231 total occurrences.
  · Per-decl unfold-set size: 107 decls (70 %) unfold a single
    definition; 40 (26 %) unfold two; **only 5 (3 %) unfold ≥ 3**.

The corpus is structurally **unfold-light** — most proofs delegate
operational computation to `rfl` / `decide` rather than opening
definitions explicitly.  This itself is a meta-observation:
DRLT's operational abstraction layer is mature enough that
multi-definition unfolds are rare.

---

## Top-frequency unfolded definitions (top 10)

| def | cnt | callers |
|-----|----:|--------:|
| `Raw.slash`        | 11 | 11 |
| `Tree.canonical`   | 10 |  8 |
| `slashTree`        | 10 |  7 |
| `tier`             |  9 |  7 |
| `cupList`          |  8 |  6 |
| `shiftAround`      |  8 |  1 ← outlier (single decl, manual unfold-and-rewrite 8x) |
| `canonicalBy`      |  8 |  6 |
| `and`              |  7 |  4 |
| `small`            |  7 |  6 |
| `composite`        |  6 |  5 |

`shiftAround` is a single-decl outlier — `Lib/Math/Pigeonhole.lean ::
shiftAround_inj` unfolds it 8 times in one proof.  Not a chunk; a
manual rewrite-after-unfold pattern.

---

## Six chunks discovered

### Chunk 1 — `cupList ⊕ deltaList` (J = 0.67, x4)

Decls in `Cup/LeibnizLexListLevel.lean`:

  · `list_level_leibniz_1_1`, `list_level_leibniz_2_1`,
    `list_level_leibniz_1_2`, `list_level_leibniz_2_2`

Reading: list-level Leibniz at the 4 bidegrees, all unfold cupList
+ deltaList to expose the operational structure.

**Status: already abstracted** — `list_level_leibniz_general`
(HANDOFF, parallel branch) is the unified ∀(k, l) theorem; the 4
unfold sites are the concrete bidegree instances kept as named
witnesses.

### Chunks 2a–b — `cupAW ⊕ Cochain.add / Cochain.zero` (x2 each)

  · `Bilinear.lean::cupAW_add_left`, `cupAW_add_right` —
    distributivity over Cochain.add.
  · `Zero.lean::cupAW_zero_left`, `cupAW_zero_right` —
    zero-annihilator.

**Status: already abstracted** — these ARE the named lemmas for
cup's bilinearity + zero-annihilator algebra, in their own files
(`Bilinear.lean`, `Zero.lean`).  The chunks correctly map to
existing algebraic axioms; no missing lemma.

### Chunk 3 — `lensXor ⊕ {constTrueLens, constFalseLens}` (J = 0.6, x4)

  · `OnLensImage.lean::lensXor_TT`, `lensXor_TF`, `lensXor_FT`,
    `lensXor_FF` (truth-table cases).
  · The unified theorem `boolToConstLens_xor` follows
    immediately in the same file — case-bashing on the four
    truth-table helpers.

**Status: already abstracted** — explicit-cases + 1 unified
theorem pattern.  Clean design.

### Chunk 4 — `Raw.fold ⊕ Raw.slash` (x3)

  · `Theory/Raw/Fold.lean::Raw.fold_slash` — **the canonical
    operational lemma** that defines Clause 4's behaviour.  G92
    top-2 internal hub (61 cites / 50 callers).
  · `Lens/EqPW.lean::fold_slash_eqPW` — using the operational
    definition.
  · `Lens/Lattice/IndexedJoin.lean::iProdLens_view` — same.

**Status: already abstracted** — this is the universal API
surface for the 4-clause Raw axiom.  The chunk's existence at
the unfold layer confirms the G94 §3 finding that
`Raw.fold_slash` is THE operational form of Clause 4.

### Chunk 5 — `caseElement ⊕ aPrism / bPrism` (x4)  ★ implicit-lemma candidate

  · `Prism.lean::aPrism_a`: `(caseElement Raw.a).preview Raw.a = some ()`
  · `Prism.lean::aPrism_b`: `(caseElement Raw.a).preview Raw.b = none`
  · `Prism.lean::bPrism_a`: `(caseElement Raw.b).preview Raw.a = none`
  · `Prism.lean::bPrism_b`: `(caseElement Raw.b).preview Raw.b = some ()`

**4 truth-table cases** for `caseElement`'s `preview` on Raw's
two distinguishable values.  Each proof unfolds `aPrism` /
`bPrism` (which is `caseElement Raw.{a,b}`) plus `caseElement`,
then closes via `rfl`/`if_pos`/`if_neg`.

**Status: NOT abstracted at the general level.**  The 4 specific
truth-table theorems exist; the **general** statements about
`caseElement` don't:

```lean
-- Missing general lemma 1 (positive case)
theorem caseElement_preview_self (target : Raw) :
    (caseElement target).preview target = some () := by
  show (if target = target then some () else none) = some ()
  rw [if_pos rfl]

-- Missing general lemma 2 (negative case)
theorem caseElement_preview_other (target r : Raw) (h : r ≠ target) :
    (caseElement target).preview r = none := by
  show (if r = target then some () else none) = none
  rw [if_neg h]
```

Each of the 4 existing `aPrism_a` / `aPrism_b` / `bPrism_a` /
`bPrism_b` could then be a one-line corollary:

```lean
theorem aPrism_a : aPrism.preview Raw.a = some () :=
  caseElement_preview_self Raw.a
theorem bPrism_a : bPrism.preview Raw.a = none :=
  caseElement_preview_other Raw.b Raw.a (by decide)
-- etc.
```

The cocategorical structure of `caseElement` (parametric in
`target : Raw`) makes the general form natural; the file
`Prism.lean` has `caseElement_disjoint` (a 2-target structural
property) but **not** the per-target preview characterisation.
This is the gap.

**Net effort to close**: 2 new general lemmas + 4 one-line
rewrites.  Mass change roughly neutral but **explanatory
content increases** — the truth-table becomes a corollary of
the categorical structure rather than 4 hand-instantiated rfl
chains.

### Chunk 6 — `Survives ⊕ residue` (J = 1.0, x2)

  · `Theory/Atomicity/Alive.lean::survives_iff_odd`
  · `Theory/Atomicity/Alive.lean::alive_iff_odd_pair`

**Status: already abstracted** in the parallel branch's
`AliveDerivation.alive_iff_clause4_alive` (G87 §11).  The
`Survives + residue` chunk operationally embodies the alive
predicate; its abstraction now lives as the recursive Clause-4
derivation.

---

## Summary table

| Chunk | Pair | Decls | Status |
|-------|------|------:|--------|
| 1 | `cupList ⊕ deltaList`           | 4 | ✅ → `list_level_leibniz_general` |
| 2a | `cupAW ⊕ Cochain.add`           | 2 | ✅ → `cupAW_add_left/right` |
| 2b | `cupAW ⊕ Cochain.zero`          | 2 | ✅ → `cupAW_zero_left/right` |
| 3 | `lensXor ⊕ constLens`            | 4 | ✅ → `boolToConstLens_xor` |
| 4 | `Raw.fold ⊕ Raw.slash`           | 3 | ✅ → `Raw.fold_slash` (G92 hub) |
| **5** | **`caseElement ⊕ aPrism/bPrism`** | **4** | **⚪ implicit-lemma candidate** |
| 6 | `Survives ⊕ residue`             | 2 | ✅ → `alive_iff_clause4_alive` |

**Hit rate**: 1 / 6 = 17 % new implicit-lemma surface.  Five of
six chunks were already correctly abstracted; one (Chunk 5,
Prism truth-table) has a clear gap.

---

## Meta-observations about the unfold-graph method

### What worked

  · **Confirmation method** — successfully recovered 5 known
    abstractions (cup bilinearity, zero, list-level Leibniz,
    Raw.fold_slash, alive bridge).  The method correctly
    identifies operational chunks; when DRLT has already
    abstracted them, the chunks pass through cleanly.
  · **Negative validation** — the absence of unexpected
    high-Jaccard pairs is itself a structural claim about DRLT:
    operational abstractions are mature.
  · **Hit on Chunk 5** — surfaced one genuinely-missing
    abstraction (`caseElement_preview_self/other`) by the
    Prism-truth-table parallel to the lensXor-truth-table.

### What didn't work

  · **Single-def unfolds dominate** (70 % of unfolders).  No
    co-occurrence signal at all.  Most `unfold`s are surgical
    one-shots, not multi-def operational opens.
  · **Triple co-occurrence is virtually zero** — no triple was
    co-unfolded in ≥ 3 decls.  The operational chunks bottom
    out at pairs.
  · **`unfold` is rare** (4.6 % of decls).  The bulk of DRLT
    proofs use `decide`/`rfl`/`rw` and never open definitions.
    Implicit-lemma candidates hiding in non-unfold proofs are
    inaccessible to this method.

### Implication for the "implicit lemma extraction" goal

The unfold-graph method has a **17 % hit rate** for new
implicit-lemma candidates and a **83 % confirmation rate** for
existing ones.  It is therefore primarily a **validation tool**
for the existing abstraction layer, with occasional new
surfacing.  Not a primary engine for math-law discovery in this
corpus.

The deeper goal (motif → automatic implicit-lemma extraction)
requires either:

  1. **`rw`-cascade analysis** — the 800+ `rw → rw` bigrams from
    G91 might encode implicit composite-rewrite lemmas at the
    citation-graph layer.  Higher density than `unfold` chains
    (since `rw` is the dominant tactic at 17 % of tokens).
  2. **Cross-corpus motif transfer** — comparing DRLT chunks
    against Mathlib or other Lean repos for universal patterns
    that DRLT specialises.
  3. **Decide-failure mining** — extracting cases where
    `decide` outputs false, treating these as automatically-
    discovered counterexamples / falsifiers.

(1) is the natural next step on this branch.

---

## Concrete next action (small)

**N7** — promote `caseElement_preview_self` + `caseElement_preview_other`
into `Lens/Instances/Prism.lean`, rewrite the 4 truth-table
theorems as one-line corollaries.  ~30 LOC change, zero blast
radius (the 4 named theorems' API is preserved).

Surfaces directly from the meta-scan as an immediately
actionable implicit-lemma extraction.  Small enough to be done
on this branch without conflict, but consistent with the
process model: surfaced here, executable wherever convenient.

---

## Artifacts

  · `tools/syntax_unfold_scan.py` — scanner
  · `tools/_syntax_unfold_rows.tsv` — extracted rows (gitignored)
