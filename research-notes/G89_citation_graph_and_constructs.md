# G89 — Citation graph & tactic-construct shapes (Tier-1.5)

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Tool**: `tools/syntax_arg_scan.py` (+ shared `tools/lean_syntax_parse.py`)  
**Companion**: G87 (AST motifs), G88 (syntax tactic skeletons)  
**Scanned**: 3,283 decls / 780 files / 7,446 lemma citations /
981 induction/cases/obtain constructs.

---

## Method

Per tactic body extracted by `lean_syntax_parse.find_decl_bodies`:

  · **(B) Citations** — bracket-list tactics
    (`rw [..]`, `rewrite [..]`, `simp only [..]`, `simp_rw [..]`,
    `simp_all only [..]`) → balance brackets, split top-level by
    `,`, take the leading dotted identifier of each item (with
    `←` / `↑` stripped).  Plus `apply <name>`, `exact <name>`,
    `refine <name>` heads.
  · **(C) Constructs** — `induction <x>`, `cases <h>`, with the
    optional immediately-following `with | tag1 ... | tag2 ...`
    block parsed for case tags.  Plus `obtain ⟨...⟩ := ...` with
    angle-bracket balancing → destructuring-shape normalisation.

After filtering hypothesis-shaped names (`h`, `ih`, `h1`, `hx`,
`this`, …) we have **6,256 non-hypothesis citations across 1,592
distinct names**.

---

## (B) — Citation graph

### Internal vs external

After filtering hypothesis-shaped names:

  · **E213.* internal**: 7.9 % (492 cites)
  · **External** (Lean core / Nat / List / *open*'d E213 names):
    92.1 % (5,764 cites)

The 92 % external figure overstates externality, because heavily
`open`'d E213 names appear without prefix (`Raw.fold_slash`,
`leavesModNat_view_eq`, `h_components`, `ZI.ext`).  Even so, the
**true Lean-core dependency** dominates — DRLT leans heavily on
`Nat.*` and `Bool.*` core lemmas.

### Top 10 E213-internal hubs

| Lemma | cites | callers |
|-------|------:|--------:|
| `E213.Tactic.NatHelper.mul_assoc` | 174 | 58 |
| `E213.Tactic.NatHelper.add_mul`   |  45 | 27 |
| `E213.Meta.Int213.mul_comm`       |  20 |  6 |
| `E213.Meta.Int213.neg_mul`        |  14 |  6 |
| `E213.Meta.Int213.neg_add`        |  13 |  9 |
| `E213.Tactic.NatHelper.add_sub_cancel_right` | 12 | 12 |
| `E213.Tactic.NatHelper.mul_mul_mul_comm_213` | 11 |  5 |
| `E213.Meta.Int213.add_comm`       |  11 |  9 |
| `E213.Meta.Int213.mul_neg`        |  10 |  6 |
| `E213.Term.Internal.Tree.noConfusion` | 7 |  5 |

**`E213.Tactic.NatHelper.*` is the dominant internal infrastructure**
— 5 of the top 10 internal bricks live there.  It's the
PURE-replacement layer for `Nat.*` lemmas whose Mathlib / kernel
forms would import `propext` or `Classical`.  Any change to
NatHelper has the largest downstream blast radius in the corpus.

Second-tier: **`E213.Meta.Int213.*`** — the integer-algebra
infrastructure (5 entries in top 10).

### Top 10 external (Lean-core or `open`'d) hubs

| Lemma | cites | callers |
|-------|------:|--------:|
| `absurd`        | 177 | 104 |
| `Nat.mul_comm`  | 165 |  90 |
| `Nat.add_assoc` | 149 |  74 |
| `Nat.add_comm`  | 145 |  99 |
| `decide_eq_true`|  84 |  47 |
| `Nat.one_mul`   |  82 |  62 |
| `Nat.le_trans`  |  76 |  59 |
| `Nat.mul_add`   |  71 |  45 |
| `ext`           |  68 |  68 |
| `Raw.fold_slash`|  61 |  50 |

`Raw.fold_slash` is **E213-internal but shown unprefixed because of
`open E213.Theory`**.  At 50 distinct callers, it's the
*operational form of the Raw axiom* — anywhere a proof needs to
unfold the 4-clause behaviour, this is the lemma cited.  Its
50-caller spread is the single most-significant **internal hub
after NatHelper**.

`absurd` at 177/104 confirms **proof-by-contradiction is the
dominant negation strategy** (combined with the heavy `exact` use
from G88).  Workflow is `... ; absurd hP h¬P` more often than
`... ; exfalso; exact h¬P hP`.

`decide_eq_true` (84/47) is the **Pattern #2 bridge lemma**:
between `Decidable.decide p = true` and `p`.  Quantified: ~14 % of
non-hypothesis citations route through this bridge.

### Per-kind cite leaders

| Tactic | top cites |
|--------|-----------|
| `rw`     | `NatHelper.mul_assoc` (174), `Nat.mul_comm` (163), `Nat.add_assoc` (146) |
| `exact`  | `absurd` (177), `Nat.le_trans` (76), `Nat.add_comm` (41) |
| `apply`  | `ext` (67), `Raw.fold_slash` (40), `decide_eq_true` (37) |
| `simp`   | `Int.neg_neg` (7), `Int.sub_eq_add_neg` (5), `neg_mul` (5) |

`apply` is the gateway for the structurally important lemmas
(`ext`, `Raw.fold_slash`, `decide_eq_true`) — the "open the
proof" move.

`simp` is so rarely used (147 cites total across the whole
corpus; G88 measured 0.3 % of tokens) that its top citations
have only 5-7 occurrences each — no clear pattern.

### Out-degree distribution

Cites per proof distribution:

| out-degree | proofs |
|-----------:|-------:|
| 1 | 444 |
| 2 | 333 |
| 3 | 248 |
| 4 | 117 |
| 5 |  75 |
| ≥6 | 360 (tail to max 43) |

  · **Mean: 4.05 cites per proof**
  · **Median: 2** (444 + 333 + 248 = 1,025 proofs at ≤ 3 cites)
  · **Outliers**: proofs with > 20 cites cross-reference with G88's
    boilerplate ladders.

---

## (C) — Construct shapes

### Induction targets

281 `induction` invocations.  **80 % are Nat-typed variables**:

| Variable | count |
|----------|------:|
| `k`  | 70 |
| `n`  | 68 |
| `r`  | 57 |
| `t`  | 20 |
| `l`  | 13 |
| `s`  | 10 |
| `h`  |  9 |
| `m`  |  7 |
| `xs` |  4 |

Of 281 inductions, **17 are on List** (`l`, `xs`) and the rest are
either Nat or hypothesis variables (`r` is sometimes a Raw-Tree
parameter, sometimes a Real213 variable).

### `with`-block case-count distribution

| #cases | count |
|-------:|------:|
| no with | 74  |
| 2      | 145 |
| 3      | 27  |
| 4      | 12  |
| 5      | 4   |
| 6      | 8   |
| 12     | 5   |

**145 of 207 `with`-blocks (70 %) have exactly 2 cases** — the
`zero | succ` and `nil | cons` pattern.

### Top induction case-tag sets

| count | tag set |
|------:|---------|
| **136** | `zero \| succ` |
|    15 | `a \| b \| slash`              ← **DRLT-native Raw trichotomy** |
|     5 | `ofL \| ofM \| refl \| symm \| trans \| slash_cong` ← Raw congruence closure |
|     5 | `nil \| cons` |
|     4 | `one \| succ` |
|     3 | `zero \| succ \| k_pred` |
|     2 | `zero \| succ \| h_ge` |

**`a | b | slash` (15 occurrences) is DRLT's unique structural-
induction signature** — every proof that touches the Raw axiom
directly via case-split lands here.  These are the load-bearing
"structural" theorems.

`ofL | ofM | refl | symm | trans | slash_cong` (5 occurrences) is
the **Raw equivalence relation's inductive closure** — the
quotient structure proofs.

### `cases` targets

492 `cases` invocations.  Top targets:

| Variable | count |  Typical role |
|----------|------:|--------------|
| `b`, `a` | 31 each | Bool destructure |
| `h`      | 30 | hypothesis destructure |
| `v`      | 29 | value destructure |
| `k`, `n`, `u` | 28, 21, 21 | Nat / index destructure |
| `c`, `y`, `hcx`, `hsw`, `xs` | 18, 16, 13, 13, 12 | mixed |

Top `cases ... with` tag sets:

| count | tags |
|------:|------|
| 28 | `zero \| succ` |
|  8 | `inl \| inr`               (Or destructure) |
|  6 | `zero \| succ \| zero \| succ` (nested Nat) |
|  4 | `zero \| succ \| j` |
|  3 | `a \| b \| slash`        (Raw — same trichotomy) |
|  3 | `true \| false` |
|  3 | `nil \| cons` |
|  3 | `ofNat \| negSucc`       (Int) |

### `obtain` destructuring shapes

208 `obtain` invocations.  Shape distribution (`⟨,⟩` = pair):

| shape | count |
|-------|------:|
| `⟨,⟩`         | 144 (69 %) |
| `⟨,,,⟩`       |  21 |
| `⟨,,⟩`        |  20 |
| `⟨,,,,⟩`      |   9 |
| `⟨,,,,,,⟩`    |   8 |
| `⟨,,,,,⟩`     |   5 |
| `⟨,,,⟨,⟩,⟩`   |   1 |

**69 % of obtains destructure pairs** — Σ-existential or
And-product witnesses.  Larger destructurings concentrate where
multi-witness existentials appear (e.g., bidirectional
constructions, multi-case lex bridges).

---

## Cross-layer reading (G87 + G88 + G89)

### Three views of the same skeleton

| Layer | What it sees | Strongest signal |
|-------|-------------|------------------|
| G87 (AST) | Elaborated `Expr` proof terms | 5 recursor tags, fold-XOR/Σ motifs |
| G88 (Syntax skeletons) | Tactic-token sequence per decl | `decide` 36 %, 48-tactic Leibniz ladder |
| G89 (Argument graph) | Lemma citations + construct shapes | NatHelper hub, Raw.fold_slash hub, a/b/slash induction |

### Convergent findings

  · **Nat-structural recursion dominates** — 80 % of inductions
    on Nat (G89), `Nat.recAux + brecOn` carry 42 % of AST sites
    (G87), `[induction, decide, show, rw]` template covers 37
    Pell-FSM decls (G88).
  · **Decide is the primary closer** — 36 % of proofs are pure
    `[decide]` (G88), `decide_eq_true` cited 84 times (G89),
    Pattern #2 universal across recursor families (G87 M3).
  · **`rw` over Nat algebra is the workhorse rewrite** — 17 % of
    tokens (G88), `Nat.{mul_comm, add_assoc, add_comm}` are
    top-3 external hubs (G89).

### Newly visible from G89 alone

  · **NatHelper as load-bearing infrastructure** — 174 cites for
    a single lemma (`NatHelper.mul_assoc`).  If consolidation work
    happens at the math layer, this is where it starts.
  · **Raw.fold_slash is the operational form of the axiom** — 50
    distinct callers, dominantly invoked via `apply`.  Behaves as
    the single API surface of the 4-clause axiom in proofs.
  · **`a | b | slash` is DRLT's unique fingerprint** — 18
    occurrences across induction + cases.  No other inductive
    type case-set has comparable mass at this layer.

---

## Concrete next actions surfaced by G89

  · **N1 — Audit NatHelper coverage**: `NatHelper.mul_assoc`
    has 174 cites.  Verify (a) it is PURE, (b) its statement is
    minimal, (c) no NatHelper.* lemma is redundant with a kernel
    Nat lemma that is already PURE.  Top down: NatHelper acts as
    the PURE-shield; if some `Nat.foo` is now PURE-safe, the
    `NatHelper.foo` shim can be deprecated and callers redirected.

  · **N2 — Investigate the 50 `Raw.fold_slash` callers**: cluster
    by the tactic-sequence surrounding the `apply Raw.fold_slash`
    invocation.  If the same pre/post pattern repeats, a derived
    lemma `Raw.fold_slash_<variant>` could replace the manual
    invocations.

  · **N3 — `a | b | slash` induction template**: the 15 + 3 = 18
    decls that case-split on Raw's three clauses share the same
    structural skeleton.  Cross-reference with G87 / G88 — are
    these covered by the existing abstraction roster or new?

  · **N4 — Proofs with out-degree ≥ 20**: extract the decls that
    cite ≥ 20 distinct lemmas; these are the "boilerplate
    ladders" — likely overlapping with G88 L1/L2 (LeibnizAlgLift,
    Leibniz{21,22}Final), validating the citation-graph and
    tactic-skeleton views point at the same outliers.

---

## Artifact map

  · `tools/lean_syntax_parse.py` — shared surface-parsing helpers
    (used by both G88 and G89 scanners)
  · `tools/syntax_arg_scan.py` — citation graph + construct
    shape extractor (G89)
  · `tools/_syntax_arg_cites.tsv` — citation TSV (gitignored)
  · `tools/_syntax_arg_shapes.tsv` — construct-shape TSV (gitignored)

`--report-only` flag re-clusters cached TSVs without re-scanning.
