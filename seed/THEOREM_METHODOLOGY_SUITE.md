# Theorem Methodology Suite

How DRLT's proof corpus is analysed, derived, falsified, and
consolidated.  This file combines four companion specifications
into one read-through:

  · **§TH-1** Proof-shape fingerprint — what makes two proofs
    "the same shape," and how the fingerprint scanners surface
    consolidation candidates.
  · **§TH-2** Raw-derivation: three technical readings — when
    "X is derived from Raw" is asserted, which of (α) / (β) / (γ)
    is meant.
  · **§TH-3** Falsifiability surface — the quantitative profile
    that operationalises `seed/AXIOM/08_falsifiability.md` §8.2.
  · **§TH-4** L1 4-sibling parametric methodology — the closure
    pattern that absorbed Part 3 + Part 5 of the Cup-AW Leibniz work
    into 2 parametric helpers.

Together: TH-1 surfaces a cluster, TH-2 verifies the cluster is
genuinely Raw-derivable, TH-3 confirms the abstraction preserves
the falsifier surface, TH-4 extracts the parametric helper.

Companions: `seed/META_SCAN_ARCHETYPES.md` (the 11 scanner
archetypes + dual-branch process model), `theory/meta/methodology_patterns.md`
Patterns #1-#20.

---

## §TH-1 Proof-shape fingerprint

How the 213 corpus identifies proof-shape clusters, what the
fingerprint captures, and what consolidation it enables.

### What is a "proof-shape fingerprint"?

A fingerprint of a proof is a normalised abstraction that captures
its structural pattern while ignoring per-instance content:

  · **Tactic token sequence**: the ordered list of top-level
    tactic names — `[intro, apply, show, constructor, intro, have, ...]`.
  · **Expr-node shape**: the AST shape after `unfold` and
    `simp`-normalisation, as a multiset of constructor/elim tags.
  · **Recursor invocation set**: which inductive types' `.rec` or
    `.casesOn` are called inside the proof body.
  · **Citation graph**: which other theorems are `exact`-applied
    or `rw`-rewritten.

Two proofs are **byte-identical at fingerprint level** when they
share all four projections.  A 2-sibling group exists when both
proofs in the pair share their fingerprint but differ in surface
text (variable names, specific Nat literals).

### Source catalogs

The canonical fingerprint inventory is split across:

  · `catalogs/recursor-inventory.md` — 185 inductive types ×
    recursor invocations.  The recursor set is the most stable
    discriminator (re-running the scanner is deterministic).
  · `catalogs/internal-hubs.md` — top E213-internal load-bearing
    lemmas by citation count (citation-graph + Expr-level
    callgraph surfaces).
  · `catalogs/falsifier-roster.md` — 135 `by decide` falsifier-
    style proofs, grouped by negation shape.
  · `catalogs/cross-domain-identifications.md` — 109 cross-
    namespace byte-identical-shape groups, 25 of which are
    substantive math↔physics bridges.
  · `lean/E213/ARCHITECTURE.md` NAV-3 note — `Bool.casesOn`
    (1,681 invocations) was missing from the fold-motif scanner's
    hardcoded 5-tag list, which led to the namespace-shape +
    recursor inventory correction (185 inductive types, not 5).

### What the fingerprint enables

**Consolidation candidates.**  When N proofs share fingerprint,
an abstraction is warranted.  The Part 3 + Part 4 + Part 5
work absorbed 280+ sites across 12 templates (L1, L2, C,
FLUX-1, COH-1/2/3, L3, L4, Pell-FSM, ModArith, M-recursor,
Pattern10, InvolutionTemplate).  Each template was surfaced by a
fingerprint-cluster scan.

**Mass tracking.**  Expr-node mass gives a numeric metric for
"how much elaboration would be retired" if a template absorbed
the cluster.  L1 α/β-side at 6.6M chars and FLUX-1 at 30K nodes
were the largest single consolidations.

**Cross-domain bridges.**  When fingerprint clusters span math
vs. physics namespaces, the bridge IS the equation.  CDI-5
(physics atomic-bracket containment) is 8 distinct "observed
constant X in DRLT-bracket [low, high]" proofs that are byte-
identical post-normalisation.

### How to re-run the scanner

```bash
python3 tools/syntax_tactic_scan.py     # tactic-token surface
python3 tools/ast_callgraph_scan.py     # Expr-level call graph
python3 tools/ast_shape_scan.py         # Expr-shape density + L1 zones
python3 tools/syntax_rw_cascade_scan.py # rw-cascade k-grams (adoption gap)
python3 tools/falsifier_mining_scan.py  # by-decide falsifier catalog
python3 tools/ast_typesig_scan.py       # type-sig + sort-universe
```

Each scanner writes a cached TSV to `tools/_<scan_name>_rows.tsv`
(gitignored).  Re-runs are deterministic.

### When this spec is reused

When future work surfaces a new fingerprint cluster, follow
the TH-1 → TH-4 chain:

  1. **§TH-1**: run scanners, identify cluster.
  2. **§TH-2**: verify the cluster is α/β-derivable (not just
     structural duplication).
  3. **§TH-3**: check that the abstraction preserves the
     falsifier surface (does not add axioms).
  4. **§TH-4**: extract the parametric helper; per-instance
     corollaries become 1-line calls.

---

## §TH-2 Raw-derivation: three technical readings

When "X is derived from Raw" appears in DRLT commentary, papers,
or AXIOM chapters, this section pins which reading is meant.
Implementation-level evidence in `lean/E213/`.

The phrase "everything in DRLT is derived from Raw" has three
distinct technical meanings.  Each is independently TRUE or FALSE
on a different basis.  Conflation is the common error.

### Reading (α) — Logical derivability

**Statement.**  Every theorem in `lean/E213/` closes under Lean's
kernel + the 4-clause Raw axiom set (no further axiom).

**Status.**  **TRUE.**  Verified by `#print axioms` on every
`★`-marked theorem.  No `Classical.choice`, no `native_decide`,
no `sorryAx`, no external axiom.  See `STRICT_ZERO_AXIOM.md` for
the canonical PURE/DIRTY ledger and `seed/AXIOM/08_falsifiability.md` §8.2 for the falsifiability rule that enforces this.

**Independently verified:**

  · Lean-core dep-purity audit on every cited core lemma.
  · Parallel-branch closure of all DIRTY-cited remnants (N5 / N6
    centralisations).
  · DRLT is **PURE-bounded on Lean 4 core** — no axiomatic
    escape hatch downstream of the 4-clause axiom.

The mechanical auditor is `#print axioms`.  Reading (α) is the
**logical** version: derivability under the kernel's notion of
proof.

### Reading (β) — Structural-content derivability

**Statement.**  The mathematical content of DRLT — specifically
the inevitability chain Raw → (NS, NT, d) = (3, 2, 5) → 6-theorem,
including the alive predicate (Clause-4 recursive per
`AliveDerivation.alive_iff_clause4_alive`) — is **provably
derivable from the 4-clause Raw axiom alone**.

**Status.**  **TRUE.**  The atomicity / Pell-unit invariant /
ZOmega^× = C_6 / dual-filling χ-sum chain constructs the corpus's
headline numbers (`α_em`, `m_t/m_c`, `η_B`, …) without invoking
external content — verified by the substantive branches' work and
catalogued in `catalogs/physics-constants.md`.

Reading (β) is the **structural-mathematical** version: the
mathematics itself, not just its kernel-checkability.

### Reading (γ) — Operational / definitional reduction

**Statement.**  Every theorem's **proof body** and **type
signature** Expr should transitively reduce to references to Raw
atoms via Expr-level forward edges.

**Status.**  **FALSE in general.**  Empirically (Expr-level
callgraph scanner + Expr-shape density scanner §1 + Raw-derivation
three-level taxonomy §2): only ~15 % of E213 declarations reach a
Raw atom via Expr-level forward edges within finite depth.

The remaining ~85 % use carrier types like:

  · `Cochain n k := Fin (binom n k) → Bool`
  · `Cut := Nat → Nat → Bool`
  · `binom` — Nat arithmetic
  · `Lens.view`, `Lens.combine` — Lens projections

These are **generic Lean infrastructure**, defined in terms of
`Nat`, `Bool`, `Int`, `Fin`, not in Raw-construction terms.  Their
Expr neither contains Raw atoms in its body nor in its type
signature.

**(γ) being false does not undermine (α) or (β).**  The architecture
is: **Raw-derived mathematical content layered on top of generic
Lean computational infrastructure.**  The math is Raw-native; the
substrate is Lean stdlib.

A version of DRLT where every carrier type unfolds to a Raw
construction at the Expr level — `Cochain` defined as a recursive
function over `Raw.fold`, `binom` defined as counting Raw sub-
trees, etc. — would be required to make (γ) true.  This is **not
the current design** and **not desirable**: the chosen substrate
(Nat / Bool / Fin) is what makes the corpus mechanically
tractable.

**Empirical evidence** (Raw-derivation three-level taxonomy §2):

| Metric | Body-only edges | Body ∪ type edges |
|---|---:|---:|
| Reach Raw | 1,111 (14.8 %) | 1,218 (14.7 %) |
| Max depth | 3 | 3 |
| Mean depth | 1.13 | 1.09 |

Adding type-signature edges barely changes the reach percentage.
The encapsulation isn't at the body-vs-type distinction; it's at
the **definitional layer** — carrier types are defined in non-Raw
terms.

### Why the distinction matters

The three readings answer different questions:

| Reading | Question | Answer | Verified by |
|---|---|---|---|
| (α) | "Is the proof logically closed under the Raw axiom set?" | YES | `#print axioms` |
| (β) | "Does the mathematics derive from Raw structurally?" | YES | substantive branch proofs |
| (γ) | "Does every Expr reduce to Raw atoms operationally?" | NO | Expr-level callgraph / Expr-shape density / Raw-derivation three-level taxonomy meta-scans |

A statement like "DRLT is grounded in Raw" usually means (α) +
(β).  Citing the "14.8 % reach Raw" empirical finding as a
counter-claim only contradicts (γ), which is not what (α) / (β)
require.

Conflation is the failure mode.  Specifying which reading is at
stake removes the confusion.

### Self-check before writing "derived from Raw"

When a future doc or commit message uses the phrase, the writer
should be able to point to one of (α) / (β) / (γ) as the intended
reading.  If none fits cleanly, the claim is unclear and needs
disambiguation.

---

## §TH-3 Falsifiability surface — quantitative profile

Quantifies the falsifiability rule of
`seed/AXIOM/08_falsifiability.md` §8.2 as an operational
footprint in the Lean corpus.  Pairs with the manual measurement-
falsifier roster in `catalogs/falsifiers.md` and the auto-
discovered roster in `catalogs/falsifier-roster.md`.

The falsifiability rule says: "If any result is shown to be
absolutely impossible without adding an axiom, the entirety of
213 is discarded."  This section measures how DRLT operationally
enacts that rule — which kinds of impossibility / distinguish-
ability statements the corpus actually proves.

### Two surfaces

**Physics surface** (`catalogs/falsifiers.md`).  26 manually-
curated entries (F1-F26): atomicity (d=5), neutrino ordering,
θ_QCD, 4th-generation absence, Cabibbo λ, m_p, m_t/m_c, η_B,
magic numbers, etc.

Each predicts what nature must satisfy if 213 holds.  Violation
by measurement = entire framework discarded.  This is the surface
that an experimentalist confronts.

**Structural surface** (`catalogs/falsifier-roster.md`).  135
auto-discovered entries from `tools/falsifier_mining_scan.py`.
Each is a Lean theorem of the shape `X ≠ Y` or `¬ ∃ ...` or
`¬ ∀ ...`, body-verified by `decide` / `native_decide`.

Each certifies what 213 itself forbids — internal impossibility
of construction, distinguishability of would-be-equal candidates,
non-existence of universals that would over-extend the positive
content.

### Quantitative profile

  · 135 decls match falsifier shape (negation marker + decide
    body).
  · 8 % of all tactic-bodied decls (population 1,117).
  · Compared to ~36 % positive `[decide]` proofs: roughly **1 in
    4 decide-proofs is a falsifier**.

| Category | Count | %   | Operational meaning |
|---|---:|---:|---|
| `ne` (`x ≠ y`)       | 105 | 78 % | Distinguishability witness — two candidates differ |
| `not` (general `¬ P`) |  20 | 15 % | Structural impossibility — P cannot be exhibited |
| `not_exists` (`¬ ∃`)  |   8 |  6 % | No construction satisfies the predicate |
| `not_forall` (`¬ ∀`)  |   2 |  1 % | A counter-instance breaks a universal claim |

**Why `≠` dominates (78 %).**  The Raw axiom's operational
primitive is *distinguishing* (Clause 1).  Non-distinguishing =
identity.  Most falsifiers therefore record "these two would-be-
same things are actually different" — operationally invoking
Clause 1.

### The 8 deepest impossibilities

These are the load-bearing negation claims — DRLT's machine-
checked "this candidate construction cannot exist" theorems.

| # | Decl | Statement |
|---|---|---|
| 1 | `Chain.chain_uncountable` | Raw functions `Nat → Raw` are uncountable: `¬ ∃ f, Function.Surjective f` |
| 2 | `Max.maxLens_R4_fails` | `maxLens` admits no swap-matching conjugation by `Nat → Nat` |
| 3 | `Reach.fin3_image_strict` | Universal morphism to `Fin 3` is not surjective |
| 4 | `Reach.int_image_strict` | Universal morphism to `Int` is not surjective |
| 5 | `SumNotCoproduct.sum_not_coproduct_xor` | `Sum Bool Bool` fails the coproduct property for XOR |
| 6-8 | (CayleyDickson tower + Lens layer) | three additional structural impossibilities |

These bound DRLT's positive side: without them, the positive
content could be trivially over-extended into territory the
residue doesn't support.

### The Cayley–Dickson tower as negation factory

The CD tower contributes 21 of the 135 (16 %):

  · `CayleyDickson/Levels/Cayley.lean`: 8 — octonion non-
    associativity witnesses.
  · `CayleyDickson/Levels/Sedenion.lean` + Heavy: 5 + 3 —
    sedenion non-alternative.
  · `CayleyDickson/Tower/CDDouble.lean`: 5 — doubling-construction
    mismatches.
  · `Lib/Math/Foundations/UniverseChain/Residue.lean`: 5 — residue
    distinguishes 5 atomic levels.

Each tower level provably *loses* an algebraic property
(commutativity → associativity → alternativity → power-
associativity → …).  Decide-verifying the loss creates a
falsifier.

**The Cayley–Dickson construction IS a systematic negation
generator** — each level a fresh batch of structural
impossibilities.

### Connection to the falsifiability doctrine

`seed/AXIOM/08_falsifiability.md` §8.2 says:

> 213 must never require any external axiom addition.  If any
> result is shown to be absolutely impossible without adding an
> axiom, the entirety of 213 is discarded.

The 135 auto-discovered + 26 manual falsifiers are the **active
content** of that rule:

  · Each `≠` witness is a Clause-1 distinguishing claim being
    operationally cashed in.
  · Each `¬ ∃` is a non-existence theorem closing a candidate
    construction.
  · Each `¬ ∀` is a counter-instance breaking a would-be
    universal.

If any of these were to fail (e.g., a `≠` witness shown to be `=`
under some valid Lens), it would either:

  (a) reveal a misclassification (the Lens choice was wrong → fix
      the Lens), or
  (b) reveal that adding an axiom is genuinely necessary → trigger
      the falsifiability rule → discard 213.

Per the rule, (b) is the dangerous case.  The corpus is structured
so that (a) is the recoverable interpretation; (b) has not been
observed.

### Operational signature

The Pattern #2 quantification (`theory/meta/methodology_patterns.md`):

  · 1,178 single-tactic `[decide]` proofs.
  · 135 negative-side `decide` proofs (this catalogue).
  · ~44 % of all decls are decide-routed (positive or negative).

Pattern #2 is not a methodological choice; it's the operational
signature of the corpus.  Falsifiability is mechanically enforced
because `decide` is the lingua franca of both positive proof and
negative impossibility.

### Regenerating

```bash
python3 tools/falsifier_mining_scan.py
# → TSV with all 135 entries (decl, file, category, body snippet)
```

TSV is gitignored.  Re-running takes ~1 minute.

---

## §TH-4 L1 4-sibling parametric methodology

How to consolidate a Cup-AW Leibniz lift 4-sibling group into 2
parametric helpers (one per side).  Companion to the implicit-
lemma-extraction deep dive and the L1 β/α-side commits.

### Surface pattern

A 4-sibling L1 family at degrees `(n, a, b)` consists of:

  · 2 β-decomp lenses (typically `b = 2`, varies over `a ∈ {1, 2}`)
  · 2 α-decomp lenses (typically `a = 2`, varies over `b ∈ {1, 2}`)

Each sibling's proof body is structurally identical (10-step
bilinearity expansion via `delta_cupAW_add_*` × 9 + `cupAW_add_*`
× 9 + `cupAW_delta_add_*` × 9 + `h_components ⟨i, _⟩` × 10 +
`combine_10`).

The variable parts: the cochain dimensions and the index Fin
type.

### β-side methodology

Parameter: left-factor degree `a`.

```lean
theorem leibniz_via_β_decomp_general {a : Nat}
    (α : Cochain 5 a) (β : Cochain 5 2)
    (i : Fin (binom 5 (a + 2 - 1 + 1)))   -- LHS index, reduces for abstract a
    (h_components : ∀ p, ...) :
    delta (cupAW 5 a 2 α β) i = xor (...) (...)
```

The β-side index type `a + 2 - 1 + 1` reduces because the
variable `a` is on the LEFT of `Nat.add` and the constant `2` is
on the RIGHT (Lean's `Nat.add` recurses on its RHS argument).
After Lean's automatic reduction, `a + 2 - 1 + 1 = a + 2`, which
unifies with the RHS index types `a + 1 + 2 - 1 = a + 2` and
`a + (2+1) - 1 = a + 2` — all reduce to the same canonical form.

Result: no casts needed; the parametric helper signature is
clean.

### α-side methodology

Parameter: right-factor degree `b`.

```lean
@[reducible] def castA (b : Nat) :
    Fin (binom 5 (2 + b - 1 + 1)) → Fin (binom 5 (3 + b - 1)) := ...
@[reducible] def castB (b : Nat) :
    Fin (binom 5 (2 + b - 1 + 1)) → Fin (binom 5 (2 + (b+1) - 1)) := ...

theorem leibniz_via_α_decomp_general {b : Nat}
    (α : Cochain 5 2) (β : Cochain 5 b)
    (i : Fin (binom 5 (2 + b - 1 + 1)))
    (h_components : ∀ p,
      delta (cupAW 5 2 b ...) i
        = xor (cupAW 5 3 b ... (castA b i))     -- RHS index 1: needs cast
              (cupAW 5 2 (b+1) ... (castB b i))) :  -- RHS index 2: needs cast
    ...
```

The α-side asymmetry: cup signature `cupAW 5 2 b` produces
`Cochain 5 (2 + b - 1)`, where `2 + b` is **stuck for abstract
`b`** (Nat.add doesn't reduce when the variable is on the RHS
argument).  The three index types appearing on LHS / RHS1 / RHS2
are propositionally equal (all = `b + 2`) but not definitionally
equal:

  · LHS: `2 + b - 1 + 1`   (from `delta (cupAW 5 2 b)`)
  · RHS1: `3 + b - 1`      (from `cupAW 5 3 b (delta α)`)
  · RHS2: `2 + (b+1) - 1`  (from `cupAW 5 2 (b+1) α (delta β)`)

Solution: explicit `Fin.cast` plumbing in two helpers (`castA`,
`castB`) that bridge the LHS index to the RHS index spaces.  The
casts use `Nat.add_comm` to swap the variable to the LHS where
Nat.add reduces.

The casts are `@[reducible]` so call-site `b ∈ {1, 2}` reduces
them to identity by `rfl` automatically.

### Caller pattern

For both sides, each concrete sibling becomes a 1-line corollary:

```lean
theorem leibniz_via_β_decomp_lens   -- (a=1, b=2)
    (α : Cochain 5 1) (β : Cochain 5 2) (i : Fin (binom 5 3))
    (h_components : ...) :
    delta (cupAW 5 1 2 α β) i = xor (...) (...) :=
  leibniz_via_β_decomp_general α β i h_components

theorem leibniz_via_α_decomp_21    -- (a=2, b=1)
    (α : Cochain 5 2) (β : Cochain 5 1) (i : Fin (binom 5 3))
    (h_components : ...) :
    delta (cupAW 5 2 1 α β) i = xor (...) (...) :=
  leibniz_via_α_decomp_general α β i h_components
```

The user's `h_components` (no cast) matches the generic helper's
casted `h_components` directly via `castA / castB` reducibility
at concrete `b`.

### Mass reduction

| sibling | original | after corollary |
|---|---:|---:|
| β-decomp at (5, 1, 2) | 95 lines | 20 lines |
| β-decomp at (5, 2, 2) | 83 lines | 16 lines |
| α-decomp at (5, 2, 1) | 101 lines | 41 lines |
| α-decomp at (5, 2, 2) | 101 lines | 41 lines |
| β generic helper | (new) | 113 lines |
| α generic helper | (new) | 131 lines |

Net: 380 → 362 lines but ~170 lines of repeated 10-step body
retired.

---

## Cross-references (unified)

### Specs

  · `seed/AXIOM/08_falsifiability.md` §8.2 — the discard rule
    grounding (α) and §TH-3.
  · `STRICT_ZERO_AXIOM.md` — canonical PURE / DIRTY ledger
    enforcing (α).
  · `seed/META_SCAN_ARCHETYPES.md` — 11 scanner archetypes +
    dual-branch process model.
  · `seed/CLOSED_FORM_SPEC.md` — closed-form catalogue with
    Bishop subsumption.

### Catalogs

  · `catalogs/falsifiers.md` — manual physics-falsifier roster
    (F1-F26).
  · `catalogs/falsifier-roster.md` — auto-discovered structural
    roster (135 entries).
  · `catalogs/recursor-inventory.md` — 185 inductive types with
    recursor invocations.
  · `catalogs/internal-hubs.md` — top E213-internal load-bearing
    lemmas.
  · `catalogs/cross-domain-identifications.md` — math ↔ physics
    byte-identical Expr groups.

### Lean modules

  · `lean/E213/Theory/Atomicity/PairForcing.lean` etc. —
    substantive derivations realising (β).
  · `lean/E213/Lib/Math/Cohomology/Cochain/Core.lean` — example
    of generic-substrate carrier type (`Cochain n k := Fin _ →
    Bool`).
  · `lean/E213/Lib/Math/Cohomology/CupAW/LeibnizAlgLiftBeta.lean` —
    β-side generic helper.
  · `lean/E213/Lib/Math/Cohomology/CupAW/LeibnizAlgLiftAlpha.lean` —
    α-side generic helper with `castA / castB` plumbing.
  · `lean/E213/Lib/Math/Cohomology/CupAW/LeibnizAlgLift{21,22,21Alpha,22Alpha}.lean`
    — 4 corollaries.

### Companions

  · `theory/meta/methodology_patterns.md` Patterns #1-#20.
  · `theory/meta/scanner_suite.md` — Tier-3 chapter mirroring the
    methodology.
  · `theory/meta/raw_derivation_levels.md` — Tier-3 chapter
    expanding §TH-2.
    abstraction registry.
