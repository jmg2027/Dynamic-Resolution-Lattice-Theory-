# G100 — Decide-failure mining: auto-discovered falsifier catalog

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Tool**: `tools/falsifier_mining_scan.py`  
**Companion**: G91, G92 (citation), G98 (unfold), G99 (rw-cascade).  
**Cross-branch**: parallel-branch G87 has manual falsifier
roster; this is the automated complement.

---

## Question

`decide` proves both positive (`p`) and negative (`¬ p`)
propositions.  G91 counted 36 % of decls as pure `[decide]` —
mostly positive.  What about the NEGATIVE side?  How many
theorems in DRLT are **machine-verified impossibility /
distinguishability claims**?  This catalog is DRLT's
"what cannot be" surface — its falsifiability footprint.

---

## Method

For each `theorem|lemma|def|instance|example` declaration:
  1. Extract signature (`<head> ... := by`) and body.
  2. Match if signature contains a negation marker: `¬`, `≠`,
     `Not `, `False`.
  3. Match if body uses `decide` or `native_decide` in its
     first 600 characters.
  4. Classify by sub-shape: `ne` (≠), `not_exists` (¬∃),
     `not_forall` (¬∀), `not` (general ¬P), plus edge cases.

**Population**: 1,117 tactic-bodied decls scanned (`theorem` +
`lemma` only at this layer — `def` and `instance` rarely host
falsifier statements).

---

## Results

  · **135 decls match — auto-discovered falsifiers**.
  · **8 % of tactic-bodied decls** are decide-verified
    impossibility / distinguishability claims.
  · For comparison: ~36 % of decls are positive `[decide]`
    proofs (G91).  So ~1 in 4-5 decide-proofs is a falsifier.

### Category breakdown

| Category | Count | % |
|----------|------:|--:|
| `ne` (`x ≠ y`)         | 105 | 78 % |
| `not` (general `¬ P`)  |  20 | 15 % |
| `not_exists` (`¬ ∃`)   |   8 |  6 % |
| `not_forall` (`¬ ∀`)   |   2 |  1 % |

**`≠` dominates at 78 %** — DRLT's negative knowledge is
overwhelmingly about *distinguishability witnesses* (two
candidates are different).  This matches the Raw axiom's
operational structure: distinguishing is the fundamental
operation; non-distinguishing = identity.  Most falsifiers are
"these two things would-be-same-but-aren't" statements.

### Top falsifier-producing files

| count | file |
|------:|------|
|     8 | `Lib/Math/CayleyDickson/Levels/Cayley.lean` |
|     6 | `Theory/Raw/ParenthesizationDistinct.lean` |
|     5 | `Lib/Math/CayleyDickson/Levels/Sedenion.lean` |
|     5 | `Lib/Math/CayleyDickson/Tower/CDDouble.lean` |
|     5 | `Lib/Math/UniverseChain/Residue.lean` |
|     4 | `Lens/Instances/F9.lean` |
|     3 | `Lens/Instances/Reach.lean`, `Lens/Properties/Diagonal.lean`, ... |

### The Cayley-Dickson tower is a falsifier factory

**4 CayleyDickson files contribute 21 of 135 falsifiers (16 %)**:

  · `Cayley.lean` (8): the Cayley level (= octonions), where
    associativity fails.  Each witness records a non-associative
    triple as decide-verified `(a * b) * c ≠ a * (b * c)`.
  · `Sedenion.lean` + `SedenionHeavy.lean` (5 + 3): the
    Sedenion level, where the alternative property fails.
  · `CDDouble.lean` (5): the doubling construction itself
    produces structural mismatches.
  · `TowerFixedPoint.lean` (3): the tower's fixed-point
    structure.

Methodologically, the **Cayley-Dickson construction IS a
negation generator**: each tower level provably *loses* an
algebraic property; decide-verifying the loss creates a falsifier.

---

## §1.  `ne` category — 105 distinguishability witnesses

Top samples illustrating the typology:

```
  · Theory/Raw/T_ne_F                     : T ≠ F
  · Lens/Instances/AB/abLens_distinguishes : abLens.view rAAB ≠ abLens.view rABB
  · Lens/Instances/Bool/bool_not_ne_id     : (!·) ≠ (id : Bool → Bool)
  · Lens/Instances/F9.one_ne_i            : F9.one ≠ F9.i
  · Lens/Instances/F9.i_mul_i_nonzero     : F9.mul F9.i F9.i ≠ F9.zero
  · Lens/Instances/Leaves/DepthIncomparable
        /depth_distinguishes              : Lens.depth.view rDeep ≠ Lens.depth.view rBalanced
  · Theory/Raw/ParenthesizationDistinct.* : ((a/b)/c) ≠ (a/(b/c))  -- 6 distinct trees
  · UniverseChain/Residue.residue_*_ne_*  : residue distinguishes 5 atomic levels
```

Sub-pattern: `${LemmaName}_distinguishes` and `*_ne_*` naming
conventions identify the falsifier role at the name layer
(~40 % of `ne` decls follow one of these conventions).

---

## §2.  `not_exists` category — 8 STRUCTURAL impossibility theorems

The deepest finds — these assert that **no construction exists**
satisfying a desired property:

```
  1. Chain/chain_uncountable
       ¬ ∃ f : Nat → (Nat → Raw), Function.Surjective f
       -- Raw functions Nat → Raw are uncountable

  2. Max/maxLens_R4_fails
       ¬ ∃ conj : Nat → Nat, SwapMatching maxLens conj
       -- maxLens has no swap-matching conjugation

  3. Reach/fin3_image_strict
       ∃ x : Fin 3, ¬ ∃ r : Raw, universalMorphism (Fin 3) r = x
       -- Fin 3 universal morphism is not surjective

  4. Reach/int_image_strict
       ∃ x : Int, ¬ ∃ r : Raw, universalMorphism Int r = x
       -- Int universal morphism is not surjective

  5. SumNotCoproduct/sum_not_coproduct_xor
       ¬ ∃ h : Sum Bool Bool → Bool, ...
       -- Sum Bool Bool fails the coproduct property for XOR

  6-8. Three more (CayleyDickson tower + Lens layer)
```

**Interpretation**: these are DRLT's most-load-bearing negation
claims.  They formally close major candidate constructions:
  · Raw is "too big" for countable enumeration (#1).
  · Specific Lenses cannot be conjugated by integer permutations (#2).
  · Universal morphisms into specific carriers fail to be
    surjective (#3, #4).
  · Bool + Bool doesn't realise the coproduct universal property
    in expected forms (#5).

These are NOT incidental — they're machine-checked **negative
existence theorems** that bound the theory's positive side.
The 8 of them constitute DRLT's automated
falsifiability-bite-point catalog.

---

## §3.  `not` category — 20 functional-property failures

Sample:

```
  · Lens/Instances/Bool/boolXorLens_not_homomorphism
        ¬ (∀ u v : Bool, !(xor u v) = xor (!u) (!v))
        -- Bool's NOT is NOT a homomorphism over XOR
  · Lens/Instances/Leaves/DepthJoin/three_classes_distinct
        ¬ JoinEquiv ... -- three distinct join-equivalence classes
  · Lens/Properties/RefinesParity/parity_not_refines_leaves
        ¬ parityLens.refines Lens.leaves
  · Lens/Instances/Max/maxLens_not_injective
        ¬ Function.Injective maxLens.view
  · Lens/Instances/Parity/parityLens_not_injective
        ¬ Function.Injective parityLens.view
```

Lens-property failures dominate: `_not_homomorphism`,
`_not_refines`, `_not_injective`.  Each is a Lens-specific
falsifier with a concrete structural reading.

---

## §4.  `not_forall` — 2 universality failures

Smallest category but conceptually significant:

```
  · ¬ ∀ ... : a universally-quantified candidate property fails
```

(Just 2 instances.)  Low count because most universality
failures are recast as `not_exists` (¬∃ witness of the
universal claim).

---

## Comparison vs parallel-branch G87 manual falsifier roster

G87 (parallel branch) lists ~5-10 manually-curated headline
falsifiers (e.g., 3-classes-distinct, sum_not_coproduct,
alive-gap closure, etc.).  My automated scan finds **135** —
much broader, since it catches every distinguishability `≠`
witness, not just structural impossibilities.

Useful split:

  · **Structural falsifiers** (G87 manual): the ~10 deepest
    impossibility / non-existence claims.  Curated.
  · **Distinguishability witnesses** (G100 automated): the
    ~100 `≠` claims that operate in proofs as discriminating
    moves.  Catalogued automatically.
  · **Functional property failures** (G100 §3): the ~20 `¬`
    claims about Lens or homomorphism properties.

The G100 catalog complements G87 by providing the **complete
machine-verified surface**, while G87 highlights the
**conceptually-load-bearing subset**.

---

## What this says about DRLT's logical structure

  1. **Falsifiability is operationalised at the `decide` layer**:
     8 % of all theorems are negative decide-proofs.  The
     0-axiom standard's falsifiability contract isn't a
     methodological aspiration — it's a measurable proof-shape.
  2. **Distinguishability is the dominant negation**: 78 % of
     falsifiers are `≠`.  Consistent with the Raw axiom's
     distinguishability primitive: every Lens carries its
     identity-witness as a `≠` failure where two non-equivalent
     Raw events have different views.
  3. **The Cayley-Dickson tower is a structural negation
     generator**: each level provably loses a property, and
     each loss is decide-witnessed.  16 % of falsifiers live
     in 4 CD files.
  4. **Lens-property falsifiers cluster**: `_not_injective`,
     `_not_refines`, `_not_homomorphism` recur across Lens
     instances — these collectively map out the **Lens
     incomparability lattice**.

For the "math-law / logical-structure" question (G98 §"Meta-
observations"): the falsifier catalog IS a direct logical-
structure surface.  Each `not_exists` row is an automatically-
discovered impossibility theorem; each `ne` row is a
distinguishability law in operational form.

---

## §5.  Connections to other meta-findings

  · `decide_eq_true` is cited 84 times (G92) — many of those
    cites are in falsifier proofs, applying the bridge to
    convert `decide`'s computation into the negation goal.
  · The `a | b | slash` Raw trichotomy (G94 §6) appears in
    `Theory/Raw/ParenthesizationDistinct.lean` (6 falsifiers
    from this catalog).  The trichotomy IS the substrate of
    Raw's negation generation.
  · `Raw.fold_slash` (G92 hub) is invoked in several
    `ne` proofs as the operational bridge between Raw's slash
    structure and the negation conclusion.

---

## Artifacts

  · `tools/falsifier_mining_scan.py` — scanner
  · `tools/_falsifier_rows.tsv` — TSV of all 135 rows
    (file, decl, category, signature) — gitignored

Run with `--report-only` to re-cluster cached rows.

---

## Future extensions

  · **Decide-disjunction mining**: theorems of the form
    `P ∨ ¬ Q` proved by decide are case-split falsifiers.
    Currently uncategorised by this scanner.
  · **Native_decide vs decide split**: how many falsifiers use
    `native_decide` (potentially un-PURE)?  Cross-check with
    `STRICT_ZERO_AXIOM.md` to ensure no falsifier is
    axiom-dirty.
  · **Falsifier dependency graph**: which falsifiers cite which
    other falsifiers — possibly surfaces a "negation
    hierarchy" parallel to the positive theorem hierarchy.
