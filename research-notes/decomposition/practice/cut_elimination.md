# Decomposition: proof theory / cut-elimination (sequent calculus, the cut rule, Gentzen's Hauptsatz, normalization, strong normalization, the subformula property, the proof-theoretic ordinal)

*A FRESH decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`). The
sharpened proof-theory companion to `curry_howard.md` — which read `⟨C|L⟩ = ⟨proof|proposition⟩` and
normalization = `view=fold`. This entry does NOT re-skin that. Its NEW datum is on **the cut rule
specifically**: cut = the **composition** of the 2-category of readings (`refines_trans` /
`view_factors_through_morphism`), so the **cut-elimination theorem = admissibility of composition =
every arrow reduces to a cut-free normal form**, the `raw_initial`/`fold` normal form read on proofs;
the **subformula property = the fold's no-new-atoms structural-recursion property** (the catamorphism
mentions only sub-distinctions of its input); and the **proof-theoretic ordinal ε₀ = the `q=−1`
height-escape** that ties `ordinals.md` (the height ceiling) to `godel.md` (the diagonal /
consistency-strength limit). Honest verdict: **PREDICTION + EXTEND**, with a real but toy in-repo
witness (`Logic/CutElimination.lean`, 10/0 PURE) and a precisely-located absent object (a genuine
`Sequent`/`Formula`/cut-rule calculus with a formula-induction Hauptsatz + subformula property).*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — distinguishing, iterated: a **proof is a `Raw`-tree** built by the
  inference rules (the same `C` as `curry_howard.md`). A sequent-calculus derivation is exactly a
  finite tree whose nodes are rule-applications and whose leaves are axioms — i.e. one `Raw`
  (`Lens/LensCore.lean` `Raw`, built on `Tree`: two bases `Raw.a`/`Raw.b`, one combine `Raw.slash`).
  The **cut rule** is a binary node: from a derivation of `Γ ⊢ A` and one of `A, Δ ⊢ C` build
  `Γ, Δ ⊢ C` — a `slash` combining two already-built sub-derivations on the shared cut-formula `A`.
  So a proof-with-cuts is a `Raw` containing combine-nodes that mention a formula `A` not appearing
  in the conclusion. A **cut-free** proof is a `Raw` in which every combine-node mentions only
  sub-distinctions of its own conclusion — the normal form.

- **Reading `L`** — the **reduction / normalization reading** (the `q=+1` peel of `curry_howard.md`),
  read here on the *cut node specifically*:
  - **the cut rule = composition** = the 2-category's `∘`/`⊗`. Modus ponens / cut on `A` is
    `Lens.refines_trans` (`LensCore.lean:95`: `A→B` then `B→C` gives `A→C`, the cut-formula `B`
    eliminated) and, at the 2-cell level, `view_factors_through_morphism` (`Compose/Morphism.lean:37`:
    `M.view = h ∘ L.view`, naturality — composition of readings is admissible, term for term).
  - **cut-elimination = `normalize`** = the fold to the unique cut-free normal form. Evaluating the
    catamorphism `Raw.fold` (`Fold.lean:22`) IS the unique arrow out of the free object `Raw`
    (`raw_initial`, `SemanticAtom.lean:412`; `universalMorphism_unique`, `:388`); any two
    normalizing maps agree pointwise (`dhom_unique_pointwise`, `UniversalDistinguishing.lean:103`).
  - **the subformula property = the fold's no-new-atoms structural-recursion law.** `Raw.fold`
    recurses *structurally*: its value at `slash x y` is built only from its values at the
    sub-trees `x`, `y` (`fold_slash`, the homomorphism law) — it **invents no atom not already
    present in the input**. Read on proofs: the cut-free normal form mentions only sub-distinctions
    (subformulas) of the end-sequent — the catamorphism cannot introduce a new formula `A` that the
    conclusion does not already decompose into. The subformula property is not an extra theorem; it
    is *what structural recursion is*.

- **Residue** — the reduction reading's self-application surplus, split at the two `q=±1` poles:
  - **`q=+1` (terminate / converge) — STRONG NORMALIZATION & the HAUPTSATZ.** Cut-elimination
    terminates: there is **no infinite reduction sequence** (`Lambek.no_infinite_descent`,
    `Lambek.lean:273`, PURE — no total `chain : Nat → Raw` peeling at every step; a chain of length
    `depth+1` would drive depth below 0). Equivalently the peel relation is **well-founded**
    (`isPart_wf`, `:199`), every descent bottoms out at the **atomic floor = the cut-free normal
    form** (`terminal_iff_atom`, `:308`; `no_part_of_atom`, `:178`), with the explicit per-step rate
    `part_depth_succ_le` (`:245`: each peel drops at least the unit `1` of depth — this is Gentzen's
    cut-rank/degree measure in 213-native form). The atomic floor is reached, the converging
    unimodular pole (`ResidueTag` `q=+1`, `converge_residue_fixed`, `ResidueTag.lean:160`;
    `golden_is_converge`, `:180`). **This is the SAME termination floor `curry_howard.md` uses** —
    cut-elimination and β/SN are one descent reading on one `C`.
  - **`q=−1` (escape / reached-by-none) — the PROOF-THEORETIC ORDINAL & CONSISTENCY-STRENGTH LIMIT.**
    The *height* of the cut-elimination measure, pushed past every finite stage, is the
    proof-theoretic ordinal (ε₀ for PA). It is the **`q=−1` height-escape of `ordinals.md`**: the
    height-reading `L↑`'s residue over the unbounded ascent (`MuNuMirror.ascent_unbounded`,
    `:50`), named one scale up as the `ω^ω`/ε₀-direction (`DepthHeightDiagonal.height_diagonal_escapes`,
    `:56`; `epsilon_direction`, `:71`) — and it relocates the global self-cover non-surjection
    (`object1_not_surjective`, `FlatOntologyClosure.lean:61`). Gödel's second theorem — the system
    cannot prove the well-foundedness up to its own ordinal, i.e. cannot prove its own consistency —
    is the **same `q=−1` escaping diagonal** as `godel.md` (`russell_liar_no_surjection`,
    `OneDiagonal.lean:87`; `no_surjection_of_fixedpointfree`, `:51`). So cut-elimination's
    *termination* (`q=+1`, reached) and its *ordinal / consistency-strength* (`q=−1`, reached-by-none)
    are **one residue at its two unimodular signs** — `residue_tag_two_poles` (`ResidueTag.lean:228`)
    exhibited on sequent proofs.

## Re-seeing — ⟨C | L⟩

```
   a derivation π            =  a Raw-tree built by the inference rules                       (C)
   the cut rule (on A)       =  a slash-node combining two sub-derivations on cut-formula A
                                = COMPOSITION  (refines_trans; view_factors_through_morphism)  (the ∘/⊗ of the 2-cat)
   a cut-FREE derivation     =  a Raw whose every node mentions only sub-distinctions of its conclusion
   CUT-ELIMINATION           =  normalize = the fold to the cut-free normal form
                                = ADMISSIBILITY OF COMPOSITION  (every arrow reduces to a cut-free arrow)
                                  (raw_initial + dhom_unique_pointwise: the UNIQUE arrow out of the free object)
   the SUBFORMULA PROPERTY   =  the fold's no-new-atoms structural-recursion law
                                  (fold_slash: value at slash x y built only from x,y — no atom invented)
   STRONG NORMALIZATION      =  Residue(reduction-reading, C) at q=+1 = cut-elim TERMINATES
                                  (no_infinite_descent / isPart_wf; per-step drop part_depth_succ_le = cut-rank)
   the HAUPTSATZ             =  the q=+1 floor reached: every proof has a cut-free normal form
   PROOF-THEORETIC ORDINAL   =  Residue(L↑, C) at q=−1 = the height-escape (ε₀-direction)
   (ε₀ for PA)                 (height_diagonal_escapes / epsilon_direction; ordinals.md's ceiling)
   CONSISTENCY-STRENGTH LIMIT=  Gödel-2 = the q=−1 escaping diagonal on the proof self-cover (godel.md)
```

## THE REVELATION — cut = composition; cut-elimination = admissibility-of-composition = arrow-normalization; subformula = the fold's no-new-atoms law; ε₀ = the q=−1 height-escape

**COLLAPSE 1 — the cut rule IS the composition of the 2-category of readings.** `curry_howard.md`
read modus ponens as `refines_trans` in passing; the proof-theoretic content is sharper. In the
sequent calculus the cut rule is the *only* rule that lets you compose two derivations through a
formula not in either conclusion — exactly `A→B` ∘ `B→C` = `A→C` with `B` (the cut-formula)
eliminated. That is `Lens.refines_trans` (`LensCore.lean:95`) as a 1-cell composition, and
`view_factors_through_morphism` (`Compose/Morphism.lean:37`, the naturality triangle
`M.view = h∘L.view`) as the 2-cell statement that *composition of readings is well-defined*. So the
cut rule is not a primitive proof-rule the calculus must import — it is the composition the README
v7.1 already records readings as having (readings form a 2-category, ∅-axiom).

**COLLAPSE 2 — cut-elimination = admissibility of composition = arrow-normalization.** Gentzen's
Hauptsatz says: the cut rule is *admissible* — anything provable with cut is provable without it.
Categorially this is "every arrow built using `∘` reduces to a normal-form arrow not mentioning the
intermediate object." That is exactly `raw_initial` + `dhom_unique_pointwise`: the unique arrow out
of the free/initial object `Raw` is `Raw.fold`, and any composite normalizes to it. **Cut-elimination
= the fold-to-normal-form (`view=fold` initiality) read as "composition is admissible."** This is the
NEW sentence beyond `curry_howard.md`: there, normalization = the fold; here, the *cut rule
specifically* is the composition, and *its* elimination is the proof that the composition adds no
arrows — `dhom_unique_pointwise` is the admissibility.

**COLLAPSE 3 — the subformula property = the fold's no-new-atoms structural-recursion law.** A
cut-free proof has the subformula property: every formula in it is a subformula of the end-sequent.
This is *precisely* the defining property of a catamorphism: `Raw.fold`'s value at `slash x y` is
built only from its values at `x` and `y` (`fold_slash`), so it can mention no atom absent from its
input. Cut, by contrast, is the *one* node that introduces a formula `A` (the cut-formula) absent
from the conclusion — and eliminating it is exactly forcing the proof into structural-recursive
(subformula-only) form. So the subformula property is not a separate corollary of the Hauptsatz; it
is what it *means* for the proof to be a fold. **NEW:** `curry_howard.md` never names the subformula
property; it is the structural-recursion law of `Raw.fold` read on proofs.

**FORCING — strong normalization is forced by the `q=+1` well-founded measure already in `C`.** SN of
cut-elimination is not stipulated; it is `Lambek.no_infinite_descent` (`:273`): the depth of the
`Raw` strictly drops at every peel (`part_depth_succ_le`, `:245` — the irreducible step `1`, i.e.
Gentzen's cut-degree dropping), so no infinite reduction chain exists and the floor (cut-free normal
form, `terminal_iff_atom`) is reached in `≤ depth+1` steps. The SAME `no_infinite_descent` floor
`curry_howard.md` uses for β-SN — cut-elimination and β-normalization are one descent reading, the
confluent+terminating Side-A of the colimit synthesis (`FreeReduction.lean`, 26/0: the free
normal-form Σ-quotient, no `Quot`), here on proofs.

**SPINE — the proof-theoretic ordinal is the `q=−1` pole tying `ordinals.md` + `godel.md`.** This is
the load-bearing find. Cut-elimination's termination is `q=+1` (the floor is *reached*). But the
*ordinal* measuring how high the cut-elimination procedure can climb — ε₀ for PA — is `q=−1`: it is
the height-reading's residue over an unbounded ascent, **reached-by-none**, named only by its finite
generator (`ordinals.md`: `ascent_unbounded`, no `Raw` has depth `ω`; `height_diagonal_escapes` /
`epsilon_direction` name the ε₀-*direction*, not a completed ε₀). And Gödel's second incompleteness
theorem — PA cannot prove transfinite induction up to ε₀, hence cannot prove its own consistency — is
the SAME `q=−1` escaping diagonal as `godel.md` (`russell_liar_no_surjection`,
`no_surjection_of_fixedpointfree`; `object1_not_surjective`). So the *strength* of cut-elimination
(the ordinal it needs, the consistency it implies) is the escape pole of the very residue whose
converge pole is its termination. **`residue_tag_two_poles` (`ResidueTag.lean:228`) on sequent
proofs: one residue, two signs — terminate (`q=+1`, `no_infinite_descent`) / climb-out (`q=−1`, ε₀ =
`height_diagonal_escapes` = the consistency-strength ceiling).** This unifies `ordinals.md`'s height
ceiling and `godel.md`'s diagonal as one object read on cut-elimination — which neither prior note
did.

**What is NEW vs `curry_howard.md`** (the re-skin guard): `curry_howard.md` gave (i) `⟨proof|prop⟩`,
(ii) normalization = the fold, (iii) SN = `no_infinite_descent`, (iv) consistency `q=+1` vs Gödel
`q=−1`. This entry adds, on the cut rule *specifically*: (a) **cut = the 2-category's composition**
(`refines_trans` / `view_factors_through_morphism`), so (b) **cut-elimination = admissibility of
composition = arrow-normalization** (`dhom_unique_pointwise` is the admissibility); (c) **the
subformula property = the fold's no-new-atoms structural-recursion law** (`fold_slash`) — unnamed in
`curry_howard.md`; (d) **the proof-theoretic ordinal ε₀ = the `q=−1` height-escape**, tying
`ordinals.md` (the height ceiling) to `godel.md` (the diagonal / consistency-strength) — the cut-rank
measure (`part_depth_succ_le`) is the finite signature whose unbounded ascent is ε₀.

## VALIDATE — verdict

**EXTEND + PREDICTION, no new primitive.** The model v7.1 absorbs cut-elimination with zero new
axes: cut = composition (the 2-category, already recorded), cut-elimination = the fold-to-normal-form
(`raw_initial`/`view=fold`, the read-op = initiality), the subformula property = the fold's
structural-recursion law (`fold_slash`), SN = the `q=+1` well-founded floor (`no_infinite_descent`),
the proof-theoretic ordinal / consistency-strength = the `q=−1` height-escape (`ordinals.md` +
`godel.md`). It is the calculus's OWN normalization operation instanced on sequent proofs — not a
new field but the `curry_howard.md` substrate read on the cut rule, plus the three new sentences
above.

**Does sequent calculus need a genuine proof-term primitive that is absent? — HONEST: partly.** The
*engine* is fully built and PURE (initiality, the well-founded floor, the `q=±1` tag, the height
residue). What is **absent** is a genuine `Sequent`/`Formula`/cut-rule object: a `Formula` inductive,
a `Sequent := List Formula ⊢ List Formula`, the structural+logical rules with cut as a constructor,
and a Hauptsatz proved by **double induction on cut-formula complexity and cut-height** with a
subformula-property corollary. The repo's `Logic/CutElimination.lean` (10/0 PURE) is a **real but
toy** witness: it models a proof as `Trajectory := List Bool` and cut-elimination as
left-to-right cancellation of adjacent unequal bits (`normalize_tf : normalize [true,false] = []`,
`normalize_tfft : … = []`), with `compose = ++` (composition) and length-drop. It is genuinely
∅-axiom and genuinely *is* "cut = composition, eliminate adjacent inverse pairs, length decreases" —
but it has **no formulas, no cut-formula complexity, no subformula property, and no
well-foundedness/ordinal** wired in; it is the 2-element-alphabet shadow of the Hauptsatz, not the
theorem. So the named object is **predicted-not-built** in its load-bearing form, exactly the dual of
`curry_howard.md`'s absent typed λ-calculus and `model_theory.md`'s absent FOL syntax. The
*structural prediction* (cut-elimination lands at the `no_infinite_descent` floor, the cut-rank is
`part_depth_succ_le`, the ordinal is the `q=−1` height-residue) is delivered; the *named formula-
induction Hauptsatz with subformula property* is the open instance.

## Verified Lean anchors (file:line:theorem — all grep/Read-confirmed this session; purity via `tools/scan_axioms.py` from repo root)

| Leg | Theorem / def (file:line : name) | Status |
|---|---|---|
| **proof = derivation = `Raw`-tree; cut node = `slash`** | `Lens/LensCore.lean` `Raw`; `Theory/Raw/Fold.lean:22 Raw.fold` (catamorphism / recursor) | (def) ✓ |
| **★ subformula property = the fold's no-new-atoms structural-recursion law** | `Theory/Raw/Fold.lean` `fold_slash` (value at `slash x y` built only from `x,y`) | PURE (Fold folds used PURE) ✓ |
| **cut rule = composition (1-cell)** = modus ponens | `Lens/LensCore.lean:95 Lens.refines_trans`; `:93 refines_refl`; `:90 Lens.refines` | ∅-axiom PURE ✓ |
| **cut = composition (2-cell) / composition admissible** | `Lens/Compose/Morphism.lean:37 view_factors_through_morphism`; `:29 IsLensMorphism`; `:60 refines_of_morphism` | ∅-axiom PURE (3/0) ✓ |
| **★ cut-elimination = fold to the UNIQUE cut-free normal form = admissibility of composition** | `Lens/Foundations/SemanticAtom.lean:412 raw_initial`; `:388 universalMorphism_unique`; `:108 universalMorphism` | ∅-axiom PURE ✓ |
| uniqueness of the normal form (the only arrow out of the free object) | `Lens/Foundations/UniversalDistinguishing.lean:103 dhom_unique_pointwise` | ∅-axiom PURE (6/0) ✓ |
| **★ STRONG NORMALIZATION = no infinite cut-elimination = the `q=+1` well-founded descent** | `Theory/Raw/Lambek.lean:273 no_infinite_descent`; `:199 isPart_wf`; `:252 descent_chain_drops` | ∅-axiom PURE ✓ |
| **cut-rank / cut-degree drops per step** (Gentzen measure, native form) | `Theory/Raw/Lambek.lean:245 part_depth_succ_le`; `:187 part_depth_lt` | ∅-axiom PURE ✓ |
| **HAUPTSATZ floor = cut-free normal form = the atomic terminal** | `Theory/Raw/Lambek.lean:308 terminal_iff_atom`; `:178 no_part_of_atom` | ∅-axiom PURE (22/0) ✓ |
| reduction strictly descends / ascent total vs descent finite | `Theory/Raw/MuNuMirror.lean:80 succ_not_idempotent`; `:105 ascent_total_descent_partial` | ∅-axiom PURE (8/0) ✓ |
| **★ proof-theoretic ordinal ε₀ = the `q=−1` height-escape (the ascent past every finite cut-rank)** | `Theory/Raw/MuNuMirror.lean:50 ascent_unbounded`; `Analysis/Cauchy/DepthHeightDiagonal.lean:56 height_diagonal_escapes`; `:71 epsilon_direction` | ∅-axiom PURE ✓ |
| **CONSISTENCY = the `q=+1` converging pole** (floor reached) | `Lib/Math/Foundations/ResidueTag.lean:160 converge_residue_fixed`; `:180 golden_is_converge`; `:86 multiplier_unimodular`; `:228 residue_tag_two_poles` | ∅-axiom PURE (55/0) ✓ |
| **CONSISTENCY-STRENGTH LIMIT (Gödel-2) = the `q=−1` escaping diagonal** | `Lens/Foundations/OneDiagonal.lean:51 no_surjection_of_fixedpointfree`; `:87 russell_liar_no_surjection`; `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective` | ∅-axiom PURE ✓ |
| **toy in-repo cut-elimination witness** (cut = `++`, eliminate adjacent inverse pairs, length drops) | `Lib/Math/Combinatorics/Logic/CutElimination.lean:36 normalize_tf`; `:50 normalize_tfft`; `:44 normalize_tft`; `:54 normalize_length_decrease`; `Logic/Proof.lean:40 compose`, `:68 normalize` | ∅-axiom PURE (10/0 + 11/0) ✓ |
| graded-relation shape (skein/Leibniz) — for cross-frame, NOT cut | `Cohomology/Delta/V4Capstone.lean:62 leibniz_universal_delta4`; `:41 dsq_zero_universal_delta4` | ∅-axiom PURE ✓ |
| colimit Side-A normal-form Σ-quotient (confluent+terminating, no `Quot`) | `Lib/Math/Algebra/Group/FreeReduction.lean:237 proj_val_eq_iff`; `:264 free_group_quotient_no_quot` | ∅-axiom PURE (26/0) ✓ |

**Fresh purity scans (this session, `tools/scan_axioms.py` from repo root):**
- `E213.Lib.Math.Combinatorics.Logic.CutElimination` → **10 pure / 0 dirty**
- `E213.Lib.Math.Combinatorics.Logic.Proof` → **11 pure / 0 dirty**
- `E213.Theory.Raw.Lambek` → **22 pure / 0 dirty**
- `E213.Theory.Raw.MuNuMirror` → **8 pure / 0 dirty**
- `E213.Lib.Math.Foundations.ResidueTag` → **55 pure / 0 dirty**
- `E213.Lens.Foundations.UniversalDistinguishing` → **6 pure / 0 dirty**
- `E213.Lens.Foundations.OneDiagonal` → **11 pure / 0 dirty**
- `E213.Lens.Foundations.FlatOntologyClosure` → **7 pure / 0 dirty**
- `E213.Lens.Compose.Morphism` → **3 pure / 0 dirty**
- `E213.Lib.Math.Algebra.Group.FreeReduction` → **26 pure / 0 dirty**
- `E213.Lens.Foundations.SemanticAtom` → **11 pure / 23 dirty** module-wide, but the three cited
  theorems are individually PURE: `raw_initial`, `universalMorphism_unique`, `universalMorphism_slash`
  scan `[PURE]` (the 23 DIRTY are the `propext`-using classical Prop connectives — the
  propext/funext 1-categorical ceiling, SYNTHESIS §5.3, not on the cut-elimination path).

## Dropped / flagged (honest)

- **A genuine `Sequent` / `Formula` / cut-rule calculus with a formula-induction Hauptsatz —
  ABSENT (predicted-not-built).** No `Formula` inductive, no `Sequent := Γ ⊢ Δ`, no cut as a rule
  constructor, no double-induction-on-(cut-degree, cut-height) Hauptsatz, no subformula-property
  theorem stated on formulas. `Logic/CutElimination.lean` is the `List Bool` *shadow* (cut = `++`,
  eliminate adjacent inverse bits) — real and PURE but with no formulas, no cut-rank, no ordinal.
  The "cut = composition / cut-elim = arrow-normalization / subformula = fold-law" identification is
  the decomposition's framing on the existing `Raw`/`fold`/`refines`/`no_infinite_descent` engine,
  not a built sequent calculus. Dual of `curry_howard.md`'s absent typed λ-calculus and
  `model_theory.md`'s absent FOL syntax.
- **ε₀ as a *closed* ordinal — NOT built.** Per `ordinals.md`: `height_diagonal_escapes` /
  `epsilon_direction` name the ε₀-*direction* (one scale up); no transfinite arithmetic (`ω+ω`,
  `ε₀` as a value) is Lean-anchored. The proof-theoretic ordinal is cited as the `q=−1` *direction*
  / finite-signature (the unbounded cut-rank ascent), never as an inhabited transfinite object — the
  finite-signature rule biting exactly at `ω`, as in `ordinals.md`.
- **"strong-normalization-of-cut-elimination = `no_infinite_descent`" as ONE welded theorem —
  conceptual.** The descent engine is PURE-built and IS the abstract content of SN; no
  `Sequent`-with-cut object is instantiated onto it. The wiring (a cut-rank measure on derivations
  shown to equal `Raw.depth`'s drop) is the open instance — predicted (`part_depth_succ_le` is the
  step-`1` cut-degree drop), not discharged on a named calculus.
- **Buildable witness (verified shape):** the toy `Logic/CutElimination.lean` (10/0 PURE) already
  exists and is the confluent+terminating Side-A instance for a 2-symbol alphabet; a *next* buildable
  step the calculus predicts is a `Formula` inductive + `cutRank : Formula → Nat` with a
  `normalize`-drops-cutRank lemma factoring through `part_depth_succ_le` — the formula-graded analogue
  of `FreeReduction.proj_val_eq_iff`, mirroring how `FreeReduction.lean` cashed the colimit Side-A. Not
  built this session; flagged as the named promotion target.

## Cross-frame

`curry_howard.md` (the substrate: `⟨proof|prop⟩`, normalization = `view=fold`, SN =
`no_infinite_descent`, consistency `q=+1` vs Gödel `q=−1` — this entry sharpens it on the cut rule);
`category_theory.md` (`Raw` = initial object, `fold` = catamorphism, readings = 2-category — supplies
"cut = composition", "cut-elim = admissibility of composition"); `ordinals.md` (the height ceiling =
the proof-theoretic ordinal's `q=−1` escape; `ascent_unbounded` / `height_diagonal_escapes`);
`godel.md` (the `q=−1` diagonal = consistency-strength limit / Gödel-2); `model_theory.md`
(`view=fold` initiality = completeness, the `q=+1` companion). **VERDICT: EXTEND + PREDICTION** —
cut-elimination = the calculus's own fold-to-normal-form (`raw_initial`/`view=fold`) read on sequent
proofs, with cut = the 2-category's composition (`refines_trans`/`view_factors_through_morphism`),
cut-elimination = admissibility of composition / arrow-normalization (`dhom_unique_pointwise`), the
subformula property = the fold's no-new-atoms structural-recursion law (`fold_slash`), strong
normalization = the `q=+1` well-founded floor (`no_infinite_descent`, cut-rank = `part_depth_succ_le`),
and the proof-theoretic ordinal ε₀ / consistency-strength = the `q=−1` height-escape tying
`ordinals.md` + `godel.md` (`height_diagonal_escapes`, `object1_not_surjective`,
`residue_tag_two_poles`). No new primitive. The single precise absence: a *named* `Sequent`/`Formula`
cut-rule calculus with a formula-induction Hauptsatz + subformula-property theorem — the toy
`Logic/CutElimination.lean` is its 2-symbol shadow (10/0 PURE).
