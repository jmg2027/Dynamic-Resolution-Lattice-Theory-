# Decomposition: ∞-categories / higher category theory (quasi-categories, inner-horn fillers, weak composition up to coherent homotopy, the coherence tower, ∞-groupoids = spaces, (∞,1)-categories, the nerve)

*A FRESH decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants + the
q=±1 spine + the 2-category of readings + the residue-taking operation). Consolidates `two_cells.md`
(KEY — readings form a **2-category**: 1-cells `Lens.refines`, 2-cells `IsLensMorphism` /
`view_factors_through_morphism` / `LensIso`), `operads.md` (the A∞/associahedron coherence tower =
Catalan), `category_theory.md` (`Raw` = initial object, `Lens.view = Raw.fold` = the catamorphism),
`homotopy_theory.md` (∞-groupoid = space = the Ho(C)/weak-equivalence side), and `spectral_sequences.md`
/ `homological_algebra.md` (the residue re-entering as its own operand — the iterated tower). The thesis
to **test**, not re-skin:*

> **An ∞-category is the calculus's 2-category of readings (`two_cells.md`) extended to a COHERENCE
> TOWER — composition defined up to a tower of higher homotopies, indexed by the fold-height run up the
> CELL-DIMENSION.** `two_cells.md` established that readings form a 2-category (1-cells = `Lens.refines`,
> 2-cells = `IsLensMorphism` / `view_factors_through_morphism`). An ∞-category extends this UP: 3-cells,
> 4-cells, … = the coherence tower (associativity holds up to a 2-cell, coherent up to a 3-cell, …) =
> the **fold-height axis** (`Lambek.isPart_wf`, `MuNuMirror.succ_not_idempotent`) applied to the
> *cell-dimension* of the 2-category. The inner-horn filler (weak composition) = the fold/composition
> defined up to higher coherence (`Raw.fold` is associative on the nose at level 0; the general
> ∞-composition is the iterated-coherence version, `ResidueReentry.residue_perpetually_reenters`). The
> A∞/associahedron coherence (`operads.md`, `catalan_recursion_n`) = the same Catalan operad. ∞-groupoids
> = spaces (the homotopy hypothesis) = the all-invertible case = q=±1 with every cell invertible
> (`multiplier_unimodular`, `LensIso`). The nerve = the Lens-view of a category as a simplicial object
> (the Δ-complex `kSubset`/face-map machinery, `SimplexBasis`/`Delta.Core`). **No new primitive** — it is
> the 2-category of readings with the fold-height run up the cell-dimension.

---

## The decomposition (C / Reading / Residue)

- **Construction `C` — the 2-category of readings, with the cell-dimension as a fold-height axis.** The
  base is `two_cells.md`'s 2-category: objects/readings are folds out of the initial object `Raw`
  (`raw_initial`, `SemanticAtom.lean:412`); 1-cells are refinements `Lens.refines` (`LensCore.lean:90`);
  2-cells are `IsLensMorphism` / `view_factors_through_morphism` (`Morphism.lean:29,37`). An ∞-category
  asks for this same data *at every cell-dimension `n`* — `n`-cells relating `(n−1)`-cells, with
  composition coherent up to the next level up. The calculus already carries the axis this grading rides:
  the **fold-height** — distinguishing's height-raising (`MuNuMirror.ascent_unbounded`,
  `succ_not_idempotent`, `MuNuMirror.lean:50,80`) and its well-founded descent (`Lambek.isPart_wf`,
  `Lambek.lean:199`). `C` = the 2-category, with `n` = "cell-dimension" identified as the fold-height
  coordinate `category_theory.md`/`homological_algebra.md` already read as degree/dimension. The
  simplicial substrate is the Δ-complex: a `k`-simplex is the sorted `k`-subset `kSubset`
  (`SimplexBasis.lean:29`), its faces the `eraseIdx` boundary (`Delta.Core.deltaAt`, `Delta/Core.lean:42`).

- **Reading `L_∞` — "compose up to the next coherence level."** A quasi-category's defining reading is the
  **inner-horn filler**: given a composable string with the middle composite *unspecified*, fill it — but
  the fill is unique only *up to* a higher cell. In the calculus the strict (level-0) composite is the
  fold: `Raw.fold` (`Fold.lean:22`) evaluates a composition tree, its associativity `Raw.fold_slash`
  (`Fold.lean:37`) holding **on the nose**, and the composite is *forced unique* by
  `dhom_unique_pointwise` (`UniversalDistinguishing.lean:103`) — the strict-1-category corner. The
  ∞-reading is the *same fold carried with its coherence witnesses as data*: associativity holds up to a
  re-association 2-cell, coherent up to a 3-cell, … — the tower `operads.md` named (the associahedron
  carried-as-data, Catalan-counted). `L_∞` = `Raw.fold` read with the coherence tower retained, not
  quotiented away.

- **Residue `q = ±1`** — TWO residues, the README's two poles, and they partition exactly as in
  `homotopy_theory.md`:
  - **the q=−1 escape residue — the never-closing coherence tower (the genuinely ∞ part).** The tower of
    higher coherences *never bottoms out into a strict composite*: the residue re-enters as its own
    operand and the cover never closes — `ResidueReentry.residue_perpetually_reenters`
    (`ResidueReentry.lean:85`), `residue_reentry_never_closes` (`:63`). This is exactly
    `spectral_sequences.md`'s "the residue operation iterated"; the ∞ in ∞-category is this q=−1
    non-termination of the coherence tower, delegating ultimately to `object1_not_surjective`
    (`FlatOntologyClosure.lean:61`).
  - **the q=+1 converge residue — the all-invertible / strict-truncation pole.** An ∞-*groupoid* (every
    cell invertible) is the case where every coherence cell is an isomorphism — the `LensIso` groupoid
    (`lensIso_refl/symm/trans`, `Unified.lean:46,51,56`), with the involutive `q=+1` multiplier
    (`multiplier_unimodular`, `ResidueTag.lean:86`). An `(∞,n)`/strict truncation is the tower *closing*
    at finite height — the converging pole `golden_is_converge` (`ResidueTag.lean:180`).

---

## Re-seeing — ⟨C | L⟩ ⊕ Residue(L,C)

```
   an ∞-category C            =  ⟨ the 2-category of readings | the fold composed up the coherence tower ⟩ ⊕ Residue(q=±1)
   objects / 0-cells          =  readings = folds out of Raw          (raw_initial; Lens.view = Raw.fold)
   1-cells (morphisms)        =  Lens.refines                          (LensCore.lean:90)
   2-cells (naturality)       =  IsLensMorphism / view_factors_through_morphism  (Morphism.lean:29,37)
   n-cells for all n          =  the cell-dimension axis = the fold-height run UP  (MuNuMirror.succ_not_idempotent)
   the coherence tower        =  assoc up to a 2-cell, up to a 3-cell, …  =  fold-height on cell-dimension
   weak composition           =  Raw.fold, strict at level 0 (fold_slash), coherent above  (Fold.lean:22,37)
   inner-horn filler          =  fill the unspecified middle composite = the fold, unique up to higher cell
   horn filler is unique-up-to-higher = dhom_unique_pointwise at level 0 + the tower above  (UniversalDistinguishing:103)
   A∞ (assoc up to ∞-coherent homotopy) =  the associahedron coherence  =  Catalan  (catalan_recursion_n)
   the nerve N(C)             =  the Lens-view of a category as a simplicial object  (kSubset/face = Δ-complex)
   a k-simplex of the nerve   =  a sorted k-subset  (SimplexBasis.kSubset)  ;  faces = eraseIdx  (Delta.Core.deltaAt)
   ∞-groupoid = space (homotopy hypothesis) =  every cell invertible = the LensIso groupoid (q=+1, all-invertible)
   (∞,1)-category            =  cells invertible above dim 1, q=±1 only at dim 1 (the swap bit there)
   the ∞ (tower never closes)  =  q=−1 escape: the residue re-enters perpetually  (residue_perpetually_reenters)
   strict / truncated         =  q=+1 converge: tower closes at finite height  (golden_is_converge)
```

Set against the cross-frames: the **0/1/2-cell rows are `two_cells.md` verbatim** (all ∅-axiom), the
**n-cells-for-all-n / coherence-tower rows are the fold-height axis run up the cell-dimension** (the
genuinely NEW datum), the **A∞ row is `operads.md`'s Catalan** (re-used, not re-derived), the **nerve
rows are the Δ-complex `kSubset`/face machinery** (the in-repo simplicial-object leg), the
**∞-groupoid row is `homotopy_theory.md`'s q=+1 all-invertible `LensIso` pole**, and the trouble is
concentrated in the **named bundle** — the `quasiCategory`/`InfinityCategory`/`Kan`/`nerve` object is
ABSENT (grep-confirmed below).

---

## THE REVELATION (collapse + forcing + spine)

**Collapse — an ∞-category is NOT a new edifice above the 2-category: it is the same 2-category of
readings with the calculus's fold-height axis run up the *cell-dimension*, the coherence tower carried
as data rather than quotiented.** Four pieces, one per structural claim.

### 1. Collapse — the coherence tower = the fold-height axis applied to the cell-dimension (the NEW datum).

`two_cells.md` proved readings form a 2-category: 1-cells `Lens.refines`, 2-cells `IsLensMorphism` with
`view_factors_through_morphism` the naturality law, and `dhom_unique_pointwise` forcing the unique 2-cell
out of `Raw`. The genuinely new datum this note contributes — beyond re-skinning `two_cells.md` — is the
**identification of "n-cells for all n" with the fold-height axis already in `C`**. The README/SYNTHESIS
frame names the fold-height as bidirectional and load-bearing (`Lambek.isPart_wf`,
`MuNuMirror.succ_not_idempotent`), read out everywhere as dimension/degree/pole-order. An ∞-category's
*cell-dimension* is **that same axis**: a 3-cell is a coherence between 2-cells, a 4-cell a coherence
between 3-cells — height-raising on the cell-grading, exactly `MuNuMirror.succ_not_idempotent`
(`S(S r) ≠ S r`, depth strictly rises, the growing iteration-character) applied to "cell of cells." So
the ∞-tower is *not* a new primitive stacked on the 2-category; it is the 2-category's cells indexed by a
coordinate the construction already carries. The 2-category is the height-≤2 truncation; the ∞-category
removes the truncation — `ascent_unbounded` (`MuNuMirror.lean:50`: `∀ N, ∃ r, N < r.depth`) says the
height has no finite ceiling, which is precisely "cells at every dimension."

### 2. Forcing — weak composition is FORCED to be `Raw.fold`-up-to-coherence; level-0 is strict by `dhom_unique_pointwise`.

A quasi-category replaces "the composite of `f` and `g`" (a function, 1-category) with "an inner-horn
filler" (a composite *witnessed*, unique only up to higher cell). The calculus forces both ends. At
**level 0** the composite is strict and unique: `Raw.fold` is the unique structure-preserving map out of
the initial object (`raw_initial`, `dhom_unique_pointwise`), and its associativity `Raw.fold_slash`
(`Fold.lean:37`, 6/0 PURE) holds *on the nose* — this is the strict 1-category / nerve-of-an-ordinary-
category corner (every inner horn has a *unique* filler, the classical characterization of nerves of
1-categories). **Above level 0** the filler is unique only *up to a higher cell* — which is the coherence
tower carried as data, `operads.md`'s witness-carrying `FreeReduction` normal-form pattern. So weak
composition is *forced*: it is the fold, strict where `dhom_unique_pointwise` bites (level 0) and
coherent-up-to where the tower opens (the q=−1 re-entry). The inner-horn filler is not a new operation —
it is `Raw.fold` read with its coherence witnesses retained.

### 3. Spine — A∞ coherence = the associahedron = Catalan; ∞-groupoid = the all-invertible q=±1 pole.

- *A∞ coherence is `operads.md`'s associahedron, Catalan-counted.* The tower of associativity homotopies
  is the Stasheff associahedron `Kₙ`, whose face-count is **Catalan** — built ∅-axiom:
  `Catalan.catalan_recursion_3..7` (`Catalan.lean:63–92`, 17/0 PURE, `Cₙ₊₁ = Σᵢ Cᵢ·Cₙ₋ᵢ`, the
  free-binary-operad composition recurrence = the count of re-association paths). The ∞-category's
  composition-up-to-coherence is governed by *the same Catalan operad* `operads.md` already decomposed —
  no new coherence object, the count is a closed theorem.
- *∞-groupoid = space (the homotopy hypothesis) = the all-invertible q=±1 case.* When every cell is
  invertible, the coherence cells form the `LensIso` groupoid (`lensIso_refl/symm/trans`,
  `Unified.lean:46,51,56`) — `homotopy_theory.md`'s q=+1 converge pole (`golden_is_converge`), the
  involutive unimodular multiplier (`multiplier_unimodular`, `ResidueTag.lean:86`). An `(∞,1)`-category is
  the case where cells are invertible *above* dimension 1, leaving the q=±1 swap bit live only at
  dimension 1 (the `Mat2Bracket` antisymmetry `[A,B]=−[B,A]`, `bracket_antisymm`, `Mat2Bracket.lean:76`,
  10/0 PURE — the direction bit `homotopy_theory.md` used for fib/cofib). The homotopy hypothesis
  (∞-groupoids = spaces) is then the README's `q=+1` all-invertible reading of the same tower the q=−1
  pole leaves open.

### 4. Residue surfaced — the ∞ itself is the q=−1 never-closing coherence tower.

What makes an ∞-category *∞* rather than a strict 2- or 3-category is that the coherence tower **never
terminates into a strict composite**. This is exactly the calculus's q=−1 escape residue *re-entering as
its own operand*: `ResidueReentry.residue_perpetually_reenters` (`ResidueReentry.lean:85`, 14/0 PURE) /
`residue_reentry_never_closes` (`:63`) — the surplus of "compose-up-to" perpetually generates the next
coherence level, the cover never closing (delegating to `object1_not_surjective`,
`FlatOntologyClosure.lean:61`). This is the *same* iterated-residue operation `spectral_sequences.md`
named (the page recursion `E_{r+1}=H(E_r)`) and `homological_algebra.md`'s residue-taking — the
∞-category is that endofunctor's *orbit on the cell-dimension*. So the "∞" is not a transcendent target
above the finite (CLAUDE.md "Limit/infinity deified"); it is the finite signature of a never-closing
tower — `ascent_unbounded` names it by its finite generator, the tower is inhabited at every finite
height, never at "ω."

### The spine.

The ∞-category is the q=±1 spine displayed on the cell-tower: **q=+1** = all-invertible / ∞-groupoid /
truncated-to-finite-height / contractible — the converging pole that closes (`LensIso`,
`golden_is_converge`, `converge_residue_fixed`, `ResidueTag.lean:160,180`); **q=−1** = the tower never
closes / the genuinely-∞ coherence / non-invertible cells — the escaping pole
(`residue_perpetually_reenters`, `escape_residue_outside`, `ResidueTag.lean:133`, delegating to
`object1_not_surjective`). The same single spine `SYNTHESIS.md` §3 runs through Cantor/Gödel/φ/measure/
homology/spectral-sequences, now read on the cell-dimension tower of the 2-category of readings.

---

## VALIDATE — verdict

**EXTEND (by consolidation) + PREDICTION, with one new structural datum and one located break.** The
model held with no new axis; this ties `two_cells.md` + `operads.md` + `category_theory.md` +
`homotopy_theory.md` + `spectral_sequences.md` into one statement, with one genuinely NEW datum
(cell-dimension = the fold-height axis run up the 2-category, the coherence tower = that axis with the
q=−1 re-entry) and one recurring located break (the named quasi-category / nerve / Kan object absent).

- **EXTENDS, grounded ∅-axiom:** the **2-category** the ∞-structure extends (`two_cells.md`'s 1-cells
  `Lens.refines` + 2-cells `IsLensMorphism` / `view_factors_through_morphism`, all PURE); the
  **cell-dimension = fold-height axis** (`MuNuMirror.succ_not_idempotent` the growing pole,
  `ascent_unbounded` the no-ceiling, `Lambek.isPart_wf` the well-founded descent); **weak composition** =
  `Raw.fold`, strict at level 0 (`Raw.fold_slash`, `dhom_unique_pointwise` forcing uniqueness) and
  coherent above; **A∞ coherence** = `operads.md`'s associahedron, Catalan-counted
  (`catalan_recursion_n`, 17/0 PURE); **∞-groupoid = the all-invertible q=+1 pole** (`LensIso` groupoid,
  `multiplier_unimodular`, `golden_is_converge`); the **(∞,1) swap bit at dim 1** = `Mat2Bracket`
  antisymmetry; the **never-closing tower (the ∞)** = the iterated-residue re-entry
  (`residue_perpetually_reenters`, `residue_reentry_never_closes`, 14/0 PURE).

- **the nerve / simplicial leg is GROUNDED ∅-axiom (the in-repo simplicial-object machinery):** the
  Δ-complex `kSubset` (`SimplexBasis.lean:29`, 8/0 PURE) is the calculus's simplicial substrate (a
  `k`-simplex = a sorted `k`-subset), with face maps `eraseIdx` and the simplicial coboundary `δ`
  (`Delta.Core.deltaAt`/`delta`, `Delta/Core.lean:42,54`, 10/0 PURE; `dsq_zero_universal_delta4`,
  `V4Capstone.lean:41`, 5/0 PURE). This is the nerve's *simplicial-set* leg — a simplicial object with
  faces and the `δ²=0`/horn-degenerate structure — built; only the *named* `nerve`/`SimplicialSet` bundle
  is absent.

- **PREDICTION + located BREAK:** the calculus predicts the *form* of an ∞-category (the 2-category +
  the cell-dimension fold-height tower + Catalan coherence + the q=±1 invertibility pole) and the
  **named objects are ABSENT** — no `quasiCategory` / `InfinityCategory` / `Kan` (complex) /
  `innerHorn` / `nerve` / `SimplicialSet` declaration exists (grep-confirmed: zero matching files). Same
  shape as `homotopy_theory.md`'s missing `ModelCategory`, `operads.md`'s missing `Operad`/`A∞`/`E∞`
  bundle, and `homological_algebra.md`'s missing `Ext^n` object: every *structural mechanism* (the
  2-category, the fold-height tower, Catalan, the Δ-complex nerve substrate, the q=±1 pole) is built and
  PURE; only the *named bundle* welding them into a quasi-category is open.

- **the genuine remaining absence (consistent with the corpus's located breaks):** the **inner-horn
  filler as a colimit-up-to-homotopy** sits in the same un-built colimit/`q=−1` corner +
  ambient-space absence as `knots.md`/`homotopy_theory.md`'s isotopy quotient (`SYNTHESIS.md` §5.1, Side
  B). The strict-filler (level-0, unique) corner IS built (`dhom_unique_pointwise`, the nerve-of-a-1-
  category case); the *homotopy-coherent* filler welded into a `Kan`/quasi-category object is the open leg
  — `operads.md`'s missing homotopy-coherence tower object, restated for ∞-categories.

---

## Does this touch model v7.1? — NO new invariant; one frame observation + EXTEND.

The two invariants (character arrow, q=±1 residue) and the four axes absorb ∞-categories whole:

> **An ∞-category is the calculus's 2-category of readings (`two_cells.md`) with the FOLD-HEIGHT axis run
> up the CELL-DIMENSION — n-cells for all n = the coherence tower (assoc up to a 2-cell, up to a 3-cell,
> …) = `MuNuMirror.succ_not_idempotent`/`ascent_unbounded` applied to the cell-grading.** Weak
> composition = `Raw.fold` (strict at level 0 by `dhom_unique_pointwise`/`Raw.fold_slash`, coherent
> above); the inner-horn filler = the fold carried with coherence witnesses; A∞ coherence = the
> associahedron, Catalan-counted (`catalan_recursion_n`); ∞-groupoid = space = the all-invertible q=+1
> pole (`LensIso` groupoid, `multiplier_unimodular`); the ∞ (never-closing tower) = the iterated-residue
> re-entry (`residue_perpetually_reenters`, q=−1); the nerve = the Lens-view-as-simplicial-object, the
> in-repo Δ-complex `kSubset`/face/δ substrate. The located break is the **named
> `quasiCategory`/`InfinityCategory`/`Kan`/`nerve`/`SimplicialSet` bundle** — every leg built and PURE,
> the welded object absent (twin of `homotopy_theory.md`'s `ModelCategory` and `operads.md`'s `A∞`/`E∞`).

So model v7.1's interior is unchanged; the frame gains the observation that **the 2-category of readings
is the height-≤2 truncation of an ∞-category, and the fold-height axis IS the cell-dimension** — removing
the truncation (`ascent_unbounded`) gives cells at every dimension, with the coherence tower's never-
closing the q=−1 residue and the all-invertible case the q=+1 pole. The cell-dimension is a coordinate
the calculus's composition already carries (the same axis `category_theory.md`/`homological_algebra.md`
read as degree), not a new axis.

---

## Verified Lean anchors (file:line:theorem — all grep-confirmed + `tools/scan_axioms.py`-scanned this session, from repo root; all PURE)

| Leg | Anchor (file:line : name) | Purity (scanned) |
|---|---|---|
| **★ the 2-category base — 2-cells = naturality (the ∞-tower's height-≤2 truncation)** | `lean/E213/Lens/Compose/Morphism.lean:29 : IsLensMorphism`, `:37 : view_factors_through_morphism`, `:60 : refines_of_morphism` | PURE (Morphism **3/0**) |
| **1-cells = `Lens.refines` + composition/identity (2-of-3-style coherence)** | `lean/E213/Lens/LensCore.lean:90 : Lens.refines`, `:93 : refines_refl`, `:95 : refines_trans`; `:48 : Lens.equiv` | PURE (LensCore **11/0**) |
| **invertible cells = the `LensIso` groupoid (∞-groupoid pole) = kernel coincidence** | `lean/E213/Lens/Unified.lean:42 : LensIso`, `:46/51/56 : lensIso_refl/symm/trans`, `:64 : lensIso_iff_kernel_eq`, `:163 : LensImage.proj_val_eq_iff` | PURE (Unified **14/0**) |
| **★ cell-dimension = the fold-height axis run UP (n-cells for all n)** | `lean/E213/Theory/Raw/MuNuMirror.lean:80 : succ_not_idempotent` (depth strictly rises), `:50 : ascent_unbounded` (`∀N,∃r,N<r.depth`) | PURE (MuNuMirror **8/0**) |
| **well-founded descent of the tower (terminates at atoms)** | `lean/E213/Theory/Raw/Lambek.lean:199 : isPart_wf`, `:273 : no_infinite_descent` | PURE (Lambek **22/0**) |
| **★ the ∞ = the coherence tower never closes (residue re-enters as its own operand)** | `lean/E213/Lens/Foundations/ResidueReentry.lean:85 : residue_perpetually_reenters`, `:63 : residue_reentry_never_closes` | PURE (ResidueReentry **14/0**) |
| **weak composition = the fold; strict at level 0 (assoc on the nose)** | `lean/E213/Theory/Raw/Fold.lean:22 : Raw.fold`, `:30 : fold_a` (unit), `:37 : fold_slash` (assoc) | PURE (Fold **6/0**) |
| **horn filler unique-up-to-higher-cell: level-0 uniqueness (nerve-of-1-category)** | `lean/E213/Lens/Foundations/UniversalDistinguishing.lean:103 : dhom_unique_pointwise` | PURE (UniversalDist **6/0**) |
| **objects = folds out of the initial object (the catamorphism)** | `lean/E213/Lens/Foundations/SemanticAtom.lean:412 : raw_initial` | PURE (`raw_initial` individually; module 11/23) |
| **★ A∞ coherence = the associahedron = Catalan (free-binary-operad composition recurrence)** | `lean/E213/Lib/Math/Combinatorics/Catalan.lean:26 : catalan`, `:63–92 : catalan_recursion_3..7` (`Cₙ₊₁=Σ Cᵢ·Cₙ₋ᵢ`) | PURE (Catalan **17/0**) |
| **(∞,1) swap bit at dim 1 = q=±1 direction (antisymmetry)** | `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:76 : bracket_antisymm` (`[A,B]=−[B,A]`) | PURE (Mat2Bracket **10/0**) |
| **★ the nerve's simplicial substrate — k-simplex = sorted k-subset; faces** | `lean/E213/Lib/Math/Cohomology/Examples/SimplexBasis.lean:29 : kSubset` (`kSubset_*` decide-checked) | PURE (SimplexBasis **8/0**) |
| **the simplicial coboundary δ (face/eraseIdx) + δ²=0 (the Δ-complex nerve leg)** | `lean/E213/Lib/Math/Cohomology/Delta/Core.lean:42 : deltaAt` (`τ.eraseIdx i`), `:54 : delta`; `…/Delta/V4Capstone.lean:41 : dsq_zero_universal_delta4` | PURE (Delta.Core **10/0**, V4Capstone **5/0**) |
| **the q=±1 residue tag (escape/converge, ∓1; ∞-groupoid = converge pole)** | `lean/E213/Lib/Math/Foundations/ResidueTag.lean:73 : ResidueTag`, `:86 : multiplier_unimodular`, `:133 : escape_residue_outside`, `:160 : converge_residue_fixed`, `:180 : golden_is_converge`, `:228 : residue_tag_two_poles` | PURE (ResidueTag **55/0**) |
| escape residue's kernel (the tower's q=−1 non-closure delegates here) | `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective` | PURE (prior-scan) |

**Fresh scan tallies this session (`tools/scan_axioms.py`, repo root, `E213.` prefix):**
`Lens.Compose.Morphism` **3/0**; `Lens.LensCore` **11/0**; `Lens.Unified` **14/0**;
`Theory.Raw.MuNuMirror` **8/0**; `Theory.Raw.Lambek` **22/0**; `Lens.Foundations.ResidueReentry` **14/0**;
`Theory.Raw.Fold` **6/0**; `Lens.Foundations.UniversalDistinguishing` **6/0**
(`dhom_unique_pointwise` PURE); `Lens.Foundations.SemanticAtom` module **11/23** but `raw_initial`
**individually PURE**; `Combinatorics.Catalan` **17/0**; `Mat2.Mat2Bracket` **10/0**;
`Cohomology.Examples.SimplexBasis` **8/0**; `Cohomology.Delta.Core` **10/0**;
`Cohomology.Delta.V4Capstone` **5/0**; `Foundations.ResidueTag` **55/0**. All load-bearing anchors PURE.

---

## Dropped / flagged (honest — NOT cited as anchors)

- **The named `quasiCategory` / `quasiCategory` / `InfinityCategory` / `Kan` (complex) / `innerHorn` /
  `nerve` / `SimplicialSet` / `KanComplex` object — ABSENT, predicted-not-built.** Grep over
  `lean/E213` (case-insensitive) for `nerve`/`quasicategory`/`infinitycategory`/`innerhorn`/`kancomplex`/
  `simplicialset`/`deltacomplex` returns **zero matches**. The `\bKan\b`/`\bhorn\b`/`simplex` token hits
  are unrelated (physics `Simplex`, `HorizonInformation`, `Kan`-as-substring). So the
  ∞-category/quasi-category/nerve bundle is genuinely absent — only its legs (2-category, fold-height
  tower, Catalan, the Δ-complex simplicial substrate, the q=±1 pole) are built. This is the precise
  located break, the twin of `homotopy_theory.md`'s missing `ModelCategory`/`πₙ` and `operads.md`'s
  missing `A∞`/`E∞`/`MayRecognition` objects.

- **The genuine inner-horn filler as a homotopy-coherent (colimit-up-to-homotopy) operation — not
  built.** Grounded only at the leg level: `Raw.fold`/`Raw.fold_slash` (the strict level-0 composite) +
  `dhom_unique_pointwise` (level-0 uniqueness = nerve-of-a-1-category, every inner horn uniquely filled)
  + the Catalan coherence count + the `ResidueReentry` non-closure (the q=−1 tower). The
  homotopy-coherent filler welded into a `Kan`/quasi-category object is the same un-built colimit/`q=−1`
  corner + ambient-space absence as `homotopy_theory.md`/`knots.md` Side B (`SYNTHESIS.md` §5.1) — a
  theorem-grade absence, not a missing 213 primitive.

- **The named `nerve N(C)` functor / `SimplicialSet` type — absent; only the simplicial OBJECT
  machinery is built.** The Δ-complex `kSubset`/`deltaAt`/`delta`/`dsq_zero_universal_delta4` is a genuine
  simplicial object with faces and `δ²=0`, but there is no `nerve : Category → SimplicialSet` functor and
  no `SimplicialSet`/face-degeneracy-with-simplicial-identities bundle. The simplicial *substrate* is
  built; the named nerve construction is the open leg.

- **The homotopy hypothesis (∞-groupoids ≅ spaces) as a stated equivalence — prose-only.** The
  all-invertible `LensIso` groupoid (q=+1) is the right analogue, but there is no `Space`/`∞-groupoid`
  equivalence object — the same ambient-space absence `two_cells.md` Shape 3 / `homotopy_theory.md`'s
  homotopy quotient located.

### Verified buildable witness (named, not asserted)
A **"strict ∞-category collapses to a 1-category"** truncation theorem is buildable ∅-axiom from existing
PURE legs: state that when every coherence cell is *strictly* an identity (the `dhom_unique_pointwise`
level-0 corner), the cell-tower collapses — i.e. `succ_not_idempotent`'s strict-ascent is replaced by the
idempotent `clo`-style closure, so the height-≤n truncation is the nerve of a 1-category with *uniquely*
filled inner horns (`dhom_unique_pointwise`). Both halves are already closed PURE
(`dhom_unique_pointwise` 6/0, `Raw.fold_slash` 6/0); the witness is the named bridge theorem
`unique_filler_iff_strict_truncation` — the strict/coherent dichotomy is exactly the q=+1/q=−1 split
(`golden_is_converge` vs `residue_perpetually_reenters`). Not built this session; named as the concrete
promotion target, the ∞-category twin of `operads.md`'s `fold_split = catalan_convolution`.

### Cross-frame
`two_cells.md` (KEY — the 2-category of readings = the height-≤2 truncation; `view_factors_through_morphism`,
`IsLensMorphism`, `dhom_unique_pointwise`); `operads.md` (A∞/associahedron coherence = Catalan
`catalan_recursion_n`, the multicategory above the 2-category — ∞-categories are its
cell-dimension-graded twin); `category_theory.md` (`raw_initial`/`Lens.view = Raw.fold` = initial object +
catamorphism); `homotopy_theory.md` (∞-groupoid = space = the q=+1 all-invertible pole; the homotopy
quotient = the located break recurring); `spectral_sequences.md`/`homological_algebra.md`
(`residue_perpetually_reenters` = the residue operation iterated up the cell-dimension);
`golden_ratio.md`/SYNTHESIS `golden_is_converge` (∞-groupoid / truncation = the q=+1 converging pole).
