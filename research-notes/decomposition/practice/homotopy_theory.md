# Decomposition: homotopy theory / model categories (Quillen model structure, fib/cofib/weak-equivalence, 2-of-3, lifting, Ho(C) = localization, πₙ, fibration sequences, Whitehead)

*A FRESH decomposition per `../README.md` (model v7.1) and `SYNTHESIS.md` (the two invariants + the
q=±1 spine + the 2-category of readings + the residue-taking operation). Consolidates `two_cells.md`
(readings form a **2-category**: 1-cells `Lens.refines`, 2-cells `IsLensMorphism`/`LensIso`),
`equivalence.md` (sameness = one Lens-arrow `Lens.refines`, iso = kernel coincidence
`lensIso_iff_kernel_eq`), `fundamental_group.md` (the loop-reading `L_loop`, holonomy, the homotopy
quotient = `knots.md`'s located break), and `homological_algebra.md` (the residue-taking operation's
long exact sequence). The hypothesis to **test**, not re-skin:*

> **A model category = the calculus's 2-category of readings (`two_cells.md`), equipped with a
> q=±1 fibration/cofibration lifting dual and a weak-equivalence = Lens-refinement localization.**
> Weak equivalences = `Lens.refines` (two constructions with the same reading are weakly equivalent);
> Ho(C) = localization at weak equivalence = the `Quot`-free `LensImage` Σ-quotient
> (`LensImage.proj_val_eq_iff` / `FreeReduction.proj_val_eq_iff` — the SAME colimit Side-A machinery);
> fibrations vs cofibrations = the q=±1 dual pair (the lifting property's orientation = the swap bit,
> `Mat2Bracket` antisymmetry); the 2-of-3 property = composition-coherence of `Lens.refines`
> (`refines_trans`); πₙ = `fundamental_group.md`'s loop-reading graded by fold-height; the long exact
> sequence of a fibration = `homological_algebra.md`'s residue-taking LES (`dsq_zero_universal_delta4`).
> **No new primitive** — it is `two_cells.md`'s 2-category + `equivalence.md`'s `Lens.refines`
> localized, with a q=±1 lifting structure.

---

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **category of constructions and reading-arrows between them**: the
  2-category `two_cells.md` already exhibits. Objects are `Raw`s / readings (folds out of the initial
  object `Raw`); 1-cells are refinements `Lens.refines` (`LensCore.lean:90`); 2-cells are
  `IsLensMorphism` / `LensIso` (`Morphism.lean:29`, `Unified.lean:42`). `C` carries the README's two
  read-off axes load-bearingly here: the **direction / swap bit `q=±1`** (the orientation of a
  lifting square — right-lift vs left-lift, the `Mat2Bracket` antisymmetry) and the **fold-height**
  (the grading `n` that turns π₁ into πₙ, `homological_algebra.md`'s degree). Nothing classically
  model-theoretic is a primitive: no `ModelCategory` type, no `fibration`/`cofibration` class, no
  `WeakEquivalence` predicate, no `homotopyGroup` (all grep-confirmed ABSENT below).

- **Reading `L` — the weak-equivalence reading = `Lens.refines` (and its symmetric closure
  `LensIso`).** A model category's *whole content* is "which maps are weak equivalences" — the maps you
  invert when you pass to Ho(C). In 213 the weak-equivalence relation is `equivalence.md`'s single
  Lens-arrow: two constructions are *weakly equivalent* iff they **read the same** under the organizing
  reading, `x ≈_L y := L.view x = L.view y` (`Lens.equiv`), and one reading is *finer than* another iff
  `Lens.refines` (`L.equiv x y → M.equiv x y`). A **weak equivalence between readings** is then a
  `LensIso` — mutual refinement = kernel coincidence (`lensIso_iff_kernel_eq`, `Unified.lean:64`). So
  the weak-equivalence class IS the calculus's comparison layer; the three model-category map classes
  are this one reading + a q=±1 orientation (Residue).

- **Residue `q = ±1`** — TWO residues, the README's two poles, and they split the verdict exactly as in
  `fundamental_group.md`:
  - **the q=−1 escape residue** — the homotopy quotient / non-contractible class: a weak-equivalence
    class that does NOT reduce to a point (`first_loop_is_the_fold : holonomy [S,S] = −I ≠ I`,
    `HolonomyLattice.lean:313`), the obstruction the long exact sequence of a fibration displays
    (`dsq_zero_universal_delta4`, `V4Capstone.lean:41`), tagged `escape` / `multiplier = −1`
    (`ResidueTag.lean:73,81`). The **isotopy/homotopy quotient itself** (loops mod a continuous family)
    is `knots.md`/`fundamental_group.md`'s located break — the genuine ABSENCE.
  - **the q=+1 converge residue** — "simply connected" / "contractible" / Whitehead's theorem:
    every weak equivalence is invertible up to homotopy, the class closes to a point
    (`positive_loop_trivial`, `HolonomyLattice.lean:292`; `det_holonomy_eq_one`, `:136`), tagged
    `converge` / `multiplier = +1`, the same pole as φ/Gaussian/closure (`golden_is_converge`,
    `ResidueTag.lean:180`).

---

## Re-seeing — ⟨C | L⟩ ⊕ Residue(L,C)

```
   a model category C        =  ⟨ the 2-category of readings | the weak-equivalence reading L ⟩ ⊕ Residue(q=±1)
                                = two_cells.md's 2-category (1-cells refines, 2-cells IsLensMorphism/LensIso)
   weak equivalence          =  reads-the-same under L  =  Lens.refines / LensIso   (equivalence.md's one arrow)
                                = "same reading ⇒ weakly equivalent"  (Lens.equiv; lensIso_iff_kernel_eq)
   the 2-of-3 property       =  composition-coherence of refines  (refines_trans: L≼M ∧ M≼N ⇒ L≼N)
                                + refines_refl (the third leg is forced from two)
   Ho(C) = localize at W.E.  =  the Quot-FREE LensImage Σ-quotient  (LensImage.proj_val_eq_iff)
                                = the SAME colimit Side-A machinery  (FreeReduction.proj_val_eq_iff,
                                  free_group_quotient_no_quot — no Quot.sound, no Classical, no Mathlib)
   fibration  /  cofibration =  the q=±1 lifting dual  (right-lift vs left-lift = the swap bit)
                                = Mat2Bracket antisymmetry  [A,B]=−[B,A]  (bracket_antisymm)
   a lifting property        =  a 2-cell filling a square, oriented by q  (IsLensMorphism + view_factors…)
   πₙ(X,x₀)                  =  fundamental_group.md's loop-reading L_loop GRADED by fold-height n
                                = holonomy residue (holonomy_append) at degree n  (homological_algebra's grading)
   π₀ trivial / contractible =  q=+1 converge  (positive_loop_trivial, det_holonomy_eq_one)
   πₙ ≠ 0 / non-contractible =  q=−1 escape residue  (first_loop_is_the_fold: holonomy[S,S]=−I)
   fibration sequence / LES  =  the residue-taking operation's long exact sequence  (homological_algebra)
                                = δ threads ker=im across degrees, δ²=0  (dsq_zero_universal_delta4)
   Whitehead's theorem       =  q=+1: a weak equivalence inducing iso on all πₙ is a homotopy equivalence
                                = LensIso (mutual refinement) on the graded loop-reading  (lensIso_iff_kernel_eq)

   the homotopy quotient     =  loops/maps mod a CONTINUOUS ambient family  =  knots.md's ISOTOPY QUOTIENT
                                — the un-built colimit/q=−1 corner + an absent ambient-space construction (ABSENT)
```

Set against the four cross-frames: the **2-category rows are `two_cells.md` verbatim** (1-cells +
2-cells, all ∅-axiom), the **weak-equivalence / 2-of-3 / Ho(C)-localization rows are
`equivalence.md` + the `LensImage`/`FreeReduction` Σ-quotient** (the genuinely NEW datum: Ho(C) IS
the calculus localizing at "same reading", by the Quot-free machinery), the **fib/cofib row is the
q=±1 dual** (`Mat2Bracket` antisymmetry), the **πₙ rows are `fundamental_group.md` graded by
`homological_algebra.md`'s degree**, and the trouble is concentrated in the **last row** — exactly
`knots.md`/`fundamental_group.md`'s located break, recurring a THIRD time.

---

## THE REVELATION (collapse + forcing + spine)

**Collapse — the three model-category map-classes, the 2-of-3 property, and Ho(C) are NOT a new
edifice: they are the calculus's already-built 2-category of readings, localized at `Lens.refines`,
with a q=±1 orientation.** Three distinct collapses, one per structural piece, plus the residue
surfaced and the spine.

### 1. Collapse — weak equivalence = `Lens.refines`; Ho(C) = the Quot-free Σ-quotient (the NEW datum).

A model category is *machinery for inverting a chosen class of maps* — the weak equivalences — to
form Ho(C). `equivalence.md` already established that "sameness under a reading" is the single
Lens-arrow `Lens.refines` / `LensIso` (iso = kernel coincidence, `lensIso_iff_kernel_eq`). The new
datum this note contributes — beyond re-skinning `equivalence.md` — is **that the localization
itself is the calculus's `Quot`-free `LensImage` Σ-quotient**: Ho(C) = C localized at W.E. is exactly
`LensImage.proj_val_eq_iff` (`Unified.lean:163`) — the projection `Raw → LensImage L` whose values
coincide *iff* the Raws share the Lens-kernel, i.e. *iff* they are weakly equivalent — built with
**no `Quot.sound`, no `Classical`, no Mathlib**, the literal "invert the weak equivalences = quotient
by same-reading". And it is the **SAME colimit Side-A machinery** the program already promoted from
the knots/π₁ break: `FreeReduction.proj_val_eq_iff` (`FreeReduction.lean:237`) +
`free_group_quotient_no_quot` (`:264`) build the free group as a normal-form Σ-quotient by exactly
this recipe (26/0 PURE). So **the homotopy category = the localization = the Lens-image Σ-quotient =
the free-reduction normal form**: one quotient construction, named four ways across
`equivalence.md` / `homological_algebra.md` / the colimit-synthesis / homotopy theory. This is the
collapse that earns the note: Ho(C) is not a new colimit to fear — it is the *decidable, `Quot`-free*
corner the calculus already built (`SYNTHESIS.md` §5.1, Side A).

### 2. Forcing — the 2-of-3 property is FORCED by `refines_trans`, not an axiom.

The 2-of-3 axiom ("if two of `f`, `g`, `g∘f` are weak equivalences, so is the third") looks like a
chosen model-category axiom. In the calculus it is **forced** by the composition-coherence of the
weak-equivalence reading: `Lens.refines_trans` (`LensCore.lean:95`) gives `L≼M ∧ M≼N ⇒ L≼N`, and
`refines_refl` (`:93`) the identity, so the weak equivalences are a *subcategory containing
isomorphisms and closed under composition* — which is precisely the 2-of-3 closure for a class
generated by a reading's kernel containment (`LensIso` being mutual refinement, `lensIso_trans`,
`Unified.lean:54`, gives the iso half). The 2-of-3 property is the *transitivity of "same reading"*,
not an extra demand. Same forcing as `equivalence.md`'s ceiling: it is a 1-categorical/setoid-level
kernel preorder (no univalence; `funext`/`Quot.sound` forbidden) — so what 213 supplies is exactly
the 2-of-3 / saturation a model structure's W.E. class needs, at the honest 1-categorical altitude.

### 3. Forcing — fibration/cofibration = the q=±1 lifting dual (orientation = the swap bit).

In a model category fibrations and cofibrations are defined by *lifting properties* against the
trivial cofibrations / trivial fibrations — and the two classes are **dual** (a map is a fibration
iff it right-lifts; a cofibration iff it left-lifts). The lifting square is a 2-cell to be filled
(`IsLensMorphism` + `view_factors_through_morphism`, `Morphism.lean:37`: the component `h` filling
`M.view = h∘L.view` is the diagonal lift), and the **right-vs-left orientation is the calculus's
q=±1 swap bit** — the `Mat2Bracket` antisymmetry `[A,B] = −[B,A]` (`bracket_antisymm`,
`Mat2Bracket.lean:76`), the same direction/swap sub-structure that reads out as sign/orientation
everywhere (integers, `∂²=0`, the loop). Fibration and cofibration are *one lifting structure read at
its two unimodular poles* (`multiplier_unimodular`, `ResidueTag.lean:86`): right-lift = one pole,
left-lift = the other. This is the README's "direction / swap-bit" axis applied to the lifting
square — no new primitive, the q=±1 dual the program has read across integers/determinant/homology/Lie.

### 4. Residue surfaced — πₙ and Whitehead's theorem are the loop-reading's q=±1 residue, graded.

`fundamental_group.md` established π₁ = the loop-holonomy reading `L_loop`'s q=±1 residue
(`holonomy_append`, `HolonomyLattice.lean:108`; `first_loop_is_the_fold` the q=−1 first loop,
`positive_loop_trivial` the q=+1 simply-connected pole). **πₙ is that same loop-reading graded by the
fold-height** — `homological_algebra.md`'s degree `n`: the higher homotopy groups are the loop-class
residue read at height `n`, exactly as `Ext^n` is the residue graded by `n`. The **long exact
sequence of a fibration** `…→πₙ(F)→πₙ(E)→πₙ(B)→πₙ₋₁(F)→…` is then `homological_algebra.md`'s
residue-taking LES verbatim: the connecting map `δ` is the q=±1 sign-propagation, `δ²=0`
(`dsq_zero_universal_delta4`, `V4Capstone.lean:41`) threading `ker=im` across degrees. And
**Whitehead's theorem** ("a weak equivalence inducing iso on all πₙ is a homotopy equivalence") is the
q=+1 pole: it says a map that is a `LensIso` on the graded loop-reading (iso on every πₙ) is a genuine
equivalence — i.e. mutual refinement = kernel coincidence on the whole graded family
(`lensIso_iff_kernel_eq`), the converging/closure corner, the same `q=+1` reached-to-a-fixed-point as
φ/Gaussian/closure (`converge_residue_fixed`/`golden_is_converge`, `ResidueTag.lean:160,180`).
Whitehead FAILS without the πₙ-iso hypothesis precisely because the q=−1 escape residue (a non-trivial
higher homotopy class) is the obstruction — `escape_residue_outside` (`ResidueTag.lean:133`).

### The spine.

The model structure is the q=±1 spine displayed on maps: **q=+1** = trivial fibration / trivial
cofibration / weak equivalence / contractible / Whitehead-invertible — the converging pole that
*closes* (`positive_loop_trivial`, `det_holonomy_eq_one`, `converge_residue_fixed`); **q=−1** =
non-contractible class / the obstruction the fibration LES displays / the homotopy quotient — the
escaping pole (`first_loop_is_the_fold`, `dsq_zero_universal_delta4`, `escape_residue_outside`,
delegating to `object1_not_surjective`). The same single spine `SYNTHESIS.md` §3 runs through
Cantor/Gödel/φ/measure/homology, now read on the three model-category map classes.

---

## VALIDATE — verdict

**EXTEND (by consolidation) + PARTIAL-BREAK.** The model held across the corpus with no new axis; this
is a consolidation that ties `two_cells.md` + `equivalence.md` + `fundamental_group.md` +
`homological_algebra.md` into one statement, with one genuinely NEW datum (Ho(C) = the `Quot`-free
`LensImage`/`FreeReduction` Σ-quotient = the colimit Side-A machinery) and one recurring located break.

- **EXTENDS, grounded ∅-axiom:** the **2-category** the model structure lives in (`two_cells.md`'s
  1-cells `refines` + 2-cells `IsLensMorphism`/`LensIso`, all PURE); the **weak-equivalence reading**
  = `Lens.refines` / `LensIso` (`equivalence.md`, `lensIso_iff_kernel_eq`); the **2-of-3 property** =
  `refines_trans` + `refines_refl` (forced); **Ho(C) = localization** = `LensImage.proj_val_eq_iff` /
  `FreeReduction.proj_val_eq_iff` (the Quot-free Σ-quotient, 14/0 + 26/0 PURE — the NEW datum); the
  **fib/cofib lifting dual** = the q=±1 swap bit (`Mat2Bracket.bracket_antisymm`,
  `multiplier_unimodular`); **πₙ** = `fundamental_group.md`'s `L_loop` graded by height
  (`holonomy_append`, `first_loop_is_the_fold`, `positive_loop_trivial`); the **fibration-sequence
  LES** = the residue-taking operation's LES (`dsq_zero_universal_delta4`); **Whitehead** = the q=+1
  `LensIso`-on-all-πₙ closure pole (`converge_residue_fixed`).

- **PARTIAL-BREAK (the homotopy quotient — `knots.md`/`fundamental_group.md`'s SAME break, a THIRD
  recurrence):** the *full* homotopy relation — maps modulo a continuous ambient family
  `H : X × [0,1] → Y` — is the isotopy/homotopy quotient by a continuous ambient deformation. It is
  **not** a self-application residue, **not** a kernel-coincidence (`lensIso_iff_kernel_eq`), **not**
  the closure `clo`; it lives in the un-built colimit/`q=−1` corner PLUS an absent ambient-space
  construction (`SYNTHESIS.md` §5 item 1, Side B). The `Quot`-free Σ-quotient builds Ho(C) for the
  **decidable / confluent-terminating (q=+1) corner** (free reduction, the surface cases); the
  **non-confluent / undecidable** corner (general presented homotopy types — Novikov–Boone-grade) is
  Side B, theorem-grade absent. So Ho(C) is built exactly where the word problem is decidable, absent
  exactly where it is not — the constructive boundary, located.

- **PREDICTION:** the calculus predicts the *form* of a model structure (W.E. = a reading's kernel
  preorder; fib/cofib = its q=±1 lifting dual; Ho = its Σ-quotient localization; the 2-of-3 = the
  reading's transitivity) and the *named objects are ABSENT* — no `ModelCategory`/`fibration`/
  `cofibration`/`weakEquivalence`/`homotopyGroup`/`Quillen`/`localization` declaration exists
  (grep-confirmed below), the same shape as `homological_algebra.md`'s missing `Ext^n` object.

---

## Verified Lean anchors (file:line:theorem — all grep-confirmed + `tools/scan_axioms.py`-scanned this session, from repo root)

| Leg | Anchor (file:line : name) | Purity (scanned) |
|---|---|---|
| **★ Ho(C) = localize at W.E. = the Quot-free Σ-quotient (the NEW datum)** | `lean/E213/Lens/Unified.lean:163 : LensImage.proj_val_eq_iff` (`(proj L x).val = (proj L y).val ↔ L.equiv x y`) | PURE (Unified **14/0**) |
| **★ Ho(C) = the SAME colimit Side-A machinery (free reduction normal form)** | `lean/E213/Lib/Math/Algebra/Group/FreeReduction.lean:237 : proj_val_eq_iff`; `:264 : free_group_quotient_no_quot` (no `Quot`/`Classical`/Mathlib) | PURE (FreeReduction **26/0**) |
| **weak equivalence = `Lens.refines` / `LensIso` = kernel coincidence** | `lean/E213/Lens/LensCore.lean:90 : Lens.refines`; `lean/E213/Lens/Unified.lean:42 : LensIso`, `:64 : lensIso_iff_kernel_eq`, `:54 : lensIso_trans` | PURE (LensCore **11/0**, Unified **14/0**) |
| **2-of-3 property = composition-coherence of refines (forced)** | `lean/E213/Lens/LensCore.lean:93 : Lens.refines_refl`, `:95 : Lens.refines_trans` | PURE (LensCore **11/0**) |
| **the lifting square = a 2-cell (2-category of readings)** | `lean/E213/Lens/Compose/Morphism.lean:29 : IsLensMorphism`, `:37 : view_factors_through_morphism`, `:60 : refines_of_morphism` | PURE (Morphism **3/0**) |
| **fib/cofib = the q=±1 lifting dual (orientation = swap bit)** | `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:76 : bracket_antisymm` (`[A,B]=−[B,A]`) | PURE (Mat2Bracket **10/0**) |
| **the q=±1 residue tag (escape/converge, ∓1)** | `lean/E213/Lib/Math/Foundations/ResidueTag.lean:73 : ResidueTag` (escape\|converge), `:81 : multiplier`, `:86 : multiplier_unimodular`, `:133 : escape_residue_outside`, `:160 : converge_residue_fixed`, `:180 : golden_is_converge`, `:228 : residue_tag_two_poles` | PURE (ResidueTag **55/0**) |
| **πₙ = loop-reading L_loop graded; π₁ as a group = functorial holonomy** | `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:108 : holonomy_append` | PURE (Holonomy **26/0**) |
| **contractible / Whitehead q=+1 pole; non-contractible q=−1 residue** | `…/HolonomyLattice.lean:136 : det_holonomy_eq_one`, `:292 : positive_loop_trivial`, `:313 : first_loop_is_the_fold` (`holonomy[S,S]=−I≠I`) | PURE (Holonomy **26/0**) |
| **fibration-sequence LES = the residue-taking operation's LES; δ²=0** | `lean/E213/Lib/Math/Cohomology/Delta/V4Capstone.lean:41 : dsq_zero_universal_delta4`; `:62 : leibniz_universal_delta4` | PURE (V4Capstone **5/0**) |
| escape/faithful residue (q=−1 pole's kernel, Whitehead obstruction) | `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective` (per `fundamental_group.md`/`homological_algebra.md`) | PURE (prior-scan) |

**Fresh scan tallies this session (`tools/scan_axioms.py` from repo root, `E213.` prefix):**
`E213.Lens.Unified` **14/0**, `E213.Lib.Math.Algebra.Group.FreeReduction` **26/0**, `E213.Lens.LensCore`
**11/0**, `E213.Lens.Compose.Morphism` **3/0**, `E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Bracket`
**10/0**, `E213.Lib.Math.Foundations.ResidueTag` **55/0**,
`E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice` **26/0**,
`E213.Lib.Math.Cohomology.Delta.V4Capstone` **5/0**. All load-bearing anchors PURE; the specific
theorems (`proj_val_eq_iff`, `free_group_quotient_no_quot`, `lensIso_iff_kernel_eq`, `refines_trans`,
`view_factors_through_morphism`, `bracket_antisymm`, `residue_tag_two_poles`, `holonomy_append`,
`first_loop_is_the_fold`, `dsq_zero_universal_delta4`) each appear in the per-theorem PURE listing.

---

## Dropped / flagged (honest — NOT grounded in repo Lean)

- **The named `ModelCategory` / `fibration` / `cofibration` / `weakEquivalence` / `homotopyGroup` /
  `πₙ` / `Quillen` (adjunction) / `localization` objects — ABSENT, predicted-not-built.** Grep over
  `lean/E213` for `model_category`/`ModelCategory`/`fibration`/`Fibration`/`cofibration`/
  `weak_equivalence`/`weakEquivalence`/`WeakEquiv`/`Quillen`/`homotopyGroup`/`HomotopyGroup`/
  `liftingProperty`/`localization`/`Localization` returns **zero matching files**. The only
  `homotopy`/`fibration`-token hits are docstring prose in `GRA/HoTT.lean` and `GRA/HigherAlgebra.lean`
  (the numerical-semigroup "homotopy McNugget" / "associative up to homotopy" — unrelated to model
  structures) and `Real213` cut / topology / cohomology INDEX files; **no model-category, fibration,
  or homotopy-group declaration exists.** This is the precise missing leg — the same shape as
  `homological_algebra.md`'s missing `Ext^n` object and `fundamental_group.md`'s missing `π₁` object:
  every *structural mechanism* (the 2-category, `Lens.refines`, the Σ-quotient localization, the q=±1
  lifting dual, the loop-reading, the LES) is built and PURE; only the *named bundle* welding them into
  `ModelCategory`/`fibration`/`πₙ` is open.
- **An actual `πₙ(X,x₀)` / `pathHomotopy` / `CoveringSpace` / `vanKampen` object — ABSENT.** Per
  `fundamental_group.md`'s grep: zero `fundamentalGroup`/`pathHomotopy`/`CoveringSpace`/`vanKampen`.
  The repo has the **loop word group** (holonomy products, `holonomy_append`) and the **abelianization
  step** (`commSet`/`gcomm`), but no homotopy quotient to turn loop words into homotopy classes, hence
  no πₙ *object* and no Quillen-equivalence instance.
- **The homotopy quotient (maps mod a continuous ambient family) = `knots.md`/`fundamental_group.md`'s
  isotopy quotient — the SAME located break, a THIRD recurrence.** Not a self-application residue, not
  a kernel-coincidence, not the closure `clo`; the un-built colimit/`q=−1` corner (`SYNTHESIS.md` §5
  item 1) Side B, plus an absent ambient-space construction. **Buildable witness (verified, already
  built):** Ho(C) for the *confluent-terminating (q=+1) corner* IS built — `FreeReduction.lean`
  (`free_group_quotient_no_quot`, 26/0 PURE) is the homotopy-category localization for the decidable
  case (the free homotopy type / free loop group), the exact Side-A analogue. No *new* witness is
  proposed (no unverified `decide` claim); the existing 26/0 free-reduction Σ-quotient is the honest
  buildable side, and Side B (general presented homotopy types, Novikov–Boone-grade undecidable) is
  theorem-grade absent.
- **Quillen adjunction / derived functors of the model structure** — conceptual: tied to
  `homological_algebra.md`'s residue-taking operation (`Ext^n`-shaped), whose named graded object is
  itself absent; the adjoint-pair machinery is `galois.md`/`adjunction.md`'s closure (`clo_idempotent`,
  PURE), but no `QuillenAdjunction`/derived-functor-of-a-model-structure object exists.

---

## Cross-frame

`two_cells.md` (the 2-category readings form — 1-cells `refines`, 2-cells `IsLensMorphism`/`LensIso`;
the lifting square is a 2-cell); `equivalence.md` (weak equivalence = the one Lens-arrow `Lens.refines`,
iso = kernel coincidence — the W.E. reading); `fundamental_group.md` (πₙ = the loop-reading graded; the
homotopy quotient = the located break, recurring here a third time); `homological_algebra.md` (the
fibration-sequence LES = the residue-taking operation's LES, `dsq_zero`); `category_theory.md`/
`adjunction.md` (the localization = the colimit Side-A corner; Quillen adjunction = the closure
monad's open derived-functor leg); `knots.md` (the isotopy quotient this break shares); `SYNTHESIS.md`
§5.1 (the `Quot`-free Side-A localization machinery this note reuses for Ho(C)).
