# Decomposition: derived / triangulated categories (D(A) = chain complexes localized at quasi-isos, the shift [1], distinguished triangles X→Y→Z→X[1], the octahedral axiom, the long exact sequence of a triangle, derived functors Lf/Rf)

*A FRESH decomposition per `../README.md` (model v7.1) and `SYNTHESIS.md` (the two invariants, the
q=±1 spine, the residue-taking operation §2, the two reflexive halves: homological algebra = `Residue(L,C)`,
motives = `⟨C|L⟩`). Consolidates `homological_algebra.md` (KEY — the residue operation, `Ext`/`Tor`, the
connecting `δ`/LES) and `homotopy_theory.md` (KEY — Ho(C) = the `Quot`-free `LensImage`/`FreeReduction`
localization), with `spectral_sequences.md` (the residue operation ITERATED), `motives.md`/`homology.md`.
The hypothesis to **test**, not re-skin:*

> **A derived category is the calculus's `Residue(L,C)`-operation's NATURAL HOME — `homological_algebra.md`'s
> chain complexes (the resolution-dial objects) living inside `homotopy_theory.md`'s `Quot`-free
> localization.** D(A) = chain-complexes-localized-at-quasi-isomorphisms = the SAME Quot-free
> `LensImage`/`FreeReduction` Σ-quotient `homotopy_theory.md` identified as Ho(C) — a quasi-iso = a weak
> equivalence = `Lens.refines`. The shift [1] = the fold-height grading shifted by one, with X[1]'s
> differential-sign-flip the q=±1 swap bit (`dsq_zero`'s orientation; [2] ≅ sign-identity = the q=±1
> involution `multiplier_unimodular`). A distinguished triangle X→Y→Z→X[1] = `homological_algebra.md`'s LES
> packaged into one rotatable object (the connecting `δ` made an arrow). Derived functors Lf/Rf = the
> resolution-dial lift (`Ext`/`Tor` in their natural category). The octahedral axiom = a coherence (2-cell
> associativity of the residue composition). **No new primitive** — it is the residue operation
> (`homological_algebra.md`) located in the localized category (`homotopy_theory.md`), the home of the
> `Residue(L,C)` half.

---

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **category of chain complexes and chain maps**: `homological_algebra.md`'s `C`
  (the graded simplex/cochain nesting `… → Cᵏ → Cᵏ⁺¹ → …` with the coboundary `delta` between adjacent
  degrees, `Cochain n k := Fin (binom n k) → Bool`, `Cohomology/Cochain/Core.lean:22`; `delta`,
  `Delta/Core.lean:54`) packaged as the *objects* of a category, with the reading-arrows of
  `homotopy_theory.md`'s 2-category (`two_cells.md`'s 1-cells `Lens.refines`, 2-cells `IsLensMorphism`)
  between them. `C` carries the README's two read-off axes load-bearingly: the **fold-height** (the degree
  `k`/`n` AND the shift index, the resolution coordinate) and the **direction / swap bit q=±1** (the
  alternating differential sign, the orientation `dsq_zero` carries). Nothing classically derived-categorical
  is a primitive: no `DerivedCategory`/`triangulated`/`shiftFunctor`/`distinguishedTriangle`/`quasiIso`
  type (all grep-confirmed ABSENT below).

- **Reading `L` — the quasi-isomorphism = weak-equivalence reading = `Lens.refines`, localized.** A derived
  category's *whole content* is "invert the quasi-isomorphisms" — exactly `homotopy_theory.md`'s
  weak-equivalence reading. A **quasi-isomorphism** is a chain map inducing an isomorphism on all cohomology
  `Hⁿ` — i.e. two complexes that *read the same* under the residue-taking reading `Hⁿ = ker δ/im δ`. In 213
  this is `equivalence.md`'s single Lens-arrow `x ≈_L y := L.view x = L.view y` (`Lens.refines`,
  `LensCore.lean:90`) with `L` = "take cohomology" (the residue reading of `homological_algebra.md`); mutual
  quasi-iso = `LensIso` = kernel coincidence (`lensIso_iff_kernel_eq`, `Unified.lean:64`). So **a quasi-iso
  IS a weak equivalence IS `Lens.refines` on the cohomology reading** — the reading slot is the same one
  `homotopy_theory.md` localized to form Ho(C).

- **Residue `q = ±1`** — TWO residues, the README's two poles, displayed degree by degree by the triangle:
  - **the q=−1 escape residue** — the nonzero cohomology a triangle's connecting map detects: the
    obstruction `Z` carries that `X`→`Y` failed to capture (`Ext^{>0}`, nonzero `Hⁿ`), tagged
    `escape`/`multiplier = −1` (`ResidueTag.lean:73,81`), delegating to `object1_not_surjective`
    (`FlatOntologyClosure.lean:61`). Concrete ∅-axiom witness: `NonzeroBetti.loopClass_not_coboundary`
    (`:134`, the hollow-triangle S¹ has a closed-not-coboundary class, `b₁=1`, 56/0 PURE).
  - **the q=+1 converge residue** — a triangle that *splits* / a quasi-iso to a contractible complex: the
    residue closes, `ker = im`, `Ext=0` (`reduced_betti_d4_contractible`, `BettiKernel.lean:63`), tagged
    `converge`/`multiplier = +1`, the same pole as φ/Gaussian/closure (`golden_is_converge`,
    `ResidueTag.lean:180`). `cycle_vs_contractible_qpm` (`NonzeroBetti.lean:173`) tags the contrast on
    `ResidueTag` directly: cycle = `escape` (q=−1, `im ⊊ ker`) vs contractible = `converge` (q=+1).

---

## Re-seeing — ⟨C | L⟩ ⊕ Residue(L,C)

```
   derived category D(A)     =  ⟨ category of chain complexes | quasi-iso reading L ⟩ ⊕ Residue(q=±1)
                                = homological_algebra's C (the resolution-dial objects), localized as in homotopy_theory
   chain complex (object)    =  homological_algebra's C  =  ⟨ graded cells | the coboundary delta ⟩  (Cochain, delta)
   quasi-isomorphism         =  iso on all Hⁿ  =  reads-the-same under "take cohomology"  =  Lens.refines / LensIso
                                = homotopy_theory's weak equivalence  (Lens.equiv; lensIso_iff_kernel_eq)
   D(A) = localize at quasi-iso =  the Quot-FREE LensImage Σ-quotient  (LensImage.proj_val_eq_iff)
                                =  the SAME Side-A machinery as Ho(C)  (FreeReduction.free_group_quotient_no_quot,
                                   no Quot.sound / Classical / Mathlib)  — homotopy_theory's NEW datum, reused
   the shift / suspension [1] =  the fold-height grading shifted by one  (the degree axis ++1)
                                = X[1] negates the differential = the q=±1 swap bit  (dsq_zero orientation; bracket_antisymm)
   [2] ≅ sign-identity        =  the q=±1 involution  ((−1)·(−1)=1, multiplier_unimodular)
   distinguished triangle     =  the LES PACKAGED into one rotatable object  (homological_algebra's connecting δ as an arrow)
     X → Y → Z → X[1]         =  Z = the residue X→Y left uncaptured (the cone); the third map = δ into the shift
   long exact sequence of △   =  …→Hⁿ(X)→Hⁿ(Y)→Hⁿ(Z)→Hⁿ⁺¹(X)→…  =  homological_algebra's residue-taking LES VERBATIM
                                = δ threads ker=im across degrees, δ²=0  (dsq_zero_universal_delta4)
   rotation of a triangle     =  the q=±1 shift-by-one re-indexing  (Z→X[1]→Y[1]→Z[1]; same orientation bit)
   derived functor Lf / Rf    =  the resolution-dial LIFT  =  Ext/Tor (homological_algebra) in their natural category
                                = resolve (resolution dial), apply F, read the graded residue  (IsResolutionShift, ResolutionShift)
   octahedral axiom           =  a COHERENCE: associativity of the residue composition (the cone-of-a-composite)
                                = a 2-cell filling among three triangles  (IsLensMorphism / refines_trans associativity)
   triangle splits / cone≃0   =  q=+1 converge: residue closes  (reduced_betti_d4_contractible; converge_residue_fixed)
   nonzero cone / non-split   =  q=−1 escape: the obstruction surfaces  (loopClass_not_coboundary; escape_residue_outside)
```

So **D(A), the shift [1], the distinguished triangle, the triangle's LES, the octahedral coherence, and
Lf/Rf are ONE machine: `homological_algebra.md`'s residue operation LOCATED in `homotopy_theory.md`'s
localized category.** Set against the two notes it consolidates:

| classical derived/triangulated object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| chain complex (object of D(A)) | `homological_algebra.md`'s `C`: graded cells + `delta` | `homological_algebra.md` | `Cochain/Core.lean:22 Cochain`; `Delta/Core.lean:54 delta` |
| quasi-isomorphism | weak equivalence = `Lens.refines` on "take cohomology" | `homotopy_theory.md` (W.E. = `Lens.refines`) | `LensCore.lean:90 Lens.refines`; `Unified.lean:64 lensIso_iff_kernel_eq` |
| D(A) = localize at quasi-iso | the `Quot`-free `LensImage`/`FreeReduction` Σ-quotient | `homotopy_theory.md` (Ho(C), the NEW datum) | `Unified.lean:163 LensImage.proj_val_eq_iff`; `FreeReduction.lean:264 free_group_quotient_no_quot` |
| shift [1] (X[1] flips the diff sign) | fold-height ++1; the q=±1 swap bit | NEW (height-shift = the q=±1 involution) | `dsq_zero_universal_delta4`; `Mat2Bracket.lean:76 bracket_antisymm`; `multiplier_unimodular` |
| distinguished triangle X→Y→Z→X[1] | the LES packaged; Z = the cone = the residue | NEW (the LES as one rotatable object) | (object; legs: `dsq_zero`, `ResidueTag`) |
| long exact sequence of a triangle | `homological_algebra.md`'s residue-taking LES | `homological_algebra.md` (LES = `δ`/`dsq_zero`) | `V4Capstone.lean:41 dsq_zero_universal_delta4` |
| derived functor Lf/Rf | the resolution-dial lift = `Ext`/`Tor` in D(A) | `homological_algebra.md` (resolution dial) | `ResolutionShift.lean:73 IsResolutionShift`, `:130 IsResolutionShift_compose` |
| octahedral axiom | a coherence (associativity of residue composition) | NEW (a 2-cell coherence) | `LensCore.lean:95 refines_trans`; `Morphism.lean:37 view_factors_through_morphism` |
| cone ≃ 0 / split triangle | q=+1 converge (residue closes) | `homological_algebra.md` (`Ext⁰`/exact) | `BettiKernel.lean:63 reduced_betti_d4_contractible`; `ResidueTag.lean:160 converge_residue_fixed` |
| nonzero cone / non-split | q=−1 escape (obstruction surfaces) | `homological_algebra.md` (`Ext^{>0}`) | `NonzeroBetti.lean:134 loopClass_not_coboundary`; `ResidueTag.lean:133 escape_residue_outside` |

D(A) consumes BOTH of `C`'s axes — fold-height (to shift and to grade the LES) and direction/orientation
(to sign the differential under `[1]`) — exactly as `homological_algebra.md`/`homotopy_theory.md` found,
*because it is the same residue machine, now given its category.*

---

## THE REVELATION (collapse + forcing + spine)

**Collapse — a derived category is NOT a new edifice: it is `homological_algebra.md`'s residue operation
placed inside `homotopy_theory.md`'s `Quot`-free localization, which is the home the residue operation
needed all along.** Three collapses, one per structural piece, plus the residue surfaced and the spine.

### 1. Collapse — D(A) = Ho(C) for chain complexes; the quasi-iso IS the weak equivalence (the NEW datum).

`homotopy_theory.md` established Ho(C) = localization at weak equivalence = the `Quot`-free `LensImage`
Σ-quotient (`LensImage.proj_val_eq_iff`, `Unified.lean:163`, 14/0 PURE) = the same Side-A machinery as the
free group (`FreeReduction.free_group_quotient_no_quot`, `:264`, 26/0 PURE — no `Quot.sound`, no
`Classical`, no Mathlib). The new datum *this* note contributes — beyond re-skinning either neighbor — is
that **a derived category is THAT SAME localization with the weak equivalences specialized to
quasi-isomorphisms**: a quasi-iso is a chain map that is an iso on all cohomology `Hⁿ`, and "iso on
cohomology" is precisely "reads the same under the residue-taking reading `Hⁿ = ker δ/im δ`" — i.e.
`Lens.refines` on `L = take cohomology` (`equivalence.md`). So D(A) = (chain complexes, the objects of
`homological_algebra.md`) localized at (quasi-iso = weak equivalence = `Lens.refines`, the reading of
`homotopy_theory.md`) = the *same* `LensImage`/`FreeReduction` Σ-quotient. **The homotopy category, the
localization, the Lens-image Σ-quotient, the free-reduction normal form, AND the derived category are one
quotient construction, named five ways.** This is the collapse that earns the note: D(A) is not a new
colimit to fear — it is the decidable, `Quot`-free q=+1 corner the program already built, with
`homological_algebra.md`'s complexes as its objects. The genuine residual is the SAME one
`homotopy_theory.md` located: the *named* `DerivedCategory`/`quasiIso`/`localization` object is absent (the
mechanism is built and PURE); see VALIDATE.

### 2. Forcing — the shift [1] is the fold-height grading shifted by one, with the differential sign-flip FORCED as the q=±1 swap bit.

The shift functor `[1]` looks like an extra piece of triangulated-category data. In the calculus it is
**forced** as the README's fold-height axis run by one step, carrying the README's direction/swap bit. Two
forcings, one per part of `[1]`'s definition:
- **The re-index `Cⁿ ↦ Cⁿ⁺¹`** is the fold-height grading `++1` — the *same* height `homological_algebra.md`
  grades `Ext^n` by and `homotopy_theory.md` grades `πₙ` by (`IsResolutionShift` composes additively in the
  exponent, `ResolutionShift.lean:73,130 IsResolutionShift_compose`, 17/0 PURE: shifting twice adds the
  grades, `[1]∘[1]=[2]`). The shift is the resolution dial counting one step — the same dial whose *orbit*
  is `spectral_sequences.md`'s page recursion.
- **The differential sign-flip** (`X[1]` carries `−d`) is the q=±1 swap bit — the orientation `dsq_zero`
  already carries (the alternating sign that makes `δ²=0` by pairwise cancellation,
  `dsq_zero_universal_delta4`, `V4Capstone.lean:41`), the same direction sub-structure that reads out as
  sign everywhere (integers, `∂²=0`, the loop). The sign-flip is *forced*, not chosen: a complex's
  differential is `delta`, and re-grading it by one inverts the orientation bit, exactly
  `Mat2Bracket.bracket_antisymm` `[A,B]=−[B,A]` (`Mat2Bracket.lean:76`, 10/0 PURE). And **`[2]` returns the
  sign to `+`** — `(−1)·(−1)=1`, the q=±1 involution `multiplier_unimodular` (`ResidueTag.lean:86`, 55/0
  PURE). So `[1]` is the fold-height axis carrying the q=±1 swap; `[2]` is that swap squared = identity-on-sign
  = the unimodular involution. No new primitive — `[1]` is "the height axis ++1, signed by the q=±1 bit".

### 3. Forcing — the distinguished triangle is the LES packaged into one rotatable object; rotation = the q=±1 shift.

A distinguished triangle `X → Y → Z → X[1]` looks like a replacement for the short/long exact sequence. In
the calculus it is **forced** as `homological_algebra.md`'s long exact sequence *packaged into one
rotatable object*: `Z` is the **cone** — exactly the residue `X→Y` left uncaptured (the q=−1 obstruction,
`Ext`-flavoured), and the third map `Z → X[1]` is `homological_algebra.md`'s **connecting map `δ` made an
arrow into the shift**. Applying cohomology to the triangle gives `…→Hⁿ(X)→Hⁿ(Y)→Hⁿ(Z)→Hⁿ⁺¹(X)→…`, which
is `homological_algebra.md`'s residue-taking LES verbatim — the connecting `δ` is the q=±1 sign-propagation,
`δ²=0` (`dsq_zero_universal_delta4`) threading `ker=im` across degrees. The triangle's defining feature —
**rotation** (`X→Y→Z→X[1]` is distinguished ⟺ `Y→Z→X[1]→Y[1]` is) — is the q=±1 shift-by-one re-indexing
applied to the whole object: rotating once advances every term by `[1]`, i.e. by the same height++1/sign-flip
of forcing 2. So the triangle *is* the LES wrapped so that the connecting `δ` becomes a structural map and
rotation = the shift; "distinguished" = "the cone is the genuine residue", split/`cone≃0` = q=+1
(`reduced_betti_d4_contractible`, residue empty), non-split/nonzero cone = q=−1
(`loopClass_not_coboundary`, the obstruction surfaces). The octahedral axiom is then the **coherence** that
two ways of building the cone of a composite agree — associativity of the residue composition, a 2-cell
filling among three triangles (`refines_trans`, `LensCore.lean:95`; `view_factors_through_morphism`,
`Morphism.lean:37`, the 2-category `homotopy_theory.md`/`two_cells.md` exhibits) — not a new primitive but
the same arrow-composition coherence the 2-category already carries.

### 4. Residue surfaced — Lf/Rf are the resolution-dial lift; D(A) is the residue operation's natural home.

`homological_algebra.md` named `Ext^n`/`Tor_n` as `Residue(F∘resolution, C)` graded by `n`, but had to
*choose a resolution* each time (proj/inj), the resolution being external scaffolding. The derived category
is exactly the home where that choice disappears: a **derived functor `Lf`/`Rf`** is the original functor
*lifted to D(A)*, where resolving-and-then-localizing-at-quasi-iso has made the choice of resolution
invisible (any two resolutions are quasi-isomorphic = `Lens.refines`-equivalent = identified in the
Σ-quotient). So `Lf`/`Rf` = the resolution-dial lift: `homological_algebra.md`'s `Ext`/`Tor` read *in their
natural category*, where the resolution is no longer auxiliary data but absorbed by the localization
(`IsResolutionShift`/`IsResolutionShift_compose`, the dial that composes additively; the quasi-iso identification
= `LensImage.proj_val_eq_iff`). The README's `Residue(L,C)` operation — "resolve, apply a non-exact reading,
read the graded residue" — *needs* a category where resolutions are interchangeable to be a clean operation;
D(A) is that category. This is `spectral_sequences.md`'s lesson at one level down: there the residue
operation was shown *iterable* (the page orbit); here it is shown to have a *home* (the localized category
of complexes) where its one application is functorial.

### The spine.

The triangulated structure is the q=±1 spine displayed on triangles: **q=+1** = split triangle /
`cone ≃ 0` / quasi-iso to a contractible complex / `Ext=0` — the converging pole that *closes*
(`reduced_betti_d4_contractible`, `converge_residue_fixed`, `golden_is_converge`); **q=−1** = non-split
triangle / nonzero cone / the obstruction the triangle's LES displays — the escaping pole
(`loopClass_not_coboundary`, `dsq_zero_universal_delta4`, `escape_residue_outside`, delegating to
`object1_not_surjective`). The shift `[1]` is the q=±1 swap bit threading the two; rotation re-indexes the
spine by one. The same single spine `SYNTHESIS.md` §3 runs through Cantor/Gödel/φ/measure/homology, now read
on the distinguished triangle.

---

## VALIDATE — verdict

**EXTEND (by consolidation) + PREDICTION + PARTIAL-BREAK.** The model held across the corpus with no new
axis; this is a consolidation that ties `homological_algebra.md` + `homotopy_theory.md` into one statement,
with one genuinely NEW datum (D(A) = the residue operation's natural home = chain complexes localized by the
SAME `Quot`-free Σ-quotient as Ho(C); the shift `[1]` = the fold-height++1 carrying the q=±1 swap bit) and
one recurring located break.

- **EXTENDS, grounded ∅-axiom:** the **chain-complex objects** (`Cochain`, `delta`); the **quasi-iso =
  weak-equivalence reading** = `Lens.refines`/`LensIso` (`lensIso_iff_kernel_eq`); **D(A) = localization** =
  the `Quot`-free `LensImage`/`FreeReduction` Σ-quotient (`proj_val_eq_iff`, `free_group_quotient_no_quot`,
  14/0 + 26/0 — the NEW datum, reused from `homotopy_theory.md`); the **shift `[1]`** = fold-height++1
  (`IsResolutionShift_compose`, 17/0) signed by the q=±1 swap bit (`bracket_antisymm` 10/0,
  `multiplier_unimodular` 55/0); the **triangle's LES + connecting `δ` + `δ²=0`** = the residue-taking LES
  (`dsq_zero_universal_delta4`, 5/0); the **split/non-split poles** = q=±1
  (`reduced_betti_d4_contractible`, `loopClass_not_coboundary` 56/0, `cycle_vs_contractible_qpm`,
  `ResidueTag` 55/0); the **octahedral coherence** = the 2-category's arrow-composition coherence
  (`refines_trans`, `view_factors_through_morphism`, 3/0).

- **PREDICTION:** the calculus predicts the *form* of a derived/triangulated category (objects = complexes;
  D(A) = the quasi-iso Σ-quotient; `[1]` = the q=±1-signed height shift; triangle = the LES packaged;
  octahedral = a coherence; Lf/Rf = the resolution-dial lift) and the *named objects are ABSENT* — the same
  shape as `homological_algebra.md`'s missing `Ext^n` and `homotopy_theory.md`'s missing `ModelCategory`.

- **PARTIAL-BREAK (the localization's non-decidable corner — `homotopy_theory.md`/`knots.md`'s SAME break,
  a recurrence):** the `Quot`-free Σ-quotient builds the localization exactly where the equivalence is
  decidable / confluent-terminating (the q=+1 corner — quasi-iso between complexes with a computable
  normal form). The general localization-of-a-category-at-a-class-of-arrows (the calculus of fractions,
  where a roof `X ← X' → Y` needs an ambient identification no reading's kernel generates) is the un-built
  colimit/q=−1 corner Side B (`SYNTHESIS.md` §5.1) — the same located boundary as the homotopy/isotopy
  quotient, recurring. So D(A) is built where the quasi-iso relation is decidable, absent where the calculus
  of fractions needs a non-confluent quotient — the constructive boundary, located.

---

## Verified Lean anchors (file:line:theorem — all grep/Read-verified on `lean/E213`; purity scanned via `tools/scan_axioms.py` from repo root this session)

| Leg | Anchor (file:line : name) | Purity (scanned) |
|---|---|---|
| **★ D(A) = localize at quasi-iso = the Quot-free Σ-quotient (= Ho(C), the NEW datum)** | `Lens/Unified.lean:163 : LensImage.proj_val_eq_iff` (`(proj L x).val = (proj L y).val ↔ L.equiv x y`) | PURE (Unified **14/0**) |
| **★ same colimit Side-A machinery (free-reduction normal form, no `Quot`/`Classical`/Mathlib)** | `Lib/Math/Algebra/Group/FreeReduction.lean:237 : proj_val_eq_iff`; `:264 : free_group_quotient_no_quot`; `:191 : freeReduce_idempotent` | PURE (FreeReduction **26/0**) |
| **quasi-iso = weak equivalence = `Lens.refines` / `LensIso` = kernel coincidence** | `Lens/LensCore.lean:90 : Lens.refines`, `:93 : refines_refl`, `:95 : refines_trans`; `Lens/Unified.lean:42 : LensIso`, `:64 : lensIso_iff_kernel_eq`, `:54 : lensIso_trans` | PURE (LensCore **11/0**, Unified **14/0**) |
| **chain complex = the objects (graded cells + coboundary)** | `Lib/Math/Cohomology/Cochain/Core.lean:22 : Cochain`; `Lib/Math/Cohomology/Delta/Core.lean:54 : delta`, `:42 : deltaAt` | PURE (per `homological_algebra.md`) |
| **★ shift `[1]` = fold-height++1 (the resolution dial, composes additively → `[1]∘[1]=[2]`)** | `Lib/Math/Analysis/ResolutionShift.lean:73 : IsResolutionShift`, `:130 : IsResolutionShift_compose` | PURE (ResolutionShift **17/0**) |
| **★ `[1]`'s differential sign-flip = the q=±1 swap bit; `[2]` = the q=±1 involution** | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:76 : bracket_antisymm` (`[A,B]=−[B,A]`); `Lib/Math/Foundations/ResidueTag.lean:86 : multiplier_unimodular` (`q·q=1`) | PURE (Mat2Bracket **10/0**, ResidueTag **55/0**) |
| **★ triangle's LES + connecting `δ` + `δ²=0` = the residue-taking LES (packaged)** | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 : dsq_zero_universal_delta4`; `:62 : leibniz_universal_delta4` (cup/Yoneda product on the residue) | PURE (V4Capstone **5/0**) |
| **q=+1 converge pole: split triangle / `cone≃0` / `Ext=0` (`ker=im`)** | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 : reduced_betti_d4_contractible`, `:42 : kerSizeDelta`; `Lib/Math/Foundations/ResidueTag.lean:160 : converge_residue_fixed`, `:180 : golden_is_converge` | PURE (BettiKernel **11/0**, ResidueTag **55/0**) |
| **q=−1 escape pole: nonzero cone / non-split (`im ⊊ ker`) — concrete H¹ witness** | `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:134 : loopClass_not_coboundary`, `:111 : betti_one_cycle`, `:143 : nonzero_cohomology_class`, `:173 : cycle_vs_contractible_qpm`; `Lib/Math/Foundations/ResidueTag.lean:133 : escape_residue_outside`, `:73 : ResidueTag`, `:228 : residue_tag_two_poles` | PURE (NonzeroBetti **56/0**, ResidueTag **55/0**) |
| **octahedral axiom = a 2-cell coherence (arrow-composition associativity)** | `Lens/LensCore.lean:95 : refines_trans`; `Lens/Compose/Morphism.lean:37 : view_factors_through_morphism`, `:29 : IsLensMorphism` | PURE (LensCore **11/0**, Morphism **3/0**) |
| **derived functor Lf/Rf = the resolution-dial lift; triangle rotation = the q=±1 shift** | `Lib/Math/Analysis/ResolutionShift.lean:73 : IsResolutionShift`, `:130 : IsResolutionShift_compose`; (residue iterated) `Lens/Foundations/ResidueReentry.lean:63 : residue_reentry_never_closes` | PURE (ResolutionShift **17/0**) |
| escape / faithful residue (the q=−1 pole's kernel) | `Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective`, `:47 : object1_injective` | PURE (FlatOntologyClosure **7/0**) |

**Fresh scan tallies this session (`tools/scan_axioms.py` from repo root, `E213.` prefix):**
`E213.Lens.Unified` **14/0**, `E213.Lens.LensCore` **11/0**,
`E213.Lib.Math.Algebra.Group.FreeReduction` **26/0**, `E213.Lib.Math.Foundations.ResidueTag` **55/0**,
`E213.Lib.Math.Cohomology.Delta.V4Capstone` **5/0**, `E213.Lib.Math.Cohomology.Examples.BettiKernel`
**11/0**, `E213.Lib.Math.Cohomology.Examples.NonzeroBetti` **56/0**,
`E213.Lib.Math.Analysis.ResolutionShift` **17/0**,
`E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice` **26/0**,
`E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Bracket` **10/0**,
`E213.Lens.Foundations.FlatOntologyClosure` **7/0**. All load-bearing anchors PURE.

---

## Dropped / flagged (honest — NOT grounded in repo Lean)

- **The named `DerivedCategory` / `triangulated` / `shiftFunctor` / `suspensionFunctor` /
  `distinguishedTriangle` / `octahedral`-axiom / `quasiIso` / `Lf`/`Rf` objects — ABSENT,
  predicted-not-built.** Grep over `lean/E213` for `derived_category`/`DerivedCategory`/`triangulated`/
  `Triangulated`/`distinguished_triangle`/`distinguishedTriangle`/`octahedral`/`Octahedral` (as the
  triangulated axiom)/`quasi_iso`/`quasiIso`/`QuasiIso`/`shiftFunctor`/`suspensionFunctor` returns **zero
  matching declarations**. The only `octahedral`/`triangle`/`shift` token hits are unrelated: the **binary
  octahedral group `2O`** (order 48, the E₇ McKay node) in `CayleyDickson/Tower/*Octahedral.lean` (polyhedral
  symmetry, NOT the triangulated octahedral axiom — confirmed by reading `TypeOOctahedral.lean`), geometric
  "triangle" (Heron/lattice/iteration), and resolution/sequence "shift". This is the precise missing leg —
  the same shape as `homological_algebra.md`'s missing `Ext^n` and `homotopy_theory.md`'s missing
  `ModelCategory`/`fibration`: every *structural mechanism* (the complex objects, the quasi-iso =
  `Lens.refines` reading, the `Quot`-free Σ-quotient localization, the q=±1-signed shift, the LES/`δ`/`δ²=0`,
  the split/non-split poles, the 2-cell coherence) is built and PURE; only the *named bundle* welding them
  into `DerivedCategory`/`distinguishedTriangle`/`[1]` is open.
- **A `Cone`/`mappingCone` object + the triangle-as-a-typed-object — ABSENT.** The cone IS the residue
  `X→Y` leaves (q=−1, `ker δ/im δ`, witnessed `NonzeroBetti.loopClass_not_coboundary`), but there is no
  `Cone : ChainMap → ChainComplex` constructor nor a `Triangle` type with the rotation/octahedral axioms.
  The residue mechanism is built; the named cone/triangle object is the open leg.
- **The localization's non-decidable corner (the calculus of fractions / roofs) — PARTIAL-BREAK, Side B.**
  D(A)'s Σ-quotient is built exactly where the quasi-iso relation is decidable / confluent-terminating (the
  q=+1 corner, the same `FreeReduction` 26/0 Side-A witness `homotopy_theory.md` reused for Ho(C)). The
  general localization where a roof needs an ambient identification (non-confluent / undecidable) is
  `SYNTHESIS.md` §5.1 Side B — theorem-grade absent, the same break recurring. **No *new* witness is
  proposed (no unverified `decide` claim); the existing 14/0 + 26/0 Σ-quotient is the honest buildable side.**
- **Derived functor Lf/Rf as a named object (resolution-independence theorem) — conceptual.** The
  resolution dial (`IsResolutionShift`/`IsResolutionShift_compose`) and the quasi-iso identification
  (`LensImage.proj_val_eq_iff`) are built and PURE; the single theorem "any two resolutions are
  quasi-isomorphic, so `Lf` is well-defined on D(A)" is conceptual framing on verified PURE objects — the
  same shape as `homological_algebra.md`'s derived-functor identification.

---

## Cross-frame

`homological_algebra.md` (KEY — the residue operation `Ext`/`Tor`; the connecting `δ`/LES = `dsq_zero`; the
resolution dial; `Ext⁰/Tor₀`=q+1 exact, `Ext^{>0}/Tor_{>0}`=q−1 obstruction — D(A) is this operation's
natural home); `homotopy_theory.md` (KEY — Ho(C) = the `Quot`-free `LensImage`/`FreeReduction`
localization; quasi-iso = weak equivalence = `Lens.refines`; the localization's non-decidable corner = the
shared break); `spectral_sequences.md` (the residue operation ITERATED — `[1]` here is the same
resolution-dial step whose orbit is the page recursion); `motives.md` (the `⟨C|L⟩` half — the universal
construction through which realizations factor, dual to D(A)'s `Residue(L,C)` half); `homology.md` (the
`∂`/`d` = `delta`, `Hⁿ = ker δ/im δ` the quasi-iso reading); `equivalence.md` (quasi-iso = the one
Lens-arrow `Lens.refines`, iso = kernel coincidence); `two_cells.md` (the 2-category the octahedral
coherence lives in); `SYNTHESIS.md` §2 (homological algebra = `Residue(L,C)`), §3 (the q=±1 spine), §5.1
(the Side-A/Side-B localization split this break shares).

> Axiom-purity note: every load-bearing anchor was freshly scanned PURE this session via
> `tools/scan_axioms.py` (run from repo root with the `E213.` module prefix). The named
> `DerivedCategory`/`triangulated`/`shift`/`distinguishedTriangle`/`octahedral`(-axiom)/`quasiIso` objects
> are grep-confirmed ABSENT (the `octahedral` token is the binary octahedral *group* `2O`, unrelated). The
> purity and absence claims rest on the fresh scan and grep, not docstrings.
