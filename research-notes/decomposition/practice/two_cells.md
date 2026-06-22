# Decomposition: natural transformations / 2-cells — attacking the knots boundary

*META-decomposition, per `../README.md` (model v7) and the located boundary of `knots.md`. The knots
decomposition BROKE at two points the normal form `⟨C-self-application | reading⟩ ⊕ residue(q=±1)`
does not cover: (1) the **skein relation** = a *relation among distinct constructions*; (2) the knot =
an **ambient-isotopy quotient**. The deep question: is "relation among distinct constructions" a
GENUINELY NEW primitive, or is it a **2-cell** — a reading-between-readings — that the **category of
readings** the calculus already established (`adjunction.md`, `category_theory.md`) admits at the next
level up?*

*Field chosen: **natural transformations / the 2-categorical structure**. A natural transformation IS
a family of relations among the images of two functors-as-readings — the sharpest native test of the
2-cell hypothesis, because the calculus already proved the naturality triangle before it was named.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — here `C` is *a pair of readings of the same construction*. Two Lenses
  `L : Lens α`, `M : Lens β` are two folds out of the initial object `Raw` (`category_theory.md`:
  readings = morphisms, `Raw.fold`/`universalMorphism` = the unique arrow out of the initial object,
  so each Lens is a **functor-shaped** arrow `Raw → α`). The object under decomposition is the
  *relation between* `L` and `M` — not one Lens's self-application, but a comparison of two.

- **Reading `L` (the 2-cell reading)** — the organizing reading is **"how does one reading map onto
  another, level-wise?"** A *2-cell* `L ⟹ M` is a component map `h : α → β` together with the demand
  that it commute with the two readings on every construction:

  ```
     L ⟹ M   (a 2-cell)   :=   h : α → β   with   M.view r = h (L.view r)   for all r : Raw
  ```

  This is **literally a natural transformation**: `L.view` and `M.view` are the two functors (arrows
  out of the initial object), `h` is the component, and `M.view = h ∘ L.view` is the **naturality
  square** — which over the *single* initial object `Raw` collapses to exactly this triangle (the
  base-point square `h(L.base_a)=M.base_a` + the combine square `h(L.combine u v)=M.combine (h u)(h v)`
  are the two generating naturality conditions, and `Raw`'s induction propagates them to all `r`).

- **Residue** — what the 2-cell reading forces but cannot capture is **the relations that are NOT a
  single component map respecting one operation** — i.e. relations among *three or more* distinct
  constructions tied by a *fixed linear combination* (skein/Leibniz), and identifications coming from
  a *space the calculus has no `Raw` for* (isotopy). The 2-cell reading covers the *homomorphism /
  naturality* shape of "relation among constructions"; its residue is the *non-homomorphism* shapes.

## Re-seeing (⟨C | L⟩) — the 2-cell layer, term by term

```
   a 2-cell  L ⟹ M       =  ⟨ two readings of Raw | a component map h commuting with both ⟩
   the component map h    =  α → β                          (IsLensMorphism h L M)
   naturality square      =  h(L.combine u v)=M.combine(h u)(h v) ∧ h(L.base_*)=M.base_*
   naturality (all of Raw)=  M.view = h ∘ L.view             (view_factors_through_morphism)
   2-cell ⟹ 1-cell        =  a 2-cell INDUCES a refinement   (refines_of_morphism: L.refines M)
   invertible 2-cell      =  LensIso L M  (mutual refinement = kernel coincidence)
   identity 2-cell        =  refines_refl;  vertical ∘ = refines_trans
   the ONLY 2-cell out of Raw is the identity  =  dhom_unique_pointwise (initiality forces it)
```

Set against `category_theory.md`'s table (which named "natural transformation = a reading between two
functors" and cited `dhom_unique_pointwise` for the *shape*): this entry makes the 2-cell **a real
worked arrow with components**, not just a pointwise-uniqueness slogan. The naturality triangle
`M.view = h ∘ L.view` is a *proven ∅-axiom theorem* (`view_factors_through_morphism`), and it is
exactly the data a natural transformation carries.

## THE REVELATION — the boundary SPLITS into three, and only one third is genuinely new

**The 2-cell hypothesis does NOT give a single yes/no. It *partitions* "relation among distinct
constructions" into three shapes, and the calculus's status on each is different — that partition is
the result.**

### Shape 1 — the *naturality / homomorphism* relation: **DISSOLVES (the 2-cell is already built).**

A natural transformation between two functors-as-readings is a 2-cell `L ⟹ M`, and the calculus
**already has the entire 2-cell layer**, ∅-axiom:

- **The 2-cell itself** is `IsLensMorphism h L M` (`Lens/Compose/Morphism.lean:29`): a component map
  `h` with the two naturality squares (base-points, combine).
- **Naturality is proved**: `view_factors_through_morphism` (`Morphism.lean:37`) gives
  `M.view r = h (L.view r)` for all `r` — the naturality triangle over the initial object, by
  `Raw.rec`. This is a natural transformation, term for term.
- **2-cells and 1-cells interlock correctly**: `refines_of_morphism` (`Morphism.lean:60`) shows a
  2-cell `L ⟹ M` *induces* the 1-cell `L.refines M` — vertical structure feeding horizontal, the
  hallmark of a 2-category. The invertible 2-cells are `LensIso` (`Unified.lean:42`, with
  `lensIso_refl/symm/trans` = the groupoid of 2-cells), and the identity/vertical-composition are
  `refines_refl`/`refines_trans` (`LensCore.lean:93,95`).
- **Initiality pins the 2-cells out of `Raw`**: `dhom_unique_pointwise`
  (`UniversalDistinguishing.lean:103`) — *any two* structure-maps `Raw → N` agree pointwise, so the
  only 2-cell between two functors out of the initial object is the identity. This is *why* `Raw` is
  initial, and it is the natural-transformation structure in its degenerate (forced-unique) form.

So **a natural transformation IS a 2-cell the category of readings already admits** — the README's
hypothesis (a) is confirmed for the naturality/homomorphism shape. A "relation among distinct
constructions" of the form "a single map `h` intertwines reading `L` with reading `M`, respecting the
build-operation" is **not a new primitive**; it is the 2-cell `view_factors_through_morphism` already
proves. The knots note's worry — that relations-among-constructions are *outside* the
`⟨C-self-application | reading⟩` shape — is, for *this* shape, answered: a 2-cell is the relating-arrow
*between two readings*, which is precisely one level up in the category the calculus already lives in.

### Shape 2 — the *skein / Leibniz* relation: **REAL but PARTIALLY PRESENT — a new construct, not a 2-cell.**

The skein relation `t⁻¹V(L₊) − tV(L₋) = (t^½−t^−½)V(L₀)` is **not** Shape 1. It is a **fixed linear
combination of one reading applied to three distinct constructions** `L₊, L₋, L₀`, summing to zero —
where the three constructions differ *locally* (over-crossing, under-crossing, smoothing changes the
strand count). No single component map `h` intertwines them; there is no functor `L₊ ⟹ L₋`. A 2-cell
relates two *readings of one C*; the skein triple relates *one reading of three C's*. These are
orthogonal: the 2-cell axis is "fix the C, vary the reading"; the skein axis is "fix the reading, vary
the C, demand a linear relation."

**But the calculus is NOT empty here — it has a genuine in-repo instance of exactly this shape, and
naming it is the payoff.** The **Leibniz rule** for the cup product

```
   δ(α ⌣ β)  =  (δα ⌣ β)  ⊕  (α ⌣ δβ)
```

(`Cohomology/Delta/V4Capstone.lean:62`, `leibniz_universal_delta4`, ∅-axiom PURE) is a **three-term
relation among distinct constructions**: `δ(α⌣β)`, `δα⌣β`, and `α⌣δβ` are three *different* cochains,
tied by a fixed (here mod-2, so XOR) linear combination. This is the *same shape* as the skein
relation — a fixed linear law relating one reading (here `δ`, the boundary-reading) applied across a
family of related-but-distinct constructions. `homology.md` had already flagged Leibniz as "the
closest shadow" of a multi-term relation; this decomposition **promotes that shadow to the answer**:
the skein relation's *algebraic form* is the calculus's **derivation/Leibniz primitive** — a
**graded relation among a family of constructions under one reading**, not a 2-cell.

So the calculus needs (and partially has) a third slot, distinct from both invariants:

> **A graded-relation slot: a fixed linear law `Σ cᵢ · L(Cᵢ) = 0` among a finite family `{Cᵢ}` of
> distinct constructions related by a local move, where `L` is one reading.** Leibniz
> (`δ(α⌣β)=δα⌣β ⊕ α⌣δβ`) is the in-repo instance; the skein relation is the topological instance.
> This is neither the character arrow (`L(αβ)=L(α)·L(β)`, a *two*-term homomorphism of *one* C's build)
> nor the `q=±1` residue. The character arrow is its degenerate two-term case (one C, one product).

The honest gap: the repo's instance is the **derivation** law (`δ` is a *fixed* differential, the
three constructions related by `δ` itself), whereas the skein relation's three constructions are
related by a **crossing-resolution move** that the calculus has no operation for — see Shape 3. So the
*algebraic form* of the skein relation (a graded three-term law) is a real, partially-grounded
construct; the *move that generates the triple* is not.

### Shape 3 — the *isotopy quotient*: **REAL and ABSENT (the 2-cell layer does NOT supply it).**

The 2-cell hypothesis was raised for *both* knots gaps. For the isotopy quotient it **fails cleanly**,
and saying so is the result. An ambient-isotopy quotient is *not* a 2-cell:

- A 2-cell `L ⟹ M` is a relation between two *readings* with components in the *types* `α, β`. The
  isotopy quotient is an identification on the *constructions themselves* (two braid words name one
  knot) coming from continuous deformation in an ambient `S³`.
- The calculus's only construction-level identifications are **kernel-coincidences** (`LensIso` =
  `lensIso_iff_kernel_eq`, `Unified.lean:64` — two readings have the *same fibres*) and **closure
  operators** (`clo`, `galois.md`). A 2-cell *induces* a kernel-refinement (`refines_of_morphism`), so
  the 2-cell layer's reach on quotients is exactly the kernel/closure layer — **algebraic** quotients.
- The isotopy quotient is **not the kernel of any reading the calculus can write**: there is no Lens
  whose `equiv` is "ambient-isotopic in `S³`," because there is no `Raw`/`Lens` construction for the
  ambient 3-manifold (the calculus builds `Real213` cuts, not embeddings/isotopies). The `q=±1`
  residue tag — which generated every prior limitative phenomenon by self-application — does not apply:
  there is no diagonal, no fixed-point asymptote producing the isotopy class.

So **the isotopy quotient is a genuinely missing primitive**, and the 2-cell layer does *not* rescue
it. It is a *quotient by a relation the calculus cannot generate from any reading's kernel or
self-application* — categorically, a coequalizer / colimit in a category the calculus has only built
the `q=+1` (closure/limit) corner of (`adjunction.md`, `category_theory.md`: the free/colimit corner
is the standing open edge). The isotopy quotient sits exactly in that un-built `q=−1`/colimit corner,
and additionally needs an *ambient-space construction* the calculus does not have at all.

## Verdict — **the boundary is BOTH (it splits): one third DISSOLVES, two thirds are REAL.**

Honest, three-way:

1. **Naturality/homomorphism relations → DISSOLVE.** A natural transformation is a **2-cell the
   category of readings already admits**, fully ∅-axiom: `view_factors_through_morphism` (the
   naturality triangle `M.view = h∘L.view`), `IsLensMorphism` (the component + naturality squares),
   `refines_of_morphism` (2-cell ⟹ 1-cell), `LensIso` (invertible 2-cells), `dhom_unique_pointwise`
   (initiality forces uniqueness of the 2-cell out of `Raw`). The knots note over-stated this third of
   the break: a relation-among-constructions of *naturality* shape is not a missing primitive — it is
   the 2-cell, one level up.

2. **Skein/Leibniz (graded three-term) relations → REAL, partially present.** A new construct is
   needed — a **graded-relation slot**: a fixed linear law among a *family* of distinct constructions
   under one reading. It is **not** a 2-cell (that relates readings of one C; this relates one reading
   of many C's) and **not** the character arrow (its degenerate two-term case). The repo *has* an
   instance — the cup-product **Leibniz rule** `leibniz_universal_delta4` — so the construct is
   grounded as a *derivation* law; the skein relation's crossing-resolution *move* that generates the
   triple is not (it depends on Shape 3).

3. **Isotopy quotient → REAL and ABSENT.** The 2-cell layer does **not** supply it. It is a quotient
   by a relation no reading's kernel or self-application generates, living in the un-built
   colimit/`q=−1` corner *and* requiring an ambient-space construction the calculus lacks entirely.
   This is the hardest, cleanest missing primitive.

**THE REVELATION (collapse on one axis, two located primitives on the others):** "relation among
distinct constructions" was a *conflation* of three different shapes. The decomposition's payoff is
the **partition itself** — it dissolves the naturality third into the already-built 2-cell layer
(`view_factors_through_morphism` IS the naturality triangle), isolates the skein/Leibniz third as a
real **graded-relation primitive** (grounded by `leibniz_universal_delta4`, distinct from both
invariants), and confirms the isotopy third as a genuinely absent colimit-corner + ambient-space
primitive. The knots break was real, but it was *two* breaks wearing one name, plus one non-break.

## Does this change model v7? — YES, a refinement (not a new axis).

Model v7's break-marker (item 2) said the normal form does *not* cover (a) relations among distinct
constructions or (b) isotopy quotients, naming both as missing. This decomposition **sharpens (a) and
leaves (b) standing, with a precise relocation**:

- **(a) is too coarse — split it.** "Relations among distinct constructions" is three shapes:
  - *naturality/homomorphism* → **already covered** by the 2-cell layer (the **category of readings'
    2-cells**: `view_factors_through_morphism`, `IsLensMorphism`, `refines_of_morphism`, `LensIso`,
    `dhom_unique_pointwise`). Remove this from the "missing" list; record it as **the calculus's 2-cell
    structure, ∅-axiom, made explicit**.
  - *graded multi-term (skein/Leibniz)* → a **new construct, the graded-relation slot**, partially
    grounded (`leibniz_universal_delta4`). Add it to the model as a construct *distinct from the
    character arrow and the `q=±1` residue* — the character arrow is its two-term degenerate case.
  - The two invariants (character arrow, `q=±1` residue) and the four axes are unchanged.
- **(b) stands, relocated.** The isotopy quotient remains a genuinely missing primitive; this entry
  *locates* it precisely in the **un-built colimit/`q=−1` corner** (`adjunction.md`/`category_theory.md`'s
  standing open edge) **plus an absent ambient-space construction** — not a fourth mysterious gap, but
  the intersection of two already-known open edges.

**Net suggested v7→v7.1 edit:** the calculus *gains an explicit 2-cell layer* (readings form a
**2-category**, not just a category — 1-cells = `refines`, 2-cells = `IsLensMorphism`/`LensIso`, with
`view_factors_through_morphism` the naturality law and `dhom_unique_pointwise` the initiality
coherence), and the "missing primitive" list is reduced from two items to: **(i) the graded-relation
slot** (partially grounded by Leibniz — a *promotion target*, not pure absence) and **(ii) the
isotopy/colimit quotient** (the genuine remaining absence, located in the `q=−1` corner). The break is
smaller and more precisely mapped than v7 recorded.

---

### Verified Lean anchors (all grep-checked, all ∅-axiom PURE — scanned this session)

| Anchor (theorem / def) | File:line | Role in this decomposition | Purity |
|---|---|---|---|
| `view_factors_through_morphism` | `lean/E213/Lens/Compose/Morphism.lean:37` | **the naturality triangle** `M.view = h∘L.view` — a natural transformation, term for term (Shape 1 dissolution) | PURE (scanned) |
| `IsLensMorphism` | `lean/E213/Lens/Compose/Morphism.lean:29` | the 2-cell component `h` + the two naturality squares (base-points, combine) | PURE (scanned) |
| `refines_of_morphism` | `lean/E213/Lens/Compose/Morphism.lean:60` | a **2-cell induces a 1-cell** `L.refines M` — the 2-category interlock | PURE (scanned) |
| `Lens.refines` / `refines_refl` / `refines_trans` | `lean/E213/Lens/LensCore.lean:90,93,95` | 1-cells (the thin category) = identity + vertical composition of 2-cells | PURE |
| `LensIso` / `lensIso_refl/symm/trans` / `lensIso_iff_kernel_eq` | `lean/E213/Lens/Unified.lean:42,46,50,54,64` | invertible 2-cells (groupoid) + iso = kernel coincidence (the algebraic quotient the 2-cell layer reaches) | PURE |
| `dhom_unique_pointwise` | `lean/E213/Lens/Foundations/UniversalDistinguishing.lean:103` | **initiality forces the only 2-cell out of `Raw` to be the identity** — natural-transformation coherence | PURE (scanned) |
| `DStr` / `DHom` / `rawDStr_generated` | `lean/E213/Lens/Foundations/UniversalDistinguishing.lean:40,85,76` | functor/nat-trans schema (carriers + structure-maps) | PURE (scanned) |
| `raw_initial` / `universalMorphism_unique` | `lean/E213/Lens/Foundations/SemanticAtom.lean:412,388` | readings are arrows out of the **initial object** = functors (so a relation between two is a 2-cell) | PURE |
| `leibniz_universal_delta4` | `lean/E213/Lib/Math/Cohomology/Delta/V4Capstone.lean:62` | ★ **three-term relation among distinct constructions** `δ(α⌣β)=δα⌣β ⊕ α⌣δβ` — the in-repo instance of the skein/Leibniz **graded-relation primitive** (Shape 2) | PURE (scanned) |
| `dsq_zero_universal_delta4` | `lean/E213/Lib/Math/Cohomology/Delta/V4Capstone.lean:41` | the `q=±1` pairwise sign-cancellation (`homology.md`) — a *two-reading* relation, contrasted with the *three-construction* Leibniz to show they are different shapes | PURE (scanned) |
| `gc` / `gc_fgf`/`gc_gfg`/`clo_idempotent` | `lean/E213/Lib/Math/Order/GaloisConnection.lean:43,62,71,...` | the closure quotient — the *algebraic* quotient the 2-cell layer reaches, contrasted with the *topological* isotopy quotient it does not (Shape 3) | PURE (scanned) |

**Honest prose-only legs (NOT grounded — flagged):**
- The skein relation's **crossing-resolution move** generating `L₊/L₋/L₀` — no in-repo construction;
  only its *algebraic form* (a graded three-term law) is grounded, via Leibniz.
- The **ambient-isotopy quotient** (Shape 3) — entirely absent (no ambient 3-manifold, no embedding,
  no isotopy in `lean/E213/`); located conceptually in the un-built colimit/`q=−1` corner.
- The **2-category packaging** itself (that `{refines, IsLensMorphism}` assemble into a formal
  2-category with interchange) is *not* a single packaged theorem; it is exhibited piece-by-piece by
  the anchors above. Interchange/horizontal-composition coherence is a prose claim here, not a theorem.

### Cross-frame
`category_theory.md` (named "nat-trans = reading between functors", `dhom_unique_pointwise` — this
entry makes it a worked 2-cell with components via `view_factors_through_morphism`); `adjunction.md`
(the category of readings, the `q=+1`-only built corner — Shape 3 lives in the un-built corner);
`galois.md` (closure = the algebraic quotient, contrasted with the topological isotopy quotient);
`homology.md` (`leibniz_universal_delta4`/`dsq_zero` — the graded-relation instance and the contrasting
two-reading cancellation); `knots.md` (the boundary this entry attacks and re-partitions).
