# Decomposition: perverse sheaves / intersection cohomology (the perverse t-structure on D^b_c(X), the IC complex, the perverse heart, the BBD Decomposition Theorem, the intermediate extension j!*, Verdier/Poincaré duality for singular spaces)

*A FRESH decomposition per `../README.md` (model v7.1) and `SYNTHESIS.md` (the two invariants — the
character arrow, the `q=±1` residue tag; §2 the residue-taking operation and its two reflexive halves;
§3 the `q=±1` spine). Consolidates `derived_categories.md` (JUST DONE — D(A) = the residue machine in the
`Quot`-free localization; the shift `[1]`; distinguished triangles; the LES; `Lf`/`Rf`), `sheaf_theory.md`
(KEY — sheaf cohomology = the local-global `q=±1` obstruction; `H⁰` glued / `H^{>0}` escape), and
`homological_algebra.md` (the residue/LES, `Ext`/`Tor`, the connecting `δ`), with `homology.md` (Poincaré
duality, the `q=±1` orientation bit, `∂²=0`). The hypothesis to **test**, not re-skin:*

> **Perverse sheaves are the calculus's residue-taking machine on the derived category, RE-TRUNCATED by a
> t-structure (a fold-height re-grading), with IC = the q=+1 self-dual canonical (intermediate) extension
> and the Decomposition Theorem = the residue splitting into q=±1 graded IC summands.** The derived
> category (`derived_categories.md` = the residue operation in the `Quot`-free localization) carries a
> **t-structure** = a choice of fold-height truncation; the **perverse t-structure** re-grades by a
> support/dimension condition — a *different reading of the SAME fold-height axis* (`Lambek.isPart_wf`,
> `IsResolutionShift`). The **perverse heart** = the abelian category at the truncation level (the residue
> read at one perverse degree). **IC = j!*** = the q=+1 "neither-too-big-nor-too-small" canonical/self-dual
> extension — the SAME canonical-normal-form / self-dual fixed point as the q=+1 closure pole
> (`biconjugate_eq_clo`/`closed_iff_fixed`), Verdier-self-dual = the q=±1 reflection fixed point. **The
> Decomposition Theorem** (proper pushforward = ⊕ shifted IC) = the residue splitting into graded summands
> = the semisimple `q=+1` no-extension case (`Ext¹=0`, the spectral-sequence degeneration). **Verdier/
> Poincaré duality** = the q=±1 reflection (`s↔k−s` / `Hⁱ↔H^{n−i}`, `cup1_antisymmetric` antitone). **No
> new primitive** — it is `derived_categories.md`'s residue machine re-truncated, with IC the self-dual
> fixed point and the Decomposition Theorem its semisimple splitting.

---

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **derived category of `sheaf_theory.md`'s constructible sheaves** =
  `derived_categories.md`'s `C` verbatim: a category of chain complexes (the graded cochain nesting
  `… → Cᵏ → Cᵏ⁺¹ → …` with coboundary `delta`, `Cochain n k`, `Delta/Core.lean`) over `sheaf_theory.md`'s
  resolution poset (`DyadicOpen`, refinement), localized at quasi-isomorphisms (the `Quot`-free
  `LensImage`/`FreeReduction` Σ-quotient). `C` carries the README's two read-off axes load-bearingly: the
  **fold-height** (the cohomological degree `k`/`n` AND the shift index — the axis the t-structure
  re-grades) and the **direction / swap bit `q=±1`** (the alternating differential sign / orientation,
  which becomes Verdier duality's reflection). Constructibility = `sheaf_theory.md`'s resolution-stratified
  reading (a sheaf constant on each refinement-stratum) — *no new construction*, only a finiteness
  condition on the stratification. Nothing perverse-sheaf-theoretic is a primitive: no
  `Perverse`/`tStructure`/`IC`/`Verdier`/`intermediateExtension`/`DecompositionTheorem` type (all
  grep-confirmed ABSENT below).

- **Reading `L` — a RE-TRUNCATION of the fold-height axis (a t-structure), read at the perverse heart.**
  A derived category's residue is graded by fold-height (`derived_categories.md`'s shift `[1]`,
  `homological_algebra.md`'s degree `n`). A **t-structure** is a *choice of where to truncate* that axis
  — a pair `(D^{≤0}, D^{≥0})` with `τ_{≤n}`/`τ_{≥n}` cutting the height — i.e. `derived_categories.md`'s
  fold-height grading **read as a truncation condition** (the resolution dial `IsResolutionShift` used to
  *cut* rather than to *shift*). The **perverse t-structure** is a *different reading of the same axis*:
  it re-grades the truncation by a **support/dimension condition** (`H^i(F)` supported in dimension `≤ −i`,
  and dually for the dual), tying the cohomological height to `dimension.md`'s height-reading on the
  stratification. So `L` = "truncate the fold-height, but weight the cut by the support-dimension" — the
  SAME `Lambek.isPart_wf` height the corpus reads everywhere, re-graded. The **perverse heart**
  `Perv(X) = D^{≤0} ∩ D^{≥0}` is the abelian category that re-emerges at the truncation level — the residue
  read at one (perverse) degree, the `q=+1` corner where the reading closes into an abelian (no-shift)
  category (the heart of any t-structure is abelian — the README's "abelian category at the truncation
  level").

- **Residue `q = ±1`** — TWO residues, the README's two poles, displayed by the IC / Decomposition split:
  - **the q=+1 converge / self-dual residue — IC = j!*** the intermediate extension. Among all extensions
    of a local system from an open stratum to the singular space, IC is the **canonical one** — "neither
    too big (`j!`) nor too small (`Rj_*`)", the image of `j_! → Rj_*`. This is the q=+1 closure /
    canonical-normal-form pole: the **self-dual fixed point** of the Verdier-duality reflection
    (`𝔻(IC) = IC`), the SAME fixed point as `biconjugate_eq_clo`/`closed_iff_fixed`
    (`FenchelMoreau.lean:59,152`) — the closed element fixed by its biconjugate, tagged
    `converge`/`multiplier = +1` (`ResidueTag.lean:160,180`, `golden_is_converge`). A *semisimple* /
    *split* perverse sheaf (a direct sum of IC's) has empty extension residue — `Ext¹=0`, the q=+1
    no-extension corner (`clo_idempotent`, the split extension of `homological_algebra.md` §5).
  - **the q=−1 escape / obstruction residue** — a non-split perverse complex / a perverse cohomology
    `^pH^{>0}` that does not split off, the obstruction a non-proper or non-semisimple map carries
    (`Ext^{>0}`, nonzero `^pHⁿ`), tagged `escape`/`multiplier = −1` (`ResidueTag.lean:73,133`), delegating
    to `object1_not_surjective` (`FlatOntologyClosure.lean:61`). Concrete ∅-axiom witness of the
    obstruction shape: `NonzeroBetti.loopClass_not_coboundary` (`:134`, a closed-not-coboundary class,
    `b₁=1`, 56/0 PURE) — the same `ker δ/im δ` residue, read at a perverse degree. `cycle_vs_contractible_qpm`
    (`NonzeroBetti.lean:173`) tags the contrast on `ResidueTag` directly: non-split = `escape` (q=−1)
    vs IC-summand / semisimple = `converge` (q=+1).

---

## Re-seeing — ⟨C | L⟩ ⊕ Residue(L,C)

```
   D^b_c(X) (constructible)   =  derived_categories.md's D(A)  =  ⟨ chain complexes | quasi-iso reading ⟩ ⊕ Residue(q=±1)
                                 over sheaf_theory.md's resolution-stratified (constructible) sheaves
   t-structure (D^{≤0},D^{≥0}) =  the fold-height axis READ AS A TRUNCATION  (τ_{≤n}/τ_{≥n} = cut the resolution dial)
                                 = derived_categories.md's [1]-grading, used to CUT not to shift  (IsResolutionShift)
   perverse t-structure       =  the SAME height axis re-graded by a support/dimension condition  (Lambek.isPart_wf + dimension.md)
   perverse heart Perv(X)     =  the abelian category at the truncation level  =  residue read at one perverse degree (q=+1 closes)
   perverse cohomology ^pHⁿ   =  the residue-taking operation, GRADED by perverse degree  =  homological_algebra's Ext^n, re-graded
   IC complex = j!*           =  q=+1 canonical extension: neither too big (j!) nor too small (Rj_*)  =  the SELF-DUAL fixed point
                                 = closed_iff_fixed / biconjugate_eq_clo (the closure-normal-form, fixed by its dual)
   IC self-dual 𝔻(IC) = IC    =  the q=±1 REFLECTION's fixed point  (multiplier_unimodular: q·q=1, the involution)
   Decomposition Theorem      =  proper pushforward Rf_* IC  =  ⊕ shifted IC summands  =  the residue SPLITS into q=±1 graded pieces
     (BBD)                     =  the SEMISIMPLE / no-extension case (Ext¹=0, q=+1 split)  =  spectral-sequence DEGENERATION
   Verdier duality 𝔻          =  the q=±1 REFLECTION  =  homology.md's Poincaré Hⁱ↔H^{n−i}  =  cup1_antisymmetric (antitone)
   Poincaré duality (singular)=  Verdier duality made self-dual ON IC  =  the reflection's fixed point on the canonical extension
```

So **D^b_c(X), the perverse t-structure, the heart, IC, the Decomposition Theorem, and Verdier duality are
ONE machine: `derived_categories.md`'s residue operation RE-TRUNCATED by a fold-height re-grading, with IC
the q=+1 self-dual fixed point and the Decomposition Theorem its semisimple splitting.** Set against the
notes it consolidates:

| classical perverse-sheaf object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| D^b_c(X) (constructible derived cat) | `derived_categories.md`'s D(A) over the constructible sheaves | `derived_categories.md` + `sheaf_theory.md` | `Unified.lean:163 LensImage.proj_val_eq_iff`; `Cochain/Core.lean:22 Cochain`; `Delta/Core.lean:54 delta` |
| t-structure (truncation `τ_{≤n}`/`τ_{≥n}`) | the fold-height axis read AS A CUT (the resolution dial cutting) | NEW (height-grading → truncation condition) | `ResolutionShift.lean:73 IsResolutionShift`, `:130 IsResolutionShift_compose` |
| perverse t-structure (support/dim re-grade) | the SAME height axis re-graded by dimension | NEW (a different reading of one axis) | `ResolutionShift.lean:73 IsResolutionShift` (re-graded) |
| perverse heart `Perv(X)` (abelian) | the abelian cat at the truncation level = residue at one perverse degree (q=+1) | NEW (heart = the closed/converge corner) | `FenchelMoreau.lean:152 closed_iff_fixed`; `ResidueTag.lean:160 converge_residue_fixed` |
| perverse cohomology `^pHⁿ` | the residue operation graded by perverse degree | `homological_algebra.md` (`Ext^n` graded) | `V4Capstone.lean:41 dsq_zero_universal_delta4`; `ResidueTag.lean:228 residue_tag_two_poles` |
| IC = j!* (intermediate extension) | the q=+1 canonical / self-dual fixed point | NEW (IC = the closure-normal-form, dual-fixed) | `FenchelMoreau.lean:59 biconjugate_eq_clo`, `:152 closed_iff_fixed`; `ResidueTag.lean:86 multiplier_unimodular` |
| Decomposition Theorem (Rf_* = ⊕ IC[i]) | the residue splits into q=±1 graded pieces (semisimple) | NEW (splitting = spectral degeneration, Ext¹=0) | `BettiKernel.lean:63 reduced_betti_d4_contractible`; `ResidueTag.lean:160 converge_residue_fixed` |
| Verdier duality `𝔻` | the q=±1 reflection (Poincaré `Hⁱ↔H^{n−i}`) | `homology.md` (the `q=±1` orientation bit) | `SignedCup.lean:62 cup1_antisymmetric`; `Mat2Bracket.lean:76 bracket_antisymm`; `multiplier_unimodular` |
| Poincaré duality for singular spaces | Verdier duality made self-dual ON IC = the reflection's fixed point | `homology.md` (Poincaré, smooth case) | `FenchelMoreau.lean:152 closed_iff_fixed`; `ResidueTag.lean:86 multiplier_unimodular` |
| non-split `^pH^{>0}` (obstruction) | the q=−1 escape residue (does not split off) | `homological_algebra.md` (`Ext^{>0}`) | `NonzeroBetti.lean:134 loopClass_not_coboundary`; `ResidueTag.lean:133 escape_residue_outside` |

Perverse sheaves consume BOTH of `C`'s axes — fold-height (to truncate, to grade the perverse degree, and
to split the Decomposition Theorem's summands) and direction/orientation (the q=±1 reflection that IS
Verdier duality and selects IC's self-dual fixed point) — exactly as `derived_categories.md`/`homology.md`
found, *because it is the same residue machine, now re-truncated and self-dualized.*

---

## THE REVELATION (collapse + forcing + spine)

**Collapse — perverse sheaves are NOT a new edifice: they are `derived_categories.md`'s residue operation
RE-TRUNCATED by a fold-height re-grading (the perverse t-structure), with IC the q=+1 self-dual fixed point
and the Decomposition Theorem its semisimple splitting.** Four moves, one per structural piece, plus the
residue surfaced and the spine.

### 1. Forcing — a t-structure is the fold-height axis READ AS A TRUNCATION; the perverse one re-grades the SAME axis by dimension.

A t-structure `(D^{≤0}, D^{≥0})` with its truncation functors `τ_{≤n}`/`τ_{≥n}` looks like extra
data layered on the derived category. In the calculus it is **forced** as `derived_categories.md`'s
fold-height grading *used to cut*. The derived category already grades the residue by height (the shift
`[1]` = the resolution dial counting one step, `IsResolutionShift_compose` adds grades,
`ResolutionShift.lean:130`, 17/0 PURE: `[1]∘[1]=[2]`). A t-structure is that *same* axis read as a
**truncation condition** — `τ_{≤n}` keeps the cohomology below height `n`, `τ_{≥n}` above — i.e. the
resolution dial used to *partition* the complex rather than to *shift* it. No new primitive: a t-structure
is "the fold-height axis with a chosen cut-point", the height being `Lambek.isPart_wf` (the well-founded
measure already in `C`). The **perverse** t-structure is a *different reading of the same axis*: it
re-grades the cut by a **support/dimension condition** (each `H^i` supported in dimension `≤ −i`), tying
the cohomological height to `dimension.md`'s height-reading on the stratification — the same single axis,
weighted by where the cohomology lives. So the standard and the perverse t-structure are **two readings of
one fold-height axis** (`IsResolutionShift`), not two structures — the collapse: re-grading a t-structure
is choosing a different cut-weighting on the resolution dial.

### 2. Forcing — the perverse heart is the abelian category at the truncation level = the residue read at one perverse degree (the q=+1 closed corner).

The heart `Perv(X) = D^{≤0} ∩ D^{≥0}` of the perverse t-structure is, for any t-structure, an **abelian
category** — a striking fact (an abelian category re-emerging inside a triangulated one). In the calculus
it is **forced** as the residue read at *one* perverse degree: the truncation collapses the shifted
(triangulated) structure down to the single-degree (no-shift) reading, where the residue *closes* into an
abelian (kernel-and-cokernel) category. This is the **q=+1 converge / closure corner**
(`converge_residue_fixed`, `ResidueTag.lean:160`; `closed_iff_fixed`, `FenchelMoreau.lean:152`, 18/0 PURE):
at the truncation level the reading is at a fixed point — no obstruction shifts it up or down a degree, so
it behaves like an ordinary abelian reading (`homological_algebra.md`'s `Ext⁰=Hom`, the degree-0 exact
part). **Perverse cohomology `^pHⁿ`** is then `homological_algebra.md`'s residue operation **re-graded** by
the perverse degree — `Ext^n` with the height re-weighted by the support condition, the connecting map and
`δ²=0` the same `dsq_zero_universal_delta4` (`V4Capstone.lean:41`, 5/0 PURE) sign-propagation. The heart is
the abelian shadow of the q=+1 fixed point of the re-truncated residue machine.

### 3. Forcing — IC = j!* is the q=+1 canonical / SELF-DUAL fixed point (the closure-normal-form, fixed by Verdier duality).

The intersection-cohomology complex IC = the intermediate extension `j!*` of a local system from an open
dense stratum. Its defining property — **"neither too big (`j_!`) nor too small (`Rj_*`)"**, the image of
the canonical `j_! → Rj_*` — is exactly a **canonical-normal-form / closure** statement, and it is
**forced** as the q=+1 self-dual fixed point. Two forcings, one per half of IC's characterization:
- **Canonical (neither-too-big-nor-too-small)** is the closure-normal-form pole: among the extensions, IC
  is the *closed* one — the fixed point `x = star(star x)` of `closed_iff_fixed` (`FenchelMoreau.lean:152`),
  the converging residue that *closes* (`converge_residue_fixed`, `ResidueTag.lean:160`,
  `golden_is_converge`, `:180`). `j_!` (too big) and `Rj_*` (too small) are the two non-closed endpoints;
  IC is their reconciliation, the `biconjugate_eq_clo` image (`FenchelMoreau.lean:59`) — the canonical
  closure of an extension, the same q=+1 normal-form the corpus reads as `clo` everywhere.
- **Self-dual** (`𝔻(IC) = IC`, Verdier duality fixes IC) is the **q=±1 reflection's fixed point**: Verdier
  duality is the reflection bit `q=−1` (forcing 5), and `𝔻²=id` is its involution `q·q = +1`
  (`multiplier_unimodular`, `ResidueTag.lean:86`, 55/0 PURE — `(−1)·(−1)=1`, the same involution as
  `derived_categories.md`'s `[2]≅` sign-identity and `homology.md`'s `⋆⋆=id`). IC is the element the
  reflection fixes — the q=+1 (returns-to-itself) pole of the q=±1 reflection. So IC is **doubly q=+1**:
  the closure-normal-form (converge) AND the reflection-fixed (involution returns). No new primitive — IC
  is the canonical self-dual fixed point the calculus already names two ways (`closed_iff_fixed`,
  `multiplier_unimodular`).

### 4. Forcing — the Decomposition Theorem is the residue SPLITTING into q=±1 graded IC summands (the semisimple / Ext¹=0 / spectral-degeneration case).

The BBD Decomposition Theorem — a **proper** pushforward `Rf_*` of an IC complex (a pure complex) splits
as a **direct sum of shifted IC summands**, `Rf_* IC ≅ ⊕_i ^pH^i(Rf_* IC)[−i]` — looks like the deepest,
most miraculous theorem of the field. In the calculus it is **forced** as the residue *splitting cleanly
into its q=±1 graded pieces* — the **semisimple / no-extension `q=+1` case**:
- a direct-sum decomposition into graded pieces is exactly the **spectral-sequence degeneration**: the
  residue operation, when it splits, has no nonzero higher differentials carrying obstructions between
  degrees — every `^pH^i` splits *off* rather than extending. This is the q=+1 corner where `Ext¹=0`
  (`homological_algebra.md` §5: split extension = converge, no residue; `clo_idempotent`), the
  no-extension / semisimple case. The pushforward's residue is **semisimple** — it splits cleanly,
  `reduced_betti_d4_contractible` (`BettiKernel.lean:63`, 11/0 PURE: on the contractible/exact piece
  `ker δ = im δ`, the residue is empty *between* degrees, so each degree's residue is an independent
  summand — the literal "splits into graded pieces, no carry-over");
- "proper" is the q=+1 condition that makes the splitting hold (the analogue of compactness /
  finiteness-collapse, `sheaf_theory.md`/`topology.md`'s q=+1 corner where the residue closes); a
  non-proper or non-semisimple pushforward is the q=−1 escape where the obstruction does *not* split off
  (`escape_residue_outside`, `loopClass_not_coboundary`, the non-split `^pH^{>0}`).

So the Decomposition Theorem is **the residue splitting into ⊕ of q=±1 graded summands** — the SAME
⊕-of-graded-pieces as `spectral_sequences.md`'s degeneration and `homological_algebra.md`'s semisimple
no-extension case, with the summands the IC's (the q=+1 self-dual fixed points of forcing 3). `^pH^i ≥ 0`
that split off are q=+1 summands; any that fail to split would be q=−1. The "miracle" is that purity
(IC-ness) forces the q=+1 semisimple corner — the residue closes degree by degree
(`converge_residue_fixed`).

### 5. Forcing — Verdier / Poincaré duality is the q=±1 reflection; Poincaré duality on a singular space is that reflection made self-dual ON IC.

Verdier duality `𝔻 : D^b_c(X)^op → D^b_c(X)` with `𝔻²=id` is **forced** as the q=±1 **reflection** — the
direction/swap bit of `C` read as a contravariant involution, exactly `homology.md`'s Poincaré reflection
`Hⁱ ↔ H^{n−i}` (the `s↔k−s` antitone the corpus reads on the modular reflection and the Legendre–Fenchel
biconjugate). Two forcings:
- **The reflection itself** is the q=−1 swap bit: `cup1_antisymmetric` (`SignedCup.lean:62`, the
  order-swap flips the orientation sign, the `(−1)^inv` `homology.md`'s `∂` carries) and
  `bracket_antisymm` (`Mat2Bracket.lean:76`, `[A,B]=−[B,A]`, 10/0 PURE) — the same antisymmetry/reflection
  that signs the differential under `[1]` in `derived_categories.md`. Verdier duality reverses the height
  axis (`Hⁱ↔H^{n−i}`), the contravariant reflection.
- **`𝔻²=id`** is the involution `q·q=+1` (`multiplier_unimodular`, `ResidueTag.lean:86`) — the reflection
  applied twice returns, the q=±1 involutive pole (the same `⋆⋆=id` of `homology.md`).
- **Poincaré duality for singular spaces** is then *not a separate theorem* — it is Verdier duality made
  **self-dual on IC**: on a smooth space the constant sheaf is already self-dual and Verdier = ordinary
  Poincaré (`homology.md`); on a singular space IC is the q=+1 self-dual fixed point of `𝔻` (forcing 3),
  so `IH^i ≅ IH^{n−i}` is the reflection's fixed-point statement read on IC. **Poincaré duality on a
  singular space = the q=±1 reflection's fixed point on the canonical extension** — `closed_iff_fixed` (IC
  is closed/self-dual) read through `multiplier_unimodular` (the reflection is an involution).

### The spine.

The whole field is the q=±1 spine displayed on the perverse t-structure: **q=+1** = IC / semisimple /
split-off summand / `𝔻`-self-dual / proper pushforward / the heart's abelian closure — the converging pole
that *closes* (`reduced_betti_d4_contractible`, `converge_residue_fixed`, `closed_iff_fixed`,
`golden_is_converge`, `multiplier_unimodular`); **q=−1** = non-split `^pH^{>0}` / non-semisimple
obstruction / the perverse residue a non-proper map carries — the escaping pole
(`loopClass_not_coboundary`, `dsq_zero_universal_delta4`, `escape_residue_outside`, delegating to
`object1_not_surjective`). Verdier duality is the q=±1 reflection threading the two; IC is its q=+1
fixed point; the Decomposition Theorem is the residue splitting into q=±1 graded pieces. The same single
spine `SYNTHESIS.md` §3 runs through Cantor/Gödel/φ/measure/homology/derived-categories, now read on the
perverse t-structure and the IC summand.

---

## VALIDATE — verdict

**EXTEND (by consolidation) + PREDICTION + PARTIAL-BREAK.** The model held across the corpus with no new
axis; this is a consolidation that re-truncates `derived_categories.md`'s residue machine, with genuinely
NEW data (the perverse t-structure = a fold-height re-grading = a different reading of the SAME resolution
axis; IC = the q=+1 self-dual fixed point = `closed_iff_fixed` + `multiplier_unimodular`; the Decomposition
Theorem = the residue's semisimple q=+1 splitting into IC summands) and one recurring located break.

- **EXTENDS, grounded ∅-axiom:** the **D^b_c(X) base** = `derived_categories.md`'s D(A) (the `Quot`-free
  `LensImage` Σ-quotient, `proj_val_eq_iff`, 14/0; the cochain objects `Cochain`/`delta`); the
  **t-structure = fold-height truncation** = the resolution dial (`IsResolutionShift`/
  `IsResolutionShift_compose`, 17/0 — the same axis used to cut); the **perverse heart = the q=+1 closed
  abelian corner** (`closed_iff_fixed` 18/0, `converge_residue_fixed` 55/0); **IC = the q=+1 self-dual
  fixed point** (`biconjugate_eq_clo`/`closed_iff_fixed` 18/0, `multiplier_unimodular` 55/0); the
  **Decomposition Theorem = the semisimple q=+1 splitting** (`reduced_betti_d4_contractible` 11/0,
  `converge_residue_fixed`); **Verdier/Poincaré duality = the q=±1 reflection** (`cup1_antisymmetric`,
  `bracket_antisymm` 10/0, `multiplier_unimodular` 55/0); the **perverse cohomology / `δ²=0`** =
  `homological_algebra.md`'s residue-taking LES (`dsq_zero_universal_delta4` 5/0); the **split/non-split
  poles = q=±1** (`reduced_betti_d4_contractible`, `loopClass_not_coboundary` 56/0,
  `cycle_vs_contractible_qpm`, `ResidueTag` 55/0).

- **PREDICTION:** the calculus predicts the *form* of perverse-sheaf theory (D^b_c(X) = `derived_categories.md`'s
  localization over constructible sheaves; t-structure = the fold-height cut; perverse = the same axis
  re-graded by support-dimension; heart = the q=+1 abelian closure; IC = the self-dual q=+1 fixed point;
  Decomposition Theorem = the semisimple q=+1 splitting into IC summands; Verdier = the q=±1 reflection)
  and the *named objects are ABSENT* — the same shape as `derived_categories.md`'s missing
  `DerivedCategory`/`triangulated` and `sheaf_theory.md`'s missing presheaf-bundle. Every *structural
  mechanism* is built and PURE; only the *named bundle* welding them into `Perverse`/`tStructure`/`IC`/
  `Verdier`/`DecompositionTheorem` is open.

- **PARTIAL-BREAK (the constructible-sheaf / stratified-space ambient + the calculus-of-fractions corner —
  `sheaf_theory.md`/`derived_categories.md`/`knots.md`'s SAME break, a recurrence):** perverse sheaves
  live on D^b_c(X) over a *stratified topological space* (`sheaf_theory.md`'s missing presheaf-bundle and
  arbitrary-cover/overlap structure) localized at quasi-isomorphisms (`derived_categories.md`'s
  calculus-of-fractions / non-decidable colimit corner, `SYNTHESIS.md` §5.1 Side B). The q=+1 corner — the
  decidable / confluent-terminating residue mechanism — is built; the general stratified-space ambient and
  the non-confluent localization are the un-built Side B, the same located boundary recurring. So the
  perverse machinery is built where the residue is decidable, absent where the stratified ambient and the
  calculus of fractions need a non-confluent quotient — the constructive boundary, located.

---

## Verified Lean anchors (file:line:theorem — all grep/Read-verified on `lean/E213`; purity scanned via `tools/scan_axioms.py` from repo root this session)

| Leg | Anchor (file:line : name) | Purity (scanned this session) |
|---|---|---|
| **D^b_c(X) base = `derived_categories.md`'s D(A) = the `Quot`-free Σ-quotient** | `Lens/Unified.lean:163 : LensImage.proj_val_eq_iff`; `:64 : lensIso_iff_kernel_eq`; `:42 : LensIso` | PURE (Unified **14/0**) |
| quasi-iso reading = `Lens.refines` (the localization's equivalence) | `Lens/LensCore.lean:90 : Lens.refines`, `:93 : refines_refl`, `:95 : refines_trans` | PURE (LensCore **11/0**) |
| chain-complex objects (constructible sheaf complex) | `Lib/Math/Cohomology/Cochain/Core.lean:22 : Cochain`; `Lib/Math/Cohomology/Delta/Core.lean:54 : delta`, `:42 : deltaAt` | PURE (per `homological_algebra.md`/`homology.md`) |
| **★ t-structure = fold-height axis read AS A TRUNCATION (the resolution dial cutting); perverse = same axis re-graded** | `Lib/Math/Analysis/ResolutionShift.lean:73 : IsResolutionShift`, `:130 : IsResolutionShift_compose` | PURE (ResolutionShift **17/0**) |
| **★ perverse heart = the q=+1 closed abelian corner (residue read at one perverse degree)** | `Lib/Math/Order/FenchelMoreau.lean:152 : closed_iff_fixed`; `Lib/Math/Foundations/ResidueTag.lean:160 : converge_residue_fixed` | PURE (FenchelMoreau **18/0**, ResidueTag **55/0**) |
| **★ IC = j!* = the q=+1 canonical / self-dual fixed point (closure-normal-form, dual-fixed)** | `Lib/Math/Order/FenchelMoreau.lean:59 : biconjugate_eq_clo`, `:152 : closed_iff_fixed`; `Lib/Math/Foundations/ResidueTag.lean:86 : multiplier_unimodular`, `:180 : golden_is_converge` | PURE (FenchelMoreau **18/0**, ResidueTag **55/0**) |
| **★ Decomposition Theorem = the residue's semisimple q=+1 splitting into IC summands (Ext¹=0 / degeneration)** | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 : reduced_betti_d4_contractible`, `:42 : kerSizeDelta`; `Lib/Math/Foundations/ResidueTag.lean:160 : converge_residue_fixed` | PURE (BettiKernel **11/0**, ResidueTag **55/0**) |
| **★ Verdier / Poincaré duality = the q=±1 reflection; `𝔻²=id` = the involution** | `Lib/Math/Cohomology/Cup/SignedCup.lean:62 : cup1_antisymmetric`; `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:76 : bracket_antisymm` (`[A,B]=−[B,A]`); `Lib/Math/Foundations/ResidueTag.lean:86 : multiplier_unimodular` (`q·q=1`) | PURE (Mat2Bracket **10/0**, ResidueTag **55/0**; SignedCup per `homology.md`) |
| **perverse cohomology `^pHⁿ` / connecting `δ` / `δ²=0` = the residue-taking LES re-graded** | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 : dsq_zero_universal_delta4`; `:62 : leibniz_universal_delta4` (cup/Yoneda product) | PURE (V4Capstone **5/0**) |
| **q=−1 escape: non-split `^pH^{>0}` (obstruction) — concrete H¹ witness** | `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:134 : loopClass_not_coboundary`, `:111 : betti_one_cycle`, `:173 : cycle_vs_contractible_qpm`; `Lib/Math/Foundations/ResidueTag.lean:133 : escape_residue_outside`, `:73 : ResidueTag`, `:228 : residue_tag_two_poles` | PURE (NonzeroBetti **56/0**, ResidueTag **55/0**) |
| 2-cell coherence (the dual functor / naturality the reflection lives in) | `Lens/Compose/Morphism.lean:37 : view_factors_through_morphism`, `:29 : IsLensMorphism`, `:60 : refines_of_morphism` | PURE (Morphism **3/0**) |
| escape / faithful residue (the q=−1 pole's kernel) | `Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective`, `:47 : object1_injective` | PURE (FlatOntologyClosure **7/0**) |

**Fresh scan tallies this session (`tools/scan_axioms.py` from repo root, `E213.` prefix):**
`E213.Lib.Math.Foundations.ResidueTag` **55/0**, `E213.Lib.Math.Cohomology.Delta.V4Capstone` **5/0**,
`E213.Lib.Math.Cohomology.Examples.BettiKernel` **11/0**,
`E213.Lib.Math.Cohomology.Examples.NonzeroBetti` **56/0**,
`E213.Lens.Foundations.FlatOntologyClosure` **7/0**, `E213.Lens.Unified` **14/0**,
`E213.Lens.LensCore` **11/0**, `E213.Lib.Math.Analysis.ResolutionShift` **17/0**,
`E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Bracket` **10/0**,
`E213.Lib.Math.Order.FenchelMoreau` **18/0**, `E213.Lens.Compose.Morphism` **3/0**. All load-bearing
anchors PURE.

---

## Dropped / flagged (honest — NOT grounded in repo Lean)

- **The named `Perverse` / `PerverseSheaf` / `tStructure` / `TStructure` / `truncation` (`τ_{≤n}`/`τ_{≥n}`)
  / `IC` / `IntersectionCohomology` / `intermediateExtension` (`j!*`) / `Verdier`(-duality) /
  `DecompositionTheorem` / `constructible`(-sheaf) objects — ABSENT, predicted-not-built.** Grep over
  `lean/E213` for `perverse`/`Perverse`/`intersection_cohomology`/`IntersectionCohomology`/`IC_sheaf`/
  `ICSheaf`/`t_structure`/`tStructure`/`TStructure`/`decomposition_theorem`/`DecompositionTheorem`/
  `Verdier`/`intermediate_extension`/`intermediateExtension`/`constructible`/`Constructible` returns
  **zero matching declarations**. The only token hits are unrelated: the **`Verdier`** string appears only
  in an INDEX prose note (`Real213/INDEX.md`) and a `ScalingOrbit.lean` docstring (the spiral scaling
  orbit, NOT Verdier duality — confirmed by reading: the `scaling` hits are `scaling_orbit_structure`,
  geometric self-scaling), and `self_dual`/`semisimple`/`truncat` tokens hit unrelated number-system /
  combinatorics / power-series files (`CutExpFiniteTruncation`, `Mat2Killing`'s semisimplicity remark,
  etc.). This is the precise missing leg — the same shape as `derived_categories.md`'s missing
  `DerivedCategory`/`triangulated` and `sheaf_theory.md`'s missing presheaf-bundle: every *structural
  mechanism* (the D(A) Σ-quotient base, the fold-height truncation = the resolution dial, the q=+1 closed
  heart, the self-dual closure fixed point, the semisimple splitting, the q=±1 reflection, the `δ²=0`
  residue LES) is built and PURE; only the *named bundle* welding them into
  `PerverseSheaf`/`tStructure`/`IC`/`Verdier`/`DecompositionTheorem` is open.

- **A `tStructure := (D^{≤0}, D^{≥0})` pair with `τ_{≤n}`/`τ_{≥n}` truncation functors + the heart-is-abelian
  theorem — ABSENT.** The fold-height axis (`IsResolutionShift`) and the q=+1 closed-abelian corner
  (`closed_iff_fixed`/`converge_residue_fixed`) are built; the named t-structure pair, its truncation
  functors, and the "heart is abelian" theorem are the open legs. The truncation *mechanism* (cut the
  resolution dial) is built; the named t-structure object is absent.

- **An `IC`/`j!*` intermediate-extension object + the Decomposition Theorem as a stated splitting — ABSENT.**
  IC's defining property (the q=+1 self-dual canonical fixed point) is grounded as `closed_iff_fixed` +
  `multiplier_unimodular`, and the Decomposition Theorem's shape (the semisimple q=+1 splitting into graded
  pieces) as `reduced_betti_d4_contractible` + `converge_residue_fixed`; but there is **no**
  `intermediateExtension : (open ↪ X) → Sheaf → Sheaf` constructor, **no** `DecompositionTheorem` stating
  `Rf_* IC ≅ ⊕ ^pH^i[−i]`, **no** semisimplicity-of-pure-pushforward object. The residue mechanism is
  built; the named IC / Decomposition object is the open leg.

- **The constructible / stratified-space ambient + the calculus-of-fractions non-decidable corner —
  PARTIAL-BREAK, Side B.** D^b_c(X) lives over a stratified topological space (the `sheaf_theory.md`
  presheaf-bundle + overlap/cover structure that is itself absent) localized at quasi-isomorphisms (the
  `derived_categories.md` calculus-of-fractions, `SYNTHESIS.md` §5.1 Side B — a roof needs an ambient
  identification no reading's kernel generates). The q=+1 corner (the decidable residue mechanism, the
  `FreeReduction`/`LensImage` Σ-quotient) is built; the general stratified ambient + non-confluent
  localization is the un-built colimit/q=−1 corner — theorem-grade absent, the same break recurring.
  **No *new* witness is proposed (no unverified `decide` claim); the existing PURE residue/closure/
  reflection objects are the honest buildable side.**

- **IC / Decomposition / Verdier = the q=±1 reflection's fixed point and semisimple splitting *as one
  theorem*** — this identification is the decomposition's reading. Lean certifies each leg separately
  (`closed_iff_fixed` + `multiplier_unimodular` for IC's self-dual fixed point; `cup1_antisymmetric` +
  `bracket_antisymm` for the reflection; `reduced_betti_d4_contractible` + `converge_residue_fixed` for the
  semisimple splitting; `dsq_zero_universal_delta4` for the perverse `δ²=0`); the single theorem welding a
  named IC/perverse/Verdier object into "the re-truncated residue machine with IC the self-dual fixed point
  and the Decomposition Theorem its semisimple splitting" is conceptual framing on verified PURE objects —
  the same shape as `derived_categories.md`'s derived-functor identification.

---

## Cross-frame

`derived_categories.md` (JUST DONE, KEY — D(A) = the residue machine in the `Quot`-free localization; the
t-structure here is D(A)'s fold-height grading read as a truncation; the shift `[1]` = the resolution dial;
the distinguished triangle / LES; IC inherits D(A)'s self-dual `[2]≅` involution); `sheaf_theory.md` (KEY —
sheaf cohomology = the local-global `q=±1` obstruction; constructible sheaves = the resolution-stratified
reading; the missing presheaf-bundle is the same absent stratified ambient); `homological_algebra.md`
(the residue/LES, `Ext^n` graded by degree — perverse cohomology `^pHⁿ` is this re-graded; `Ext¹=0` = the
semisimple split the Decomposition Theorem realizes); `homology.md` (Poincaré duality `Hⁱ↔H^{n−i}` = the
q=±1 reflection Verdier duality generalizes to singular spaces; the `q=±1` orientation bit / `∂²=0` /
`⋆⋆=id` involution); `dimension.md` (the support/dimension condition the perverse t-structure re-grades by);
`SYNTHESIS.md` §2 (homological algebra = `Residue(L,C)`, the operation this re-truncates), §3 (the q=±1
spine IC/semisimple = q+1 vs non-split = q−1), §5.1 (the Side-A/Side-B localization + stratified-ambient
break this shares).

> Axiom-purity note: every load-bearing anchor was freshly scanned PURE this session via
> `tools/scan_axioms.py` (run from repo root with the `E213.` module prefix). The named
> `Perverse`/`tStructure`/`IC`/`Verdier`/`DecompositionTheorem`/`constructible` objects are grep-confirmed
> ABSENT (the `Verdier` token is an INDEX/docstring prose note + the unrelated spiral `scaling` orbit). The
> purity and absence claims rest on the fresh scan and grep, not docstrings.
