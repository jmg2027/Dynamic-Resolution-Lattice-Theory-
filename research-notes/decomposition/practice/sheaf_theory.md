# Decomposition: sheaf theory (presheaves, the gluing axiom, sections, stalks, sheaf cohomology / Čech, local-to-global)

*A FRESH decomposition per `../README.md` (model v7.1). Sheaf theory is the field that exists to manage
exactly the calculus's two load-bearing objects at once — a **reading that varies over a resolution
structure** (`continuity.md`/`topology.md`: open = resolution-stable fibre, restriction = refining the
resolution) and the **local-to-global obstruction residue** (`de_rham.md`: `H^{>0}` = the `q=±1` cohomology
gap). The consolidating hypothesis to TEST, not re-skin: a **presheaf** = a reading assigned compatibly
with restriction over the resolution poset; the **sheaf gluing axiom** = the calculus's
RESOLUTION-COMPATIBILITY made into a limit = the `q=+1` unique-amalgamation = `dhom_unique_pointwise`
initiality; **stalks** = the reading at the residue resolution (`reached_by_none.md`); **sheaf cohomology
`H*(X,F)`** = the `q=±1` local-global obstruction of `de_rham.md` (`H⁰` = the glued part `q=+1`, `H^{>0}` =
the `q=−1` escape). This note tests whether sheaf theory CONSOLIDATES topology + de_rham + resolution +
initiality under the model's two invariants — and locates the precise missing leg.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **resolution poset of `topology.md`/`continuity.md`**: the dyadic refinement
  tree, whose objects are the refinement-stable fibres `DyadicOpen := List DyadicBracket`
  (`DyadicOpen.lean:28`), ordered by refinement. Restriction `U ⊇ V` = *refining the resolution* (passing
  to a sub-bracket, raising the dyadic exponent). Nothing sheaf-theoretic is a primitive — only "the poset
  of narrowing regions and the act of refining one into a finer one". `C` here is identical to
  `topology.md`'s `C` and `de_rham.md`'s simplex/bracket `C`; the whole point of the decomposition is that
  sheaf theory adds **no new construction**, only a new *reading* of the same poset.

- **Reading `L` — a reading-varying-compatibly-with-restriction (a *presheaf*).** This is `continuity.md`'s
  resolution dial promoted one level: instead of one reading at one resolution, assign to **each** open
  `U` (each resolution-stable fibre) a reading `F(U)` — a value, a section, a piece of local data — and to
  each refinement `U ⊇ V` a **restriction map** `F(U) → F(V)` that is *functorial* (refining twice = refining
  once to the finer). A presheaf is therefore the calculus's reading slot indexed over the resolution
  poset:
  - **Presheaf** `F = ⟨ resolution poset (open sets) | a reading varying compatibly with restriction ⟩`.
    The functoriality `res_{V←U} ∘ res_{U} = res_V` is exactly `continuity.md`'s "the dial commutes with
    refinement" — `compose_modulus_eq` (`Continuity.lean:64`), modulus composes by sequential refinement
    `δ_g ∘ δ_f`. A presheaf is a reading whose *composition law over the poset* is the modulus-composition
    law. In 213 the **functorial restriction structure on the poset is built** (`IsResolutionShift`,
    `ResolutionShift.lean:73`: `g (dyadicCut M E) = dyadicCut M (E+E_g)` — a graded refinement endomap;
    `ContinuityOpenSet.preimage`/`IsDyadicOpen`, `ContinuityOpenSet.lean:65,69`: the preimage of a
    `DyadicOpen` is a region, the contravariant restriction), but **the presheaf as an assignment-object
    `U ↦ F(U)`** is conceptual (see Residue / verdict).
  - **Section** = a *value of the reading at a resolution* — `F(U)` is the local readings over `U`; a
    **global section** `F(X)` is a reading defined at the whole. In 213 a section is a bracket-pointing /
    a value hung at each bracket (`continuity.md`'s "a value at each narrowing input").
  - **The sheaf gluing axiom** = RESOLUTION-COMPATIBILITY made into a **limit**: given a cover `{Uᵢ}` of `U`
    and local sections `sᵢ ∈ F(Uᵢ)` that **agree on overlaps** (`sᵢ|_{Uᵢ∩Uⱼ} = sⱼ|_{Uᵢ∩Uⱼ}`), there is a
    **unique** global `s ∈ F(U)` restricting to each `sᵢ`. This is the equalizer/limit
    `F(U) → Π F(Uᵢ) ⇉ Π F(Uᵢ∩Uⱼ)`. The two demands — *existence* of the amalgamation and *uniqueness* —
    are the `q=+1` corner: the restriction-compatible family has a **fixed point** (the global section is
    the limit of the cover, its own amalgamation). Uniqueness is `dhom_unique_pointwise`
    (`UniversalDistinguishing.lean:103`) read on this poset: **any two readings out of the
    initial/generating object that agree on the generating local data agree everywhere** — the catamorphism
    is forced by its values on the pieces.

- **Residue — the `q=±1` tag of `de_rham.md`/`topology.md`, with the two faces of sheaf theory.**
  Read the restriction-compatible family's amalgamation; its surplus carries the tag:
  - **`q=+1` (converge / glue) — `H⁰` = GLOBAL SECTIONS.** When the compatible family glues uniquely, the
    reading **closes** at the limit: `H⁰(X,F) = F(X)` is the `q=+1` fixed point — the cover is its own
    amalgamation, exactly as `topology.md`'s cover "is its own finite subcover" (`heineBorel`,
    `Compactness.lean:42`). Gluing-uniqueness = `dhom_unique_pointwise`'s "the only arrow out of the
    initial object" (`q=+1`, `converge_residue_fixed`, `ResidueTag.lean:160`).
  - **`q=−1` (escape / the local-global obstruction) — `H^{>0}` = SHEAF COHOMOLOGY.** When compatible
    local data does **not** glue (or a closed section is not globally exact), the residue is the `q=−1`
    escape — *local readings forced by `F` that no global reading captures*. This is **literally
    `de_rham.md`'s residue**: `H^{>0}(X,F) = ker δ / im δ`, the coboundary's kernel-image gap
    (`reduced_betti_d4_contractible`, `BettiKernel.lean:63`; `delta`, `Delta/Core.lean:54`). Čech cohomology
    builds this gap *on the cover*: the Čech complex is the alternating restriction-difference reading over
    overlaps `Uᵢ∩Uⱼ∩…`, whose coboundary is `de_rham.md`'s `δ` (`dsq_zero_universal_delta4`,
    `V4Capstone.lean:41`), so `H^{>0}_Čech` is the count of overlap-cochains that close but do not glue.
    de Rham = the **constant-sheaf** cohomology — the special case `F = ℝ` (locally constant), tying
    `de_rham.md` to sheaf cohomology as one residue.
  - **Stalk / germ** = the reading **at the residue resolution**: `F_x = colim_{U∋x} F(U)`, the direct
    limit over shrinking neighbourhoods — `topology.md`'s/`continuity.md`'s **reached-by-none point**
    (`reached_by_none.md`; the `Real213` cut `Msup`, `ExtremeValue.lean:300`; `CauchyCutSeq.limit`). A
    stalk is the section read at the limit no finite open reaches — the residue of the
    refinement sequence, the same object `topology.md` named the limit point. The **étale space** is the
    bundle of these stalks over `X` — the family of residue-resolution readings, one per point.

## Re-seeing — ⟨C | L⟩

```
   open set U            =  ⟨ resolution poset | L_res's refinement-stable fibre ⟩  = List DyadicBracket (topology.md)
   restriction U ⊇ V     =  refining the resolution (sub-bracket / raise dyadic exponent)  = IsResolutionShift
   presheaf F            =  ⟨ resolution poset | a reading varying COMPATIBLY with restriction ⟩
                            functoriality res∘res = res  =  the dial commutes with refinement (compose_modulus_eq)
   section s ∈ F(U)      =  a value of the reading at resolution U  (a value hung at each bracket)
   GLUING AXIOM          =  compatible {sᵢ on Uᵢ, agree on Uᵢ∩Uⱼ}  ⟹  UNIQUE global s ∈ F(U)
                         =  the equalizer/limit  F(U) → ΠF(Uᵢ) ⇉ ΠF(Uᵢ∩Uⱼ)   (the q=+1 amalgamation)
                         =  dhom_unique_pointwise: the only reading out of the generating object, fixed by its local data
   H⁰(X,F)               =  Residue(restriction-family, C) at q=+1  =  global sections = the glued fixed point
   H^{>0}(X,F) (Čech)    =  Residue at q=−1  =  local data that does NOT glue  =  de_rham.md's ker δ/im δ (δ = delta)
   stalk F_x / germ      =  Residue(L_res) at q=−1  =  colim over shrinking nbhds  =  reached-by-none cut (Msup)
   étale space           =  the bundle of stalks  =  the family of residue-resolution readings over X
   de Rham               =  the CONSTANT-sheaf cohomology  =  H*(X,ℝ)  (ties de_rham.md as one residue)
   local-to-global SS    =  the resolution tower  (refinement levels stacked → the cohomology of the poset)
```

So **presheaf, gluing, section, stalk, sheaf cohomology are one reading at work** — the resolution dial of
`continuity.md`/`topology.md`, here indexed over the whole poset (presheaf), glued at the `q=+1` limit
(sheaf condition = `dhom_unique_pointwise` initiality), with its `q=−1` residue read on the cover
(`H^{>0}` = `de_rham.md`'s `ker δ/im δ`) and at the point (stalk = `topology.md`'s limit point). Sheaf
theory is the discipline that holds **`topology.md`'s resolution structure** and **`de_rham.md`'s
obstruction residue** in one frame, glued by **`category_theory.md`'s initiality**.

## LEVERAGE — does sheaf theory consolidate topology + de_rham + resolution + initiality?

**Verdict: PREDICTION + PARTIAL — a decisive *consolidation* of three already-built spines onto one
reading, with one genuinely absent leg located precisely (the presheaf-assignment / gluing object).** The
sheaf-theoretic skeleton falls out of three prior notes with NO new primitive; what is missing is the
*object* that would weld them — a presheaf `U ↦ F(U)` with restriction maps and a stated gluing theorem.
Leg by leg, honest.

**(1) Presheaf = restriction-compatible reading on the resolution poset — the resolution machine is built,
the assignment-object is not.** The poset (`DyadicOpen`, refinement), the contravariant restriction
(`ContinuityOpenSet.preimage`, `:69`: preimage pulls back along refinement), the *functoriality of
refinement* (`compose_modulus_eq`, `Continuity.lean:64`; `IsResolutionShift`, `ResolutionShift.lean:73`:
refinement is a graded endomap composing additively in the exponent) are all ∅-axiom built. This IS the
presheaf's *structure*. But there is **no Lean object `Presheaf := (U : DyadicOpen) → Reading` with a
`restrict : U ⊇ V → F U → F V` field and the functor laws** — the assignment is conceptual. This is the
sheaf-theory analogue of `topology.md`'s missing arbitrary-cover quantifier and `de_rham.md`'s missing
`Ω^k(M)` bundle: the *reading at one resolution* is built; the *bundle of readings over the whole poset* is
the named gap.

**(2) ★ The gluing axiom IS `dhom_unique_pointwise` initiality — the strongest leverage.** The sheaf
condition's load-bearing half is **uniqueness**: compatible local sections glue to a *unique* global
section. This is precisely `dhom_unique_pointwise` (`UniversalDistinguishing.lean:103`, PURE): *any two
distinguishing-homomorphisms `f g : DHom rawDStr N` agree at every `r : Raw`* — proved by induction on the
generating structure (`Raw.rec`), so a reading out of the initial/generating object is **forced by its
values on the pieces**. Read on the resolution poset: a global section is a reading over `X`; the cover
`{Uᵢ}` is the generating local data; two global sections agreeing on every `Uᵢ` agree everywhere — *exactly*
`dhom_unique_pointwise`'s "agree on the generators ⟹ agree". The sheaf condition's *existence* half (the
amalgamation exists) is the `raw_initial` existence leg (`SemanticAtom.lean:412`,
`universalMorphism` the catamorphism `Raw.fold`, `SemanticAtom.lean:108`) — the unique arrow out of the
initial object IS the glued global section. So **gluing = the universal property of the initial object on
the resolution poset**, the `q=+1` limit/amalgamation (`category_theory.md`: `raw_initial` +
`dhom_unique_pointwise` = the calculus's initiality). The equalizer diagram
`F(U) → ΠF(Uᵢ) ⇉ ΠF(Uᵢ∩Uⱼ)` is the limit-cone the initial object's universal property provides; the
overlap-agreement `⇉` is the naturality square `view_factors_through_morphism` (`Morphism.lean:37`,
restriction factors compatibly), and `refines_of_morphism` (`Morphism.lean:60`) is "a compatible family
induces the refinement (the 2-cell induces the 1-cell)". **The gluing axiom is the calculus's initiality,
read over the poset of resolutions** — this is the load-bearing collapse and it is Lean-grounded at the
*initiality* level (PURE), conceptual only at the *named sheaf object* level.

**(3) Stalk / germ = the residue resolution — the reached-by-none point, built.** `F_x = colim_{U∋x} F(U)`
is the reading at the limit no finite open reaches: `topology.md`/`continuity.md`'s limit point, the
`Real213` cut `Msup` (`ExtremeValue.lean:300`, PURE), `CauchyCutSeq.limit`, reached by no finite depth and
narrowed only by the modulus (`reached_by_none.md`). The germ is the section read at this residue; the
stalk is the calculus's `q=−1` reached-by-none residue (`object1_not_surjective`,
`FlatOntologyClosure.lean:61`) read on the section. The étale space (the bundle of stalks) is the family of
these residue-readings over `X` — built as a *concept* on the verified cut object, absent as a named
`EtaleSpace` bundle.

**(4) ★ Sheaf cohomology `H*(X,F)` = `de_rham.md`'s `q=±1` obstruction — `H⁰` glued, `H^{>0}` the residue.**
This is the `de_rham.md` consolidation made exact. `H⁰(X,F) = F(X)` = global sections = the `q=+1` glued
fixed point (the amalgamation closes). `H^{>0}(X,F)` = local data that does NOT glue = the `q=−1`
local-global obstruction = **`de_rham.md`'s `ker δ / im δ` verbatim**:
`reduced_betti_d4_contractible` (`BettiKernel.lean:63`, PURE: `kerSize 5 0 = 1`, `kerSize 5 1 = 2` ⟹ on
the contractible Δ⁴, `ker δ = im δ`, residue empty — no un-fillable closed cochain, i.e. local data always
glues on a contractible piece). The **Čech complex** is the alternating restriction-difference reading over
nerve-overlaps `Uᵢ∩…∩Uⱼ`, whose coboundary is `de_rham.md`'s `δ` (`delta`, `Delta/Core.lean:54`;
`dsq_zero_universal_delta4`, `V4Capstone.lean:41`, PURE: `δ²=0`), graded by the Leibniz/graded-relation
slot (`leibniz_universal_delta4`, `V4Capstone.lean:62`, PURE). **de Rham = the constant-sheaf cohomology**
(`F = ℝ` locally constant) — the de Rham theorem `H*_dR(X) ≅ H*(X,ℝ)` is then "the constant sheaf's
obstruction equals the form complex's", the same `q=±1` residue `de_rham.md` already ties to curvature via
Gauss–Bonnet. The **local-to-global spectral sequence** is the *resolution tower*: the cohomology of the
poset filtered by refinement level (`topology.md`'s dial, stacked) converging to `H*(X,F)` — the resolution
axis (`continuity.md`) made into a filtration. Lean has the **coboundary `δ` and its residue `ker/im`** (the
abstract Čech machine), PURE; it does **not** have the **nerve of a cover**, a **Čech complex of a
presheaf**, or the **spectral sequence** as named objects (Čech: grep-confirmed ABSENT).

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, freshly scanned PURE):* (a) the **resolution poset + functorial restriction** —
  `DyadicOpen` (`DyadicOpen.lean:28`), `size_union`/`dyadic_open_finite` (`:54,:64`),
  `IsResolutionShift` (`ResolutionShift.lean:73`), `ContinuityOpenSet.preimage`/`IsDyadicOpen`/
  `continuous_preimage_dyadicopen` (`ContinuityOpenSet.lean:69,65,83`), `compose_modulus_eq`
  (`Continuity.lean:64`); (b) the **gluing = initiality** engine — `dhom_unique_pointwise`
  (`UniversalDistinguishing.lean:103`), `raw_initial`/`universalMorphism` (`SemanticAtom.lean:412,108`),
  the naturality 2-cell `view_factors_through_morphism`/`refines_of_morphism` (`Morphism.lean:37,60`),
  `lensIso_iff_kernel_eq` (`Unified.lean:64`); (c) the **stalk residue** — `Msup`/`evt_sup`/`gridMax_attained`
  (`ExtremeValue.lean:300,362,275`), `object1_not_surjective` (`FlatOntologyClosure.lean:61`); (d) the
  **`H^{>0}` obstruction = `de_rham.md`'s `ker δ/im δ`** — `delta` (`Delta/Core.lean:54`),
  `dsq_zero_universal_delta4`/`leibniz_universal_delta4` (`V4Capstone.lean:41,62`),
  `reduced_betti_d4_contractible` (`BettiKernel.lean:63`); (e) the **`q=±1` tag** — `ResidueTag`/
  `escape_residue_outside`/`converge_residue_fixed`/`residue_tag_two_poles` (`ResidueTag.lean:73,133,160,228`);
  (f) the **discrete local-to-global telescope** — `gauss_conservation_telescope`
  (`TelescopingConservation.lean:152`, the divergence-theorem boundary-collapse, `de_rham.md`'s Stokes).
- *Conceptual-only / the precise missing leg (the `knots.md`/`topology.md`-style gap):* **the presheaf /
  sheaf / gluing OBJECT is ABSENT.** Grep over `lean/E213` for `sheaf`/`Sheaf`/`presheaf`/`Presheaf`/
  `stalk`/`Stalk`/`germ`/`Germ`/`etale`/`Etale`/`Cech`/`cech`/`nerve`/`Nerve` returns **zero Lean
  declarations** (the only hits are the unrelated `sophie_germain`/`germain_*` number-theory theorems and
  prose docstrings). There is **no** `Presheaf := (U) → Reading` assignment with a `restrict` field and
  functor laws; **no** `Sheaf` extending it with a stated gluing/equalizer theorem; **no** `Stalk`/colimit
  object; **no** `CechComplex`/nerve; **no** `SheafCohomology`. The closest existing object — the
  cover predicate `Compactness.IsCover := db ∈ cover` (`Compactness.lean:33`) — is **pointwise membership,
  not true `cutLe` containment** (its docstring defers containment to `Continuity.lean`), so even the cover
  cannot yet express overlaps `Uᵢ∩Uⱼ` (the equalizer's second arrow). This is the SAME shape as
  `topology.md`'s missing arbitrary-cover quantifier and `de_rham.md`'s missing smooth `Ω^k(M)` bundle: the
  *resolution structure*, the *initiality*, the *coboundary residue*, and the *cut-stalk* are each built and
  PURE; the **bundle-over-the-poset that is a presheaf, and the equalizer-statement that is the gluing
  axiom**, are the named open legs.

So: **PREDICTION on the consolidation (presheaf = restriction-compatible reading on the resolution poset;
gluing = `q=+1` unique-amalgamation = `dhom_unique_pointwise` initiality; stalk = residue resolution;
`H^{>0}` = `de_rham.md`'s `q=−1` obstruction), cashed at the structure/initiality/coboundary level; PARTIAL
because the presheaf/sheaf/gluing/Čech OBJECTS are absent — the named open legs, not hand-waves.**

## Revelation (consolidation: sheaf theory = topology + de_rham + resolution + initiality, one reading)

**Collapse — the presheaf, the sheaf gluing axiom, the stalk, and sheaf cohomology are ONE reading at the
calculus's two invariants, not four constructions.** Sheaf theory adds *no new `C` and no new `L`*: it
indexes the resolution dial over its own poset (presheaf), glues at the `q=+1` limit (gluing =
initiality), reads the residue at the point (stalk = limit) and on the cover (`H^{>0}` = obstruction). The
single forcing sentence, read at both poles:

- **`q=+1` (gluing = the amalgamation closes = initiality).** The sheaf condition demands a *unique*
  global section amalgamating a compatible family. Uniqueness is `dhom_unique_pointwise`: the only reading
  out of the generating object, forced by its local data; existence is `raw_initial`'s catamorphism. The
  global section is the **limit of the cover** — the `q=+1` converging residue (`converge_residue_fixed`),
  the exact dual of `topology.md`'s "the cover is its own finite subcover". **Gluing = the calculus's
  initiality read over the poset of resolutions.**
- **`q=−1` (sheaf cohomology = the obstruction escapes = `de_rham.md`'s residue).** When the compatible
  family does NOT glue, the surplus is `H^{>0}` = `ker δ / im δ` — `de_rham.md`'s coboundary residue
  verbatim (`reduced_betti_d4_contractible`), the `q=−1` escape (`escape_residue_outside`,
  `object1_not_surjective`). Čech `δ` = de Rham `δ` = one `delta` op (`dsq_zero_universal_delta4`); de Rham
  = the constant-sheaf case. The stalk is the same `q=−1` residue read at a point (the reached-by-none cut).

This passes the re-skin guard at the prediction bar: it does not re-describe sheaves — it **derives the
sheaf condition as initiality** (`dhom_unique_pointwise`, a PURE theorem the repo already proves for the
*generating* object) and **derives `H^{>0}` as `de_rham.md`'s obstruction** (one `delta`, one `q=±1` tag),
unifying sheaf theory with `topology.md` (the resolution poset and its `q=+1`/`q=−1` cover-residue),
`de_rham.md` (the constant-sheaf cohomology, `ker δ/im δ`), `category_theory.md`/`yoneda.md` (initiality =
the read-op, the unique arrow), and `reached_by_none.md` (the stalk = the residue resolution). Sheaf theory
is the field that **names the calculus's own normal form** `OBJECT = ⟨C | L⟩` *over a poset*: a presheaf is
"a reading over each resolution", a sheaf is "a reading whose local values determine the global one"
(initiality), sheaf cohomology is "the residue of that determination" (`q=±1`). The deepest line:
**`H⁰ = q=+1` glued part and `H^{>0} = q=−1` obstruction are the two poles of one `ResidueTag`** on the
local-global reading — the local-to-global principle IS the `q=±1` residue tag, now spanning topology,
de Rham, AND sheaf theory.

## Note for the technique

**No new primitive; the sharpest consolidation yet — sheaf theory is the *named home* of the calculus's two
invariants over a poset.** Sheaf theory does not extend model v7.1; it *fuses three of its prior fusions*:
- the **resolution dial over a poset** (`continuity.md`/`topology.md`) supplies the presheaf (a reading per
  open), restriction (refinement), and the stalk (the residue resolution);
- **initiality / the unique arrow out of the generating object** (`category_theory.md`/`yoneda.md`,
  `dhom_unique_pointwise`/`raw_initial`) supplies the gluing axiom (the `q=+1` unique amalgamation = a
  limit);
- the **`q=±1` coboundary residue** (`de_rham.md`/`ResidueTag.lean`) supplies sheaf cohomology
  (`H⁰` = `q=+1` glued, `H^{>0}` = `q=−1` obstruction = `ker δ/im δ`).

The lesson for the model: **the local-to-global principle is the `q=±1` residue tag read on a
presheaf** — gluing succeeds (`q=+1`) iff the obstruction `H^{>0}` (`q=−1`) vanishes, the SAME tag uniting
Cantor/Gödel/measure/topology/de_rham now made into the precise statement "does the compatible local data
glue?". And the gluing axiom being `dhom_unique_pointwise` confirms `yoneda.md`'s capstone from a new angle:
the calculus's normal form `OBJECT = ⟨C | L⟩` (an object is its bundle of readings) *is* the presheaf
`F : Open^op → Reading`, and the sheaf condition (local readings determine the global) is the calculus's
initiality. The one genuine absence — the presheaf-assignment/gluing/Čech object — is located precisely:
the differential-topology twin of `de_rham.md`'s missing smooth `Ω^k(M)` and `topology.md`'s missing
arbitrary-cover quantifier. **EXTEND by consolidation; no new axis; interior model v7.1 holds.**

---

## Verified Lean anchors (file:line — all grep/Read-verified on `lean/E213`; purity freshly scanned via `tools/scan_axioms.py` this session)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| resolution poset = refinement-stable fibres (the presheaf's *index*) | `Lib/Math/Geometry/Topology/DyadicOpen.lean:28 DyadicOpen`; `:54 size_union`; `:64 dyadic_open_finite` | ∅-axiom PURE ✓ (scanned) |
| **functorial restriction** (refine ∘ refine = refine; contravariant preimage) | `Lib/Math/Analysis/ResolutionShift.lean:73 IsResolutionShift`; `Lib/Math/Geometry/Topology/ContinuityOpenSet.lean:65 IsDyadicOpen`, `:69 preimage`, `:83 continuous_preimage_dyadicopen`; `Topology/Continuity.lean:64 compose_modulus_eq` | ∅-axiom PURE ✓ (ContinuityOpenSet scanned, all PURE) |
| **★ gluing axiom = initiality / unique amalgamation (`q=+1`)** | `Lens/Foundations/UniversalDistinguishing.lean:103 dhom_unique_pointwise`; `Lens/Foundations/SemanticAtom.lean:412 raw_initial`, `:108 universalMorphism` | ∅-axiom PURE ✓ (scanned) |
| gluing overlap-compatibility = naturality 2-cell (the equalizer's `⇉`) | `Lens/Compose/Morphism.lean:37 view_factors_through_morphism`; `:29 IsLensMorphism`; `:60 refines_of_morphism`; `Lens/Unified.lean:64 lensIso_iff_kernel_eq` | ∅-axiom PURE ✓ (scanned) |
| **stalk / germ = residue resolution (reached-by-none, `q=−1`)** | `Lib/Math/Analysis/ExtremeValue.lean:300 Msup`, `:362 evt_sup`, `:275 gridMax_attained`; `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective` | ∅-axiom PURE ✓ (prior, `topology.md`) |
| **★ `H^{>0}` (Čech/sheaf cohomology) = `de_rham.md`'s `ker δ/im δ` obstruction** | `Lib/Math/Cohomology/Delta/Core.lean:54 delta`, `:42 deltaAt`; `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 dsq_zero_universal_delta4`, `:62 leibniz_universal_delta4`; `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 reduced_betti_d4_contractible`, `:42 kerSizeDelta` | ∅-axiom PURE ✓ (V4Capstone, BettiKernel scanned) |
| **`H⁰`/`H^{>0}` = `q=+1`/`q=−1` poles of the local-global reading** | `Lib/Math/Foundations/ResidueTag.lean:73 ResidueTag`, `:133 escape_residue_outside`, `:160 converge_residue_fixed`, `:228 residue_tag_two_poles` | ∅-axiom PURE ✓ (scanned) |
| local-to-global telescope (discrete; = de Rham Stokes) | `Lib/Math/Analysis/FluxMVT/TelescopingConservation.lean:152 gauss_conservation_telescope` | ∅-axiom PURE ✓ (scanned) |
| cross-frame | `topology.md` (resolution poset, `q=±1` cover-residue, `heineBorel`), `de_rham.md` (`H*=ker δ/im δ`, constant-sheaf, Stokes), `continuity.md` (resolution dial), `category_theory.md`/`yoneda.md` (initiality = the read-op), `reached_by_none.md` (the residue resolution) | prior, ∅-axiom ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root):**
`Cohomology.Delta.V4Capstone`, `Cohomology.Examples.BettiKernel`, `Analysis.FluxMVT.TelescopingConservation`
— **24 pure / 0 dirty** combined; `Foundations.ResidueTag`, `Topology.DyadicOpen`, `Topology.Compactness`,
`Topology.ContinuityOpenSet` — **83 pure / 0 dirty** combined; `UniversalDistinguishing.dhom_unique_pointwise`,
`Compose.Morphism.{IsLensMorphism, view_factors_through_morphism, refines_of_morphism}`,
`Unified.lensIso_iff_kernel_eq` — **all PURE**. Build clean.

## Conceptual-only / absent legs (honest)

- **Presheaf / sheaf / stalk / Čech / sheaf-cohomology OBJECTS — ABSENT, located.** Grep over `lean/E213`
  for `sheaf`/`Sheaf`/`presheaf`/`Presheaf`/`stalk`/`germ`/`etale`/`Cech`/`nerve` (and capitalized variants)
  returns **zero Lean declarations** — only the unrelated `sophie_germain`/`germain_*` number-theory
  theorems and prose. There is no `Presheaf := (U : DyadicOpen) → Reading` assignment with a `restrict`
  field + functor laws; no `Sheaf` with a stated gluing/equalizer theorem; no `Stalk`/colimit object; no
  `CechComplex`/nerve; no `SheafCohomology`/spectral sequence. **This is the precise missing leg** — the
  bundle-over-the-poset (a presheaf) and the equalizer-statement (the gluing axiom). The *resolution
  structure* (`DyadicOpen`/`IsResolutionShift`/`ContinuityOpenSet`), the *initiality* that gluing reduces to
  (`dhom_unique_pointwise`/`raw_initial`), the *coboundary residue* `H^{>0}` (`delta`/`reduced_betti_*`),
  and the *cut-stalk* (`Msup`) are each built and PURE; the presheaf/sheaf/gluing object that would weld
  them is the named open target.
- **Overlap `Uᵢ∩Uⱼ` / true cover containment — ABSENT.** `Compactness.IsCover := db ∈ cover`
  (`Compactness.lean:33`) is pointwise membership, **not** `cutLe`-boundary containment (its docstring
  defers containment to `Continuity.lean`), so the cover cannot yet express overlaps — the equalizer's
  second arrow `⇉` (overlap-restriction) has no operand. Dual to `topology.md`'s missing arbitrary-cover
  quantifier.
- **de Rham comparison iso `H*_dR(X) ≅ H*(X,ℝ)` (constant-sheaf) — ABSENT** (inherited from `de_rham.md`:
  no smooth `Ω^k(M)` bundle). The *combinatorial* `ker δ/im δ` is built; the smooth/sheaf comparison iso is
  the `Real213`-cut residue, the same gap `de_rham.md`/`curvature.md` hit.
- **Gluing = initiality, stalk = residue, `H^{>0}` = de_rham residue *as one theorem*** — this
  identification is the decomposition's reading. Lean certifies each leg separately
  (`dhom_unique_pointwise`; `Msup`; `delta`/`reduced_betti_*`; `ResidueTag`); the single theorem welding a
  named presheaf object into "the resolution dial over a poset, glued by initiality, with `q=±1`
  obstruction" is conceptual framing on verified PURE objects.

> Axiom-purity note: every theorem cited was freshly scanned with `tools/scan_axioms.py` this session
> (run from repo root with the `E213.` module prefix); the purity claim rests on the fresh scan, not
> docstrings.
