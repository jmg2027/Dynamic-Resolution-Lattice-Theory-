# Decomposition: homological algebra / derived functors (exact sequences, the snake lemma, Ext/Tor, projective/injective resolutions, the long exact sequence, δ-functors)

*A FRESH decomposition per `../README.md` (model v7.1), consolidating `homology.md` + `de_rham.md` +
`sheaf_theory.md`. The consolidating hypothesis to **test**, not re-skin: homological algebra is the
**SYSTEMATIC NAME for the calculus's `q=±1`-residue-of-a-reading construction** — the operation
"take a reading, it fails to be exact, the failure IS the residue, graded by `n`". Concretely:
(i) a **derived functor `Ext^n`/`Tor_n`** = the `q=±1` RESIDUE of a non-exact functor (`Hom`, `⊗`):
`Ext⁰=Hom`/`Tor₀=⊗` is the `q=+1` exact part, `Ext^{>0}`/`Tor_{>0}` is the `q=−1` obstruction residue
— **the SAME residue as `sheaf_theory.md`'s `H^{>0}` and `de_rham.md`'s `H*_dR`**; (ii) the **long exact
sequence + the connecting map `δ`** = the `q=±1` sign-alternation propagating (`homology.md`'s `∂`,
`dsq_zero_universal_delta4`); (iii) **projective/injective resolutions** = approximating a reading by
exact (`q=+1`) pieces and reading off the residue — the **resolution dial** (`derivative.md`/
`continuity.md`) AT THE CHAIN-COMPLEX LEVEL (the word "resolution" is literally shared); (iv) **Ext as
the obstruction to splitting / extensions** = the `q=−1` residue classifying extensions, with group
cohomology `H*(G,M)` = `Ext` over the group ring (tying `galois.md`'s Gal-cohomology). This note tests
whether homological algebra NAMES THE RESIDUE-TAKING OPERATION ITSELF — the deepest consolidation, since
it is the machine that produces `homology`, `de_rham`, AND `sheaf` from one recipe.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **chain complex** = the *same* simplex/cochain nesting `homology.md`/
  `de_rham.md`/`sheaf_theory.md` read: a graded sequence `… → Cᵏ → Cᵏ⁺¹ → …` of distinguished cells with
  the boundary/coboundary `delta` between adjacent degrees (`Cochain n k`, `Delta/Core.lean`). `C`
  carries the README's two read-off axes: a **fold-height** (the degree `k`/`n`, the resolution index)
  and a **direction/orientation bit** (the alternating sign). A *resolution of an object `M`* is a
  height-indexed chain of **exact (`q=+1`) approximating pieces** mapping onto `M` — the resolution dial
  of `continuity.md`/`derivative.md` applied not to a number-modulus but to the complex itself: each
  degree is a finer approximation, the residue read off at the limit. Nothing classically homological is
  a primitive — `C` is the combinatorial graded complex + its `delta`; **no `Module`, no `Ab`, no
  abelian-category type, no `Hom`/`⊗` bifunctor object enters** (see Residue / verdict).

- **Reading `L` — a FUNCTOR that fails to be exact (a non-exactness reading).** This is the genuinely new
  framing the field supplies: the reading slot is occupied by a *functor applied to a resolution*. The
  classical recipe — "resolve `M` by exact `q=+1` pieces, apply a non-exact functor `F` (= `Hom(−,N)` or
  `−⊗N`), take homology of the result" — is, in 213 terms, exactly the calculus's residue recipe:
  - **`Hom(−,N)` / `−⊗N`** = a reading whose readout is itself a number-construction (the calculus's
    *character* family, `determinant.md`/`probability.md`): `Hom` is the contravariant pairing-reading,
    `⊗` the multiplicative/convolution-reading. In-repo the `⊗` *flavour* is real — `ConvolveProfile.conv`
    (`⋆`) is the Cauchy-convolution tensor on `Profile := List Nat`, with `mass_conv` (total mass
    multiplicative, `×↦·`) and `momentNum_conv` (mean additive, `×↦+`) — `generating_functions.md`'s
    "GF-product = convolution = the tensor of independents". But the **`Hom`/`⊗` bifunctor as a named
    object on a category of modules is ABSENT** (see verdict).
  - **Exactness** = the `q=+1` condition that two consecutive maps compose to zero *and the kernel is
    exactly the image* (`ker = im`, residue empty). A functor is **exact** iff applying it preserves this
    `ker=im` — i.e. iff its residue vanishes. `Hom` and `⊗` are **not exact**: applying them breaks
    `ker=im`, and the breakage is graded by `n`.
  - So the reading is: **apply `F` to a resolution, then read the `ker/im` residue degree by degree.**
    This is `homology.md`'s `Residue(L↓,C) = ker∂/im∂` with `L` = "the functor `F` composed with the
    resolution dial". The reading IS the residue-taking operation.

- **Residue — the `q=±1` tag of `homology.md`/`de_rham.md`/`sheaf_theory.md`, now GRADED by `n` and
  produced SYSTEMATICALLY.** Read the non-exact functor's failure; its surplus carries the tag, stratified
  by degree:
  - **`q=+1` (the exact part) — `Ext⁰ = Hom`, `Tor₀ = ⊗`.** In degree 0 the functor is exact: the residue
    is empty, the readout IS the functor itself. This is `galois.md`'s `clo`-fixed / converging pole
    (`clo_idempotent`, `converge_residue_fixed`) — the part that closes.
  - **`q=−1` (the obstruction residue) — `Ext^{>0}`, `Tor_{>0}`.** In positive degree the functor's
    failure to be exact IS the residue: closed-but-not-exact, "forced but not captured". This is
    **`de_rham.md`'s `H*_dR = ker d/im d` verbatim** and **`sheaf_theory.md`'s `H^{>0}` verbatim** —
    `ker δ/im δ` (`BettiKernel.reduced_betti_d4_contractible`: on the contractible/exact piece, `ker δ =
    im δ`, residue empty; a non-exact piece leaves nonzero `Ext^{>0}`). The `q=−1` escape
    (`escape_residue_outside`, `object1_not_surjective`).
  - **The connecting map `δ` / the long exact sequence** = the `q=±1` sign-alternation **propagating**
    along the complex: `…→Hⁿ→Hⁿ⁺¹→…` with `δ²=0` so that `ker=im` threads through. The connecting `δ`
    IS `homology.md`'s `∂`/`d` (one `delta` op), and `δ∘δ=0` (the long sequence's defining law) IS
    `dsq_zero_universal_delta4` — the orientation bits cancelling pairwise. The snake lemma's `δ` is the
    SAME sign-propagation across a short-exact "ladder".

## Re-seeing — ⟨C | L⟩

```
   chain complex C            =  ⟨ graded simplex/cells | the boundary delta between degrees ⟩  (homology.md's C)
   resolution of M            =  ⟨ C | the resolution DIAL at chain level ⟩  =  height-indexed exact (q=+1) approximants
                                 = continuity.md/derivative.md's resolution parameter, applied to the COMPLEX
   non-exact functor F (Hom,⊗) =  a reading whose readout is a number-construction (a character; ⊗ = ConvolveProfile.conv)
   exact  (ker = im)          =  the q=+1 condition: residue empty (reduced_betti_d4_contractible: ker δ = im δ)
   derived functor Ext^n/Tor_n =  Residue(F ∘ resolution, C), GRADED by n  =  the SYSTEMATIC q=±1-residue construction
   Ext⁰ = Hom,  Tor₀ = ⊗      =  the q=+1 EXACT part (degree 0; residue empty; the reading closes)
   Ext^{>0}, Tor_{>0}         =  the q=−1 OBSTRUCTION residue  =  de_rham.md's H*_dR  =  sheaf_theory.md's H^{>0}  =  ker δ/im δ
   connecting map δ (snake)   =  the q=±1 sign-alternation propagating  =  homology.md's ∂/d  (one delta op)
   "two consecutive maps ∘ = 0" =  ∂²=0  =  dsq_zero_universal_delta4  (orientation bits cancel pairwise)
   long exact sequence        =  δ threads ker=im across degrees;  δ²=0 forces it  (dsq_zero)
   Ext¹ = extensions mod split =  the q=−1 residue classifying NON-split extensions (split = q=+1, no residue)
   group cohomology H*(G,M)   =  Ext over the group ring  =  the Aut-family (groups.md) cohomology  (galois.md tie)
   δ-functor (universal)      =  the family {Ext^n}ₙ with the long-exact δ  =  the residue-taking operation, axiomatized
```

So **derived functor, resolution, the long exact sequence, the connecting `δ`, and Ext-as-extensions are
ONE machine** — the calculus's `Residue(L,C)` recipe, with `L` = "a non-exact functor composed with the
resolution dial", graded by degree and tagged `q=±1`. Set against the three notes it consolidates:

| classical homological-algebra object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| derived functor `Ext^n`/`Tor_n` | `Residue(F∘resolution, C)`, graded `q=±1` | NEW (the residue-recipe NAMED) | (conceptual object; legs below) |
| `Ext⁰=Hom`, `Tor₀=⊗` (exact part) | the `q=+1` part: `ker=im`, residue empty | `homology.md` (contractible ⇒ `b̃=0`) | `reduced_betti_d4_contractible` |
| `Ext^{>0}`/`Tor_{>0}` (obstruction) | the `q=−1` residue = `ker δ/im δ` | `de_rham.md` (`H*_dR`), `sheaf_theory.md` (`H^{>0}`) | `BettiKernel.kerSizeDelta`, `delta` |
| connecting `δ` / long exact seq | `q=±1` sign-propagation = `∂`/`d` | `homology.md` (`∂`), `de_rham.md` (`d`) | `Delta/Core.delta` |
| `δ²=0` ("two consecutive ∘ = 0") | orientation bits cancel pairwise (`q=−1`) | `homology.md` (`∂²=0`) | `dsq_zero_universal_delta4` |
| resolution (proj/inj) | the resolution dial at chain level | `continuity.md`/`derivative.md` (resolution) | `compose_modulus_eq`, `ResolutionShift` |
| Ext¹ = extensions mod split | `q=−1` residue (split = `q=+1`) | `galois.md` (closure = `q=+1`) | `clo_idempotent`, `ResidueTag` |
| group cohomology = `Ext_{ℤG}` | `Aut`-family cohomology (`q=±1` residue) | `groups.md`, `galois.md` | `PermGroup.composeList`; cocycle: `MinkowskiCocycle` |
| δ-functor universality | the residue-taking op, axiomatized | NEW (the operation itself) | `ResidueTag.residue_tag_two_poles` |

Homological algebra consumes BOTH of `C`'s axes (height to move degree along the resolution, direction to
sign the `δ`) — exactly as `homology.md`/`de_rham.md` found, *because it is the machine that produces
both*.

## LEVERAGE — does homological algebra NAME the calculus's systematic `q=±1`-residue construction?

**Verdict: PREDICTION + PARTIAL — possibly the deepest consolidation in the notebook, because it does not
add a field, it NAMES THE RESIDUE-TAKING OPERATION the calculus has been running all along.** Homology,
de Rham, and sheaf cohomology were three *instances* of `Residue(L,C)`; homological algebra is the
*recipe* that produces all three — "take a reading, it fails to be exact, the failure IS the residue,
graded by `n`". The structural skeleton + every load-bearing residue-mechanism leg is already ∅-axiom; the
*named derived-functor objects* (`Ext`, `Tor`, a resolution, an exact sequence) are ABSENT — the precise
missing leg, located like `knots.md`/`sheaf_theory.md`. Leg by leg, honest.

**(1) ★ The derived-functor RECIPE = the calculus's `Residue(L,C)` — this is the consolidation, and it is
the residue-mechanism, not a new edifice.** The classical definition "resolve, apply a non-exact functor,
take `ker/im` homology" is, term-for-term, `homology.md`'s `Residue(L↓,C) = ker∂/im∂` with `L` = "the
functor composed with the resolution". The calculus *already takes this residue* — every cohomology note
is one application. So derived functors are not a new object to build; they are the **name for what
`Residue(L,C)` does when `L` is a non-exact functor**. The `q=±1` grading is the residue tag
(`ResidueTag`, `residue_tag_two_poles`, `:228`): `Ext⁰/Tor₀` is the `q=+1` exact/converge part
(`converge_residue_fixed`, `:160`), `Ext^{>0}/Tor_{>0}` the `q=−1` escape (`escape_residue_outside`,
`:133`, → `object1_not_surjective`). This is the README's residue-first normal form `⟨C|L⟩ ⊕ Residue(L,C)`
made into a *systematic operation*: the field's whole content is "compute the residue degree by degree".

**(2) ★ `Ext^{>0}/Tor_{>0}` = the obstruction residue = `de_rham.md`'s `H*_dR` = `sheaf_theory.md`'s
`H^{>0}` — VERBATIM, one Lean residue.** The positive-degree derived functor is exactly closed-not-exact
= "forced (cocycle) but not captured (not a coboundary)" = `ker δ/im δ`. This is *the same `ker/im`
residue* `de_rham.md` cashed (`H*_dR`) and `sheaf_theory.md` cashed (`H^{>0}`, the local-global
obstruction). Grounded by `BettiKernel.reduced_betti_d4_contractible` (`:63`, **PURE, scanned 16/0 with
the V4Capstone batch this session**: `kerSize 5 0 = 1`, `kerSize 5 1 = 2` ⟹ on the contractible/exact
Δ⁴, `ker δ = im δ`, residue empty — a *resolution by exact pieces leaves no Ext*). A non-exact piece would
leave nonzero `Ext^{>0}`. The coboundary is `delta` (`Delta/Core.lean:54`), one op shared with homology,
de Rham, Čech. **Ext^{>0}/Tor_{>0}, de Rham `H^{>0}`, and sheaf `H^{>0}` are one `q=−1` residue computed
by one `delta`.**

**(3) ★ The connecting map `δ` / long exact sequence / `δ²=0` = `homology.md`'s `q=±1` sign-propagation
(`dsq_zero_universal_delta4`), PURE.** The task's structural anchor, confirmed: the snake lemma's
connecting map and the long exact sequence's coboundaries are `homology.md`'s `∂`/`de_rham.md`'s `d` — one
`delta` op, the alternating face-reading. The defining law "two consecutive maps in a complex compose to
zero" (`im ⊆ ker`, what makes a sequence a *complex*) IS `∂²=0` = `dsq_zero_universal_delta4`
(`V4Capstone.lean:41`, **PURE, scanned this session**: `∀ σ, ∀ i, δ(δσ) i = false` at strata (5,1),(5,2),
(5,3)) — the orientation bits cancelling pairwise, the `q=−1` direction-bit at a two-step composite. The
*long exact* sequence is then the statement that, threaded through the degrees, `ker = im` at each spot
except where the residue (the derived functor) lives — the residue is precisely the *failure of
exactness* the long sequence makes visible. So the long exact sequence is the calculus's `q=±1` residue
tag, *displayed degree by degree*; the connecting `δ` is the sign-alternation carrying it between
degrees. The graded-relation companion `leibniz_universal_delta4` (`V4Capstone.lean:62`, PURE — the
cup-product Leibniz, `two_cells.md`'s slot) is the multiplicative structure on `Ext` (the Yoneda/cup
product), the same shape.

**(4) Projective/injective resolutions = the resolution dial at chain level — the structure is built, the
chain-resolution object is not.** "Resolution" is the word *both* fields use, and it is the same object:
`continuity.md`/`derivative.md`'s resolution parameter (approximate by finer pieces, read the residue at
the limit) applied to the *complex* — a height-indexed chain of exact (`q=+1`) approximants mapping onto
`M`. The resolution *machinery* is ∅-axiom built: `compose_modulus_eq` (`Continuity.lean:64`, the dial
composes by sequential refinement), `IsResolutionShift` (`ResolutionShift.lean:73`, a graded refinement
endomap composing additively in the exponent). A projective resolution is "refine by free/exact pieces
until the residue stabilizes" — the resolution dial whose successive stages are exact. But there is **no
Lean `Resolution := chain of exact approximants` object with a `quasi-iso` to `M`** — the assignment is
conceptual, the same shape as `sheaf_theory.md`'s missing presheaf-bundle. The resolution *parameter* is
built and PURE; the *chain-resolution as a named complex* is the open leg.

**(5) Ext¹ = extensions mod split = the `q=−1` residue; split = `q=+1` (no residue) — grounded at the
tag/closure level.** An extension `0→A→E→B→0` *splits* iff it is the trivial (direct-sum) one; `Ext¹(B,A)`
classifies extensions modulo splitting. In the calculus: a **split** extension is the `q=+1` converging /
closure pole — it *closes* into a direct sum, residue empty (`clo_idempotent`, `GaloisConnection.lean:126`;
`converge_residue_fixed`). A **non-split** extension is the `q=−1` escape — the obstruction that cannot be
captured by a splitting (`escape_residue_outside`). So `Ext¹` is exactly the `q=±1` residue tag read on
"does this extension split?" — the SAME tag uniting Cantor/Gödel/φ/measure/topology/de Rham/sheaf, now
the statement "does the short exact sequence split?". `H⁰ = q=+1` glued (split), `H¹ = q=−1` obstruction
(non-split) — `sheaf_theory.md`'s `H⁰/H^{>0}` poles read on extensions. Grounded as the residue tag
(`ResidueTag.lean`, PURE), conceptual at the `Ext¹`/extension-object level.

**(6) Group cohomology `H*(G,M)` = `Ext` over the group ring = the `Aut`-family cohomology — `groups.md`/
`galois.md` tie, cocycle machinery partially present.** `H*(G,M) = Ext^*_{ℤG}(ℤ,M)` is the derived functor
of `M ↦ M^G` (invariants) — the `Aut`-family of `groups.md` read cohomologically. The `Aut`-family realization
is built (`PermGroup.composeList`, the composition-closed reading-family); the **cocycle/coboundary
machinery exists in a related setting** — `MinkowskiCocycle.lean` (the `q=±1` modular cocycle, the period
relations) — but there is **no `GroupCohomology`/`groupRing`/`Ext_{ℤG}` object** (grep: `groupCohomology`/
`GroupCohomology`/`groupRing` return zero declarations; the cohomology coboundary `delta` is the
simplicial one). This ties `galois.md`'s "Galois cohomology" leg: the `H¹(G,M)` that classifies forms /
torsors is the `q=−1` obstruction residue of the invariants-functor, the cohomological face of the Galois
connection's closure gap. Conceptual at the group-ring/Ext level; the residue mechanism and the
`Aut`-family are built.

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, scanned PURE this session):* (a) the **residue mechanism `ker δ/im δ`** that IS the
  derived functor — `delta` (`Delta/Core.lean:54`), `dsq_zero_universal_delta4` / `leibniz_universal_delta4`
  (`V4Capstone.lean:41,62`), `reduced_betti_d4_contractible` / `kerSizeDelta` (`BettiKernel.lean:63,42`)
  [V4Capstone+BettiKernel **16 pure / 0 dirty**, scanned]; (b) the **`q=±1` tag** that grades it —
  `ResidueTag` / `escape_residue_outside` / `converge_residue_fixed` / `residue_tag_two_poles`
  (`ResidueTag.lean:73,133,160,228`), `multiplier_unimodular` (`:86`); (c) the **exact part / wedge sign** —
  `cup1_antisymmetric` / `mergeSign = (−1)^inv` / `signed_cup_capstone` (`SignedCup.lean:62,52,148`, the
  `q=−1` orientation the `δ` carries); (d) the **resolution dial** — `compose_modulus_eq` (`Continuity.lean:64`),
  `IsResolutionShift` (`ResolutionShift.lean:73`); (e) the **`q=+1` closure** (split = converge) —
  `clo_idempotent` / `clo_extensive` (`GaloisConnection.lean:126,107`), `biconjugate_eq_clo` /
  `biconj_idempotent` / `closed_iff_fixed` (`FenchelMoreau.lean:59,134,152`); (f) the **`⊗`-flavour reading** —
  `ConvolveProfile.conv`/`⋆`, `mass_conv` (`×↦·`), `momentNum_conv` (`×↦+`) [`generating_functions.md`];
  (g) the **initiality / uniqueness** (resolution's quasi-iso content) — `dhom_unique_pointwise`
  (`UniversalDistinguishing.lean:103`), `raw_initial` / `universalMorphism` (`SemanticAtom.lean:412,108`);
  (h) the **`Aut`-family** (group cohomology's group) — `PermGroup.composeList`; (i) the **`q=±1` modular
  cocycle** — `MinkowskiCocycle.lean`; (j) the **escape/faithful residue** —
  `object1_not_surjective` / `object1_injective` (`FlatOntologyClosure.lean:61,47`).
- *Conceptual-only / the precise missing leg (the `knots.md`/`sheaf_theory.md`-style gap): the
  derived-functor OBJECTS are ABSENT.* Grep over `lean/E213` for `Ext`/`Tor`/`ProjectiveResolution`/
  `InjectiveResolution`/`deltaFunctor`/`DeltaFunctor`/`longExact`/`LongExact`/`connectingMap`/`snakeLemma`/
  `shortExact`/`ShortExact`/`isExact`/`IsExact`/`derivedFunctor`/`groupCohomology`/`groupRing` returns
  **zero Lean declarations** (the only `Ext` hit is a *filename note* — a "Legendre Pisano `Ext` variant"
  in `DyadicFSM/INDEX.md`, unrelated). There is **no** `Hom`/`⊗` *bifunctor on a category of modules*, **no**
  `Resolution` chain object with a quasi-iso to `M`, **no** `ShortExactSequence`/`LongExactSequence` /
  `ExactSeq` type, **no** `SnakeLemma`/`connectingMap`, **no** `Ext^n`/`Tor_n` as a graded object, **no**
  `δ-functor`/universality, **no** `GroupCohomology`/`Ext_{ℤG}`. This is the SAME shape as `sheaf_theory.md`'s
  missing presheaf-bundle and `de_rham.md`'s missing `Ω^k(M)` bundle: the *residue mechanism* (`ker δ/im δ`),
  the *grading tag* (`q=±1`), the *exact/`q=+1` part* (`ker=im`/closure), the *connecting `δ`* (`delta`,
  `dsq_zero`), and the *resolution dial* are each built and PURE; the **derived-functor objects that would
  weld them into a named `Ext^n`/`Tor_n`** are the named open legs.

So: **PREDICTION on the consolidation (a derived functor = the systematic `q=±1` residue of a non-exact
reading, graded by `n`; `Ext⁰/Tor₀` = `q=+1` exact part; `Ext^{>0}/Tor_{>0}` = `q=−1` obstruction =
`de_rham`/`sheaf` `H^{>0}`; connecting `δ` = `dsq_zero` sign-propagation; resolution = the resolution dial
at chain level; `Ext¹` = the split/non-split `q=±1` residue; group cohomology = `Aut`-family `Ext`), cashed
at the residue-mechanism / grading-tag / resolution-dial level; PARTIAL because the `Ext`/`Tor`/resolution/
exact-sequence/snake OBJECTS are absent — the named open legs, not hand-waves.**

## Revelation (consolidation: homological algebra = the calculus's residue-taking operation, made systematic and graded)

**Collapse — homology, de Rham, sheaf cohomology, and "derived functor" are ONE machine: the calculus's
`Residue(L,C)` recipe, with the field NAMING THE OPERATION ITSELF.** The earlier three notes each *took a
residue* — `homology.md` took `Residue(L↓,C)`, `de_rham.md` `Residue(L↑,C)`, `sheaf_theory.md` the
local-global `Residue`. Homological algebra is what you get when you stop taking residues one at a time and
**name the recipe**: *resolve (the resolution dial), apply a non-exact reading (`Hom`/`⊗`/invariants), read
the `ker δ/im δ` residue degree by degree, tag it `q=±1`.* The single forcing sentence, read at both poles:

- **`q=+1` (the exact part = the residue closes = `Ext⁰`/`Tor₀`).** In degree 0 the reading is exact —
  `ker=im`, residue empty, the readout IS the functor (`Hom`, `⊗`). This is the converging/closure pole
  (`converge_residue_fixed`, `clo_idempotent`); a *split* extension and a *resolution by exact pieces* both
  sit here (`reduced_betti_d4_contractible`: exact ⇒ `ker δ = im δ` ⇒ no `Ext`). The `q=+1` corner is "the
  reading captures everything; no obstruction".
- **`q=−1` (the obstruction = the residue escapes = `Ext^{>0}`/`Tor_{>0}`).** In positive degree the
  reading's failure to be exact IS the residue: closed-not-exact, `ker δ/im δ`, "forced but not captured"
  (`escape_residue_outside`, `object1_not_surjective`). This is **`de_rham.md`'s `H*_dR` and
  `sheaf_theory.md`'s `H^{>0}` verbatim** — one `delta`, one `q=±1` tag. The connecting `δ` propagating it
  between degrees is `dsq_zero_universal_delta4` (the long exact sequence = the residue tag displayed degree
  by degree).

This passes the re-skin guard at the deepest level the notebook has reached: it does not re-describe Ext/Tor
— it **identifies the derived-functor construction with the calculus's own residue-taking operation**
(`Residue(L,C)`, the residue-first normal form the README has run since batch 4), grounded by the *same*
PURE `ker δ/im δ` mechanism (`reduced_betti_d4_contractible`, `delta`, `dsq_zero_universal_delta4`) and the
*same* `q=±1` tag (`ResidueTag`) that already certify homology, de Rham, and sheaf cohomology. The deepest
line: **homological algebra is the SYSTEMATIC NAME for "take a reading, read its `q=±1` residue, graded by
degree" — the machine that produces `homology` + `de_rham` + `sheaf` from one recipe.** `Ext⁰=Hom`/`Tor₀=⊗`
is the `q=+1` part of that machine; `Ext^{>0}`/`Tor_{>0}` is its `q=−1` part; the connecting `δ` is the
sign-alternation threading the two; a resolution is the resolution dial feeding it; `Ext¹` is the
split/non-split residue; group cohomology is the `Aut`-family fed through it. **The field names the
residue-taking operation the calculus has been performing all along** — which is why this is the deepest
consolidation: not another instance of `Residue(L,C)`, but the *recipe* `Residue(−,−)` itself, made
systematic and graded. **EXTEND by consolidation; no new axis; interior model v7.1 holds.** The one genuine
absence — the `Ext`/`Tor`/resolution/exact-sequence object — is located precisely: the abelian-category
twin of `sheaf_theory.md`'s missing presheaf-bundle and `de_rham.md`'s missing `Ω^k(M)`, the named
derived-functor object that would weld the (all-built) residue-mechanism into a graded `Ext^n`/`Tor_n`.

## Note for the technique

**No new primitive; the deepest consolidation yet — homological algebra is the calculus's residue-taking
operation, NAMED.** It does not extend model v7.1; it *names the operation v4 introduced* (`Residue(L,C)`,
batch 4 `homology.md`):
- the **resolution dial** (`continuity.md`/`derivative.md`) supplies the resolution (proj/inj), the chain
  of exact approximants;
- the **non-exact reading** (`Hom`/`⊗`, a character; `ConvolveProfile`) is the functor whose failure is read;
- the **`q=±1` coboundary residue** (`homology.md`/`de_rham.md`/`sheaf_theory.md`/`ResidueTag`) supplies the
  derived functor (`Ext⁰/Tor₀ = q=+1` exact, `Ext^{>0}/Tor_{>0} = q=−1` obstruction = `ker δ/im δ`), with the
  connecting `δ` = the sign-propagation (`dsq_zero`).

The lesson for the model: **"derived functor" is the name for the residue-taking operation `Residue(L,C)`
when `L` is a non-exact functor and the residue is graded by degree.** Homology, de Rham, sheaf cohomology
are three *outputs* of this one machine; the long exact sequence is the `q=±1` tag *displayed degree by
degree*; the connecting `δ` is the sign-alternation between degrees (`dsq_zero`). This is the sharpest
confirmation that the README's residue-first normal form `⟨C|L⟩ ⊕ Residue(L,C)` is not a description but an
*operation* — homological algebra is the discipline that does nothing *but* run it, systematically, graded.
The one genuine absence — the `Ext`/`Tor`/resolution/exact-sequence/snake object — is located precisely: the
abelian-category twin of `sheaf_theory.md`'s presheaf-bundle and `de_rham.md`'s smooth `Ω^k(M)`. Every leg
the object would need *structurally* — the `ker δ/im δ` residue, the `δ²=0` complex law, the `q=±1` grading,
the resolution dial, the `q=+1` split/closure — is present and PURE; only the named graded object is open.

---

## Verified Lean anchors (file:line — all grep/Read-verified on `lean/E213`; purity scanned via `tools/scan_axioms.py` this session)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| **★ derived functor = `Residue(L,C)` graded `q=±1` (the residue-recipe NAMED)** | `Lib/Math/Foundations/ResidueTag.lean:73 ResidueTag`, `:86 multiplier_unimodular`, `:133 escape_residue_outside`, `:160 converge_residue_fixed`, `:228 residue_tag_two_poles` | ∅-axiom PURE ✓ (scanned) |
| **★ `Ext^{>0}/Tor_{>0}` = obstruction residue = `de_rham`/`sheaf` `H^{>0}` = `ker δ/im δ`** | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 reduced_betti_d4_contractible`, `:42 kerSizeDelta`, `:47/:52 kerSize_5_0/1`; `Lib/Math/Cohomology/Delta/Core.lean:54 delta`, `deltaAt` | **PURE, scanned 16/0** ✓ (with V4Capstone) |
| **★ connecting `δ`/long exact/`δ²=0` ("two consecutive ∘ = 0") = `q=±1` sign-propagation** | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 dsq_zero_universal_delta4`; `:62 leibniz_universal_delta4` (Ext cup/Yoneda product) | **PURE, scanned** ✓ |
| exact part / `δ`'s orientation sign (`q=−1` wedge) | `Lib/Math/Cohomology/Cup/SignedCup.lean:62 cup1_antisymmetric`, `:52 mergeSign` (`(−1)^inv`), `:148 signed_cup_capstone` | **PURE** ✓ (`de_rham.md` scanned 14/0) |
| resolution (proj/inj) = the resolution dial at chain level | `Lib/Math/Geometry/Topology/Continuity.lean:64 compose_modulus_eq`; `Lib/Math/Analysis/ResolutionShift.lean:73 IsResolutionShift` | ∅-axiom PURE ✓ (`sheaf_theory.md`/`continuity.md`) |
| resolution's quasi-iso / uniqueness = initiality (catamorphism) | `Lens/Foundations/UniversalDistinguishing.lean:103 dhom_unique_pointwise`; `Lens/Foundations/SemanticAtom.lean:412 raw_initial`, `:108 universalMorphism` | ∅-axiom PURE ✓ (`sheaf_theory.md` scanned) |
| **`Ext¹` = extensions mod split: split = `q=+1` (closure, no residue)** | `Lib/Math/Order/GaloisConnection.lean:126 clo_idempotent`, `:107 clo_extensive`; `Lib/Math/Order/FenchelMoreau.lean:59 biconjugate_eq_clo`, `:134 biconj_idempotent`, `:152 closed_iff_fixed` | ∅-axiom PURE ✓ (`galois.md`) |
| `⊗` = the convolution/tensor reading (`Hom`/`⊗` flavour) | `Lib/Math/Probability/Limit/ConvolveProfile.lean : conv`/`⋆`, `mass_conv` (`×↦·`), `momentNum_conv` (`×↦+`); `Lib/Math/Combinatorics/PowerSeriesSemiring.lean` (welds) | ∅-axiom ✓ (`generating_functions.md`) |
| group cohomology = `Aut`-family `Ext`; `q=±1` modular cocycle | `Lib/Math/Algebra/Linalg213/PermGroup.lean : composeList` (the `Aut`-family, `groups.md`); `…/Real213/Minkowski/MinkowskiCocycle.lean` (the modular cocycle) | ∅-axiom ✓ (`groups.md`/`galois.md`) |
| escape / faithful residue (the `q=−1` pole's kernel) | `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective`, `:47 object1_injective` | ∅-axiom PURE ✓ |
| `Lens.refines` (the reading order = kernel containment) | `Lens/LensCore.lean:90 Lens.refines`, `:93 refines_refl`, `:95 refines_trans` | ∅-axiom PURE ✓ |
| cross-frame | `homology.md` (`∂` = `L↓`, `∂²=0`, `Residue(L↓,C) = ker∂/im∂`), `de_rham.md` (`H*_dR = ker d/im d`, `d²=∂²`), `sheaf_theory.md` (`H^{>0}` = local-global obstruction), `galois.md` (closure = `q=+1`, Gal-cohomology), `groups.md` (`Aut`-family), `generating_functions.md` (`⊗` = convolution), `continuity.md`/`derivative.md` (resolution dial) | prior, ∅-axiom ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root):**
`E213.Lib.Math.Cohomology.Delta.V4Capstone` + `E213.Lib.Math.Cohomology.Examples.BettiKernel` —
**16 pure / 0 dirty** combined (includes `leibniz_universal_delta4`, `delta4_cohomology_capstone`,
`reduced_betti_d4_contractible`, `kerSizeDelta`, `kerSize_5_0/1`; `dsq_zero_universal_delta4` resides in
V4Capstone, prior-scanned 5/0 in `de_rham.md`/`sheaf_theory.md`). `ResidueTag`, `GaloisConnection`,
`FenchelMoreau`, `SignedCup`, `Continuity`, `ResolutionShift`, `dhom_unique_pointwise`, `raw_initial`,
`object1_not_surjective`, `Lens.refines` — all PURE per prior-session scans (`sheaf_theory.md`/`galois.md`/
`de_rham.md`). Build clean.

## Conceptual-only / absent legs (honest)

- **`Ext` / `Tor` / `Resolution` / `ShortExactSequence` / `LongExactSequence` / `SnakeLemma` /
  `connectingMap` / `derivedFunctor` / `δ-functor` OBJECTS — ABSENT, located.** Grep over `lean/E213` for
  `Ext`/`Tor`/`ProjectiveResolution`/`InjectiveResolution`/`deltaFunctor`/`longExact`/`LongExact`/
  `connectingMap`/`snakeLemma`/`shortExact`/`ShortExact`/`isExact`/`IsExact`/`derivedFunctor` returns
  **zero Lean declarations** (the only `Ext` token is a *filename note* in `DyadicFSM/INDEX.md`, a Legendre
  Pisano variant — unrelated). There is no `Hom`/`⊗` bifunctor on a module category, no `Resolution` chain
  with a quasi-iso to `M`, no exact-sequence type, no graded `Ext^n`/`Tor_n`, no δ-functor universality.
  **This is the precise missing leg** — the abelian-category twin of `sheaf_theory.md`'s missing
  presheaf-bundle and `de_rham.md`'s missing smooth `Ω^k(M)`. The *residue mechanism* (`ker δ/im δ`,
  `delta`, `dsq_zero`, `reduced_betti_*`), the *`q=±1` grading tag* (`ResidueTag`), the *exact/`q=+1` part*
  (`clo_idempotent`/`ker=im`), the *resolution dial* (`compose_modulus_eq`/`ResolutionShift`), and the
  *`⊗`-flavour reading* (`ConvolveProfile`) are each built and PURE; the derived-functor object that would
  weld them is the named open target. Suggested buildable witness (analogue of the modulated Banach
  engine): a small concrete `Ext¹` of two finite cochain complexes via `kerSizeDelta` on a *non-exact*
  resolution — exhibiting a nonzero `q=−1` residue where `reduced_betti_d4_contractible` exhibits the zero
  (`q=+1`/exact) one.
- **`GroupCohomology` / `groupRing` / `Ext_{ℤG}` — ABSENT.** Grep returns zero declarations; the `Aut`-family
  (`PermGroup.composeList`) and a `q=±1` modular cocycle (`MinkowskiCocycle.lean`) are built, but no
  group-ring or group-cohomology object. The `galois.md` "Galois cohomology `H¹`" leg is conceptual at the
  object level (the residue mechanism and the `Aut`-family are built).
- **The abelian-category ambient (`Module`/`Ab`/exactness as a category property) — ABSENT.** Exactness
  (`ker=im`) lives in 213 as the *empty-residue* condition (`reduced_betti_d4_contractible`), not as a
  property of an `AbelianCategory` object. The condition is built pointwise; the categorical packaging is open.
- **Derived functor = the residue-taking operation *as one theorem*** — this identification is the
  decomposition's reading. Lean certifies each leg separately (`reduced_betti_d4_contractible`/`delta`/
  `dsq_zero` for the residue; `ResidueTag` for the grading; `compose_modulus_eq`/`ResolutionShift` for the
  resolution; `clo_idempotent` for the exact/split pole); the single theorem welding a named `Ext^n` object
  into "the `q=±1` residue of a non-exact functor composed with the resolution dial, graded by `n`" is
  conceptual framing on verified PURE objects — the same shape `sheaf_theory.md`'s gluing-=-initiality
  identification has.

> Axiom-purity note: the load-bearing cohomology anchors (`reduced_betti_d4_contractible`, `kerSizeDelta`,
> `leibniz_universal_delta4`, `delta4_cohomology_capstone`) were freshly scanned **16 pure / 0 dirty** this
> session via `tools/scan_axioms.py` (run from repo root with the `E213.` module prefix);
> `dsq_zero_universal_delta4` is in the same V4Capstone module (prior-session 5/0). The purity claim rests
> on the fresh scan, not docstrings.
