# Decomposition: spectral sequences (the pages E_r, the differentials d_r with d_r²=0, E_{r+1}=H(E_r), convergence E_∞ ⟹ the associated graded of a filtration)

*A FRESH decomposition per `../README.md` (model v7.1), the NEXT step from `homological_algebra.md`. That
note found the deepest reflexive turn: homological algebra **names the calculus's own residue-taking
operation** — a derived functor = `Residue(L,C)` graded by degree `n`, the `q=±1` tag displayed degree by
degree, the resolution dial at chain level. A spectral sequence is what you get when you **iterate that
operation**. The thesis to TEST, not re-skin: a spectral sequence is the calculus's residue-taking operation
**applied to its own output**, indexed by the resolution dial `r`, and converging to a fixed point.
Concretely:
(i) each **page** `E_{r+1} = H(E_r) = ker d_r / im d_r` is exactly `homological_algebra.md`'s `Residue(L,C)`
— the SAME `ker δ/im δ` as `reduced_betti_d4_contractible` — but the *operand of the (r+1)-th residue is the
output of the r-th*: this is the residue **re-entering as the next operand** (`ResidueReentry.
residue_perpetually_reenters`), the iteration `homological_algebra.md` did not test;
(ii) the **sequence of pages** is that one residue operation iterated, **indexed by the resolution dial `r`**
(`IsResolutionShift`, `IsResolutionShift_compose`: the grades add, `r` is the cumulative shift);
(iii) **`d_r² = 0` on every page** is the `q=±1` sign-propagation (`dsq_zero_universal_delta4`), the same
orientation-bit cancellation `homological_algebra.md` cited for `δ²=0`, now **repeated per page**;
(iv) **convergence `E_∞`** (`E_r = E_{r+1}` for large `r`, the differential vanishes) is the `q=+1` modulated
limit — the page-residue STABILIZES, a **fixed point of the residue-iteration**, the SAME
modulated-completion convergence as `DyadicCompletion`/`golden_is_converge`, where the "modulus" is the page
number `r` at which `d_r` vanishes;
(v) the **filtration** = the README's fold-height axis graded.
So a spectral sequence = (the residue operation) ∘ (the resolution dial) ∘ (the q=+1 convergence) — three
already-built pieces composed; **no new primitive**. This is the deepest test yet of whether
`homological_algebra.md`'s "the normal form is an OPERATION" claim extends to ITERATION.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **filtered chain complex** (or bicomplex): the *same* graded simplex/cochain
  nesting `homology.md`/`de_rham.md`/`homological_algebra.md` read — a sequence `… → Cⁿ → Cⁿ⁺¹ → …` of
  distinguished cells with the boundary/coboundary `delta` between adjacent degrees (`Cochain n k`,
  `Delta/Core.lean`) — now carrying a **second grading**: a **filtration** `F⁰ ⊇ F¹ ⊇ F² ⊇ …`, a descending
  chain of sub-constructions. `C` carries the README's two read-off axes, *both used twice*: a **fold-height**
  (the degree `n`/`k` AND the filtration index `p` — the filtration is fold-height read on a second axis) and
  a **direction/orientation bit** (the alternating sign the differential carries). The filtration index `p`
  is exactly the README's bidirectional fold-height (`homology.md`) used as a *second* grading: where the
  degree counts cell-dimension, the filtration counts depth into the sub-construction tower. Nothing
  classically spectral-sequence-theoretic is a primitive — `C` is the filtered combinatorial complex + its
  `delta`; **no `SpectralSequence`, no `Page`/`E_r`, no bicomplex object, no `Filtration` type enters** (see
  Residue / verdict — these are ABSENT, grep-confirmed).

- **Reading `L` — the residue-taking operation `Residue(L,C)`, ITERATED, indexed by the resolution dial
  `r`.** This is the genuinely new framing the field supplies, and the precise extension of
  `homological_algebra.md`: that note read `Residue(L,C)` *once* (a derived functor = the `ker δ/im δ` of a
  non-exact reading, graded by degree). A spectral sequence reads it **again on its own output**, and again,
  the `r`-th reading taking the `(r−1)`-th's residue as operand:
  - **The page differential `d_r`** is the `r`-th coboundary reading — `homological_algebra.md`'s connecting
    `δ` at **stage `r`**, a reading `E_r → E_r` raising the filtration index by `r` (the `IsResolutionShift`
    of grade `r`). It is the SAME alternating face-reading (`delta`), read at the `r`-th resolution.
  - **`E_{r+1} = H(E_r) = ker d_r / im d_r`** is `homological_algebra.md`'s `Residue(L,C) = ker δ/im δ`
    *verbatim*, with the crucial difference that **its operand `E_r` is itself the output of the previous
    residue**. The page recursion IS the residue **re-entering as the next operand**: `residue_perpetually_
    reenters` (`ResidueReentry.lean:85`, PURE) says exactly "each turn leaves the residue, the residue
    re-enters as a Raw, the next turn leaves it again" — `E_r ↦ H(E_r) = E_{r+1} ↦ H(E_{r+1}) = E_{r+2} ↦ …`.
    The spectral sequence is `Residue(−,−)` composed with itself, indexed by `r`.
  - **The resolution dial supplies the index `r`.** Each page advances the resolution by one: `d_r` shifts
    the filtration by `r`, and the dial's grades **add under composition** — `IsResolutionShift_compose`
    (`ResolutionShift.lean:130`, PURE): grade-`E₁` ∘ grade-`E₂` = grade-`(E₂+E₁)`. So passing from page `0`
    to page `r` is the `r`-fold iterate of the unit dial (`cutHalfIter`, `ResolutionShift.lean:158`),
    cumulative grade `r`. **`r` is the resolution parameter** (`continuity.md`/`derivative.md`), here counting
    *which page* — i.e. how many times the residue operation has been re-applied.
  - So the reading is: **take the residue (`ker δ/im δ`), feed its output back in as the next operand, repeat,
    indexing the repetitions by the resolution dial `r`.** The reading IS the residue-taking operation
    iterated.

- **Residue — the `q=±1` tag of `homological_algebra.md`, now read on the WHOLE ITERATION and tagged by
  whether it STABILIZES.** Each page is a residue with the usual `q=±1` tag; the *new* residue this note
  surfaces is the residue **of the iteration itself** — does the page sequence reach a fixed point?
  - **`q=+1` (convergence `E_∞`) — the iteration STABILIZES.** For large `r` the differential `d_r` vanishes
    (`d_r = 0`), so `E_{r+1} = H(E_r) = ker 0 / im 0 = E_r`: the page-residue is a **fixed point of the
    residue-iteration**. This is the README's `q=+1` converging pole (`converge_residue_fixed`,
    `ResidueTag.lean:160`; `golden_is_converge`, `:180`) — the SAME modulated-completion convergence as
    `DyadicCompletion`'s `orbit_to_center_completion` (`:366`, the convolve-rescale orbit reaching its
    center, reached-by-none, narrowed only by a modulus). **The "modulus" is the page number `r` at which
    `d_r` vanishes** — exactly the role the dyadic exponent plays in `banach_fixed_point_modulated`'s
    `N(m)=m`. `E_∞ ⟹ gr(filtration)` (the abutment is the associated graded of the filtration) is then the
    statement that the stabilized residue equals the fold-height-graded readout — the README's filtration
    axis read off at the fixed point. The `q=+1` corner: "the iteration closes; the residue stops moving".
  - **`q=−1` (non-degeneration / a page that never dies) — the iteration ESCAPES.** A differential `d_r` that
    stays nonzero at every page, or a filtration that never exhausts, is the `q=−1` escape: the residue
    **re-enters forever and the cover never closes** — `residue_reentry_never_closes` (`ResidueReentry.lean:63`,
    PURE: re-pointing the residue's encoding is never surjective; "naming the residue yields a fresh object,
    leaving a fresh residue — the cover never closes"). This is the obstruction pole
    (`escape_residue_outside`, `object1_not_surjective`), the same `q=−1` as `homological_algebra.md`'s
    `Ext^{>0}`. So the spectral-sequence dichotomy "degenerates / does not" IS the README's `q=±1` tag read
    on the *iteration*: converge (`q=+1`, `E_∞` exists, stabilizes) vs escape (`q=−1`, the residue re-enters
    without end).
  - **`d_r² = 0` per page** = the `q=±1` sign-propagation **repeated**: on each page the differential is a
    coboundary, so `d_r ∘ d_r = 0` by the SAME orientation-bit pairwise cancellation as
    `dsq_zero_universal_delta4` (`V4Capstone.lean:41`, PURE). `homological_algebra.md` cited this once for
    `δ²=0`; a spectral sequence is `δ²=0` **holding on every page of the iteration** — the `q=±1`
    direction-bit threading through the whole tower.

## Re-seeing — ⟨C | L⟩

```
   filtered complex C        =  ⟨ graded cells + a descending filtration | the boundary delta + filtration index ⟩
                                 = homological_algebra.md's C with a SECOND fold-height grading (the filtration p)
   page E_r                  =  the residue Residue(L,C) AT ITERATION STAGE r  =  ker d_r / im d_r
   page recursion E_{r+1}=H(E_r) =  the residue RE-ENTERS as the next operand  (residue_perpetually_reenters)
                                 = Residue(−,−) composed with itself, the iteration homological_algebra.md did not test
   page differential d_r     =  homological_algebra.md's connecting δ at STAGE r  (one delta op, shifted by r)
   "d_r² = 0" (every page)   =  the q=±1 sign-propagation REPEATED per page  =  dsq_zero_universal_delta4
   the index r               =  the resolution dial counting WHICH PAGE  =  IsResolutionShift (grade r), grades ADD (compose)
   passing page 0 → page r   =  the r-fold iterate of the unit dial  =  cutHalfIter, IsResolutionShift_compose (E₂+E₁)
   convergence E_∞ (d_r=0 large r) =  the iteration STABILIZES  =  q=+1 FIXED POINT of the residue-iteration
                                 = converge_residue_fixed / golden_is_converge / orbit_to_center_completion (modulus = r)
   "the modulus" for E_∞      =  the page number r at which d_r vanishes  (banach_fixed_point_modulated's N(m))
   non-degeneration (d_r≠0 ∀r)=  q=−1 ESCAPE  =  the residue re-enters forever  (residue_reentry_never_closes)
   E_∞ ⟹ gr(filtration)      =  the stabilized residue = the fold-height-graded readout  (filtration = README height axis graded)
```

So **the pages, the page differentials, `d_r²=0`, convergence, and the abutment are ONE machine** — the
calculus's `Residue(L,C)` recipe **iterated**, the iteration indexed by the resolution dial `r` and tagged
`q=±1` by whether it stabilizes. Set against `homological_algebra.md` (whose machine produces ONE residue per
degree) and its neighbors:

| classical spectral-sequence object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| page `E_r` | `Residue(L,C)` at iteration stage `r` | `homological_algebra.md` (the single residue) | `reduced_betti_d4_contractible` |
| page recursion `E_{r+1}=H(E_r)` | the residue RE-ENTERS as the next operand (the iteration) | NEW (iteration of the residue op) | `residue_perpetually_reenters` |
| page differential `d_r` | the connecting `δ` at stage `r` (one `delta`, shifted) | `homological_algebra.md` (`δ`), `homology.md` (`∂`) | `Delta/Core.delta`; `IsResolutionShift` |
| `d_r²=0` (every page) | `q=±1` sign-propagation REPEATED per page | `homology.md` (`∂²=0`), `homological_algebra.md` (`δ²=0`) | `dsq_zero_universal_delta4` |
| the index `r` | the resolution dial counting the page (grades add) | `continuity.md`/`derivative.md` (resolution) | `IsResolutionShift_compose`, `cutHalfIter` |
| convergence `E_∞` (`d_r=0`, large `r`) | `q=+1` FIXED POINT of the residue-iteration (modulus = `r`) | NEW (fixed point of the ITERATION) | `golden_is_converge`, `orbit_to_center_completion` |
| non-degeneration (`d_r≠0 ∀r`) | `q=−1` escape: residue re-enters forever | `cardinality.md` (`q=−1`), `homological_algebra.md` | `residue_reentry_never_closes`, `object1_not_surjective` |
| `E_∞ ⟹ gr(filtration)` | the stabilized residue = the fold-height-graded readout | `homology.md` (fold-height), `dimension.md` | `kerSizeDelta`; (abutment object ABSENT) |

A spectral sequence consumes BOTH of `C`'s axes *twice over*: the fold-height once as the complex degree
(`d_r` raises it) and once as the filtration index (`r` tracks depth into it), the direction-bit on every
page's `d_r` — exactly because it is the residue machine `homological_algebra.md` named, *run as an
iteration over the resolution dial*.

## LEVERAGE — does a spectral sequence = the residue operation ITERATED ∘ the resolution dial ∘ the q=+1 convergence?

**Verdict: PREDICTION + PARTIAL — the deepest test of `homological_algebra.md`'s "the normal form is an
OPERATION" claim, and it EXTENDS: the operation iterates.** `homological_algebra.md` showed a derived functor
= `Residue(L,C)` once; a spectral sequence is that residue **fed its own output**, indexed by the resolution
dial `r`, converging to a fixed point. Every load-bearing leg — the residue mechanism, the re-entry that IS
the iteration, the resolution dial that indexes it, the `d_r²=0` per page, the `q=+1` stabilization — is
already ∅-axiom and PURE; the *named* `SpectralSequence`/`Page`/`E_r`/`Filtration`/`E_∞` objects are ABSENT,
the precise missing leg (the same shape as `homological_algebra.md`'s missing `Ext^n`/resolution object and
`sheaf_theory.md`'s missing presheaf-bundle). Leg by leg, honest.

**(1) ★ The page recursion `E_{r+1}=H(E_r)` IS the residue re-entering as its own operand — this is the NEW
datum, not a re-skin of `homological_algebra.md`.** `homological_algebra.md` read `Residue(L,C)` once and
stopped (a derived functor at each degree `n`). The spectral sequence's defining move is to take the residue
`H(E_r)` and **make it the operand of the next residue** `H(E_{r+1})`. The calculus already has this exact
operation as a foundational theorem: `residue_perpetually_reenters` (`ResidueReentry.lean:85`, PURE) — "each
turn leaves the residue, the residue re-enters as a Raw, the next turn leaves it again. The residue is the
perpetual next operand." That sentence *is* the page recursion `E_r ↦ H(E_r) = E_{r+1} ↦ H(E_{r+1}) = E_{r+2}`.
So the spectral sequence is `Residue(−,−)` **composed with itself** — the iteration the residue-first normal
form `⟨C|L⟩ ⊕ Residue(L,C)` was built to support but `homological_algebra.md` did not exercise. **This is the
load-bearing new finding: the residue operation is closed under self-composition, and a spectral sequence is
its orbit.**

**(2) ★ The index `r` is the resolution dial, and the grades ADD under page-composition — `r` counts the
re-applications.** Each page advances the resolution by one; `d_r` shifts the filtration index by `r`. The
calculus's resolution dial composes additively: `IsResolutionShift_compose` (`ResolutionShift.lean:130`,
PURE) — grade-`E₁` ∘ grade-`E₂` = grade-`(E₂+E₁)` — and the `r`-fold iterate of the unit dial is
`cutHalfIter` (`:158`), cumulative grade `r` (`IsResolutionShift_cutHalfIter`). So **the page index `r` is
the cumulative resolution shift after `r` re-applications of the residue operation** — the resolution
parameter (`continuity.md`/`derivative.md`) repurposed to count *iterations*. This is the precise sense in
which a spectral sequence = (residue op) ∘ (resolution dial): the dial supplies the grading `r` over which the
residue op is iterated, and its additivity is what makes "page `r`" well-defined.

**(3) ★ `d_r²=0` on every page = `dsq_zero_universal_delta4` REPEATED — the `q=±1` sign-propagation per
page.** Each `d_r` is a coboundary reading, so `d_r ∘ d_r = 0` by the SAME pairwise orientation-bit
cancellation `homological_algebra.md`/`homology.md`/`de_rham.md` cited for `δ²=0`/`∂²=0`/`d²=0`:
`dsq_zero_universal_delta4` (`V4Capstone.lean:41`, PURE, scanned 5/0: `∀ σ, ∀ i, δ(δσ) i = false` at strata
(5,1),(5,2),(5,3)). A spectral sequence is the statement that this `q=−1` direction-bit cancellation holds
*not once but at every page of the iteration* — the orientation bit threading through the whole tower so that
`H(E_r)` is well-defined at each stage. The graded-relation companion `leibniz_universal_delta4`
(`V4Capstone.lean:62`, PURE) is the multiplicative structure carried along (the spectral sequence's product,
`two_cells.md`'s graded-relation slot).

**(4) ★ Convergence `E_∞` = the `q=+1` fixed point of the residue-iteration, with the page number `r` as the
modulus — the same modulated-completion convergence as `DyadicCompletion`/`golden_is_converge`.** This is the
sharpest leverage and the second new datum. A spectral sequence *converges* when `d_r=0` for all large `r`,
so `E_{r+1}=H(E_r)=ker 0/im 0 = E_r`: the page-residue STABILIZES — a **fixed point of the residue-iteration**.
This is precisely the README's `q=+1` converging pole: `converge_residue_fixed` (`ResidueTag.lean:160`, PURE)
delegating to `banach_fixed_point_modulated` (the modulated converge engine), and `golden_is_converge`
(`:180`, PURE) tying the `+1` multiplier to the literal stabilizing orbit. The completion-limit instance is
`DyadicCompletion.orbit_to_center_completion` (`:366`, scanned 32/0 PURE): an orbit reaching its center,
reached-by-none, narrowed only by a modulus. **The spectral sequence's "modulus" is the page number `r` at
which `d_r` vanishes** — exactly the role of `banach_fixed_point_modulated`'s explicit `N(m)=m`: the page at
which the residue stops moving IS the convergence modulus. So `E_∞` is not a transcendent target but the
finite-signature fixed point of the iteration — the residue's shape characterized by *the page it stabilizes
on* (CLAUDE.md "Infinity is the residue's shape, not a god above it"). And the dual `q=−1` is built too:
a sequence that never degenerates (residue re-enters at every page) is `residue_reentry_never_closes`
(`ResidueReentry.lean:63`, PURE) — "naming the residue yields a fresh object, leaving a fresh residue, the
cover never closes". **Convergence vs non-degeneration IS the `q=±1` tag read on the iteration.**

**(5) The filtration = the fold-height axis graded; `E_∞ ⟹ gr(filtration)` = the stabilized residue read off
by height.** The descending filtration `F⁰⊇F¹⊇…` is the README's bidirectional fold-height (`homology.md`,
`dimension.md`) used as a *second* grading — depth into the sub-construction tower, the well-founded measure
already in `C` (`Lambek.isPart_wf`, `no_infinite_descent`). The abutment `E_∞ ≅ gr_F(H*)` says the stabilized
residue equals the fold-height-graded readout of the total cohomology — the filtration axis read off at the
fixed point. The fold-height grading and its `ker/im` residue at each level are built (`kerSizeDelta`,
`reduced_betti_d4_contractible`); the *named filtered/bigraded `E_∞`-abutment object* is conceptual (see
boundary).

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, scanned PURE):* (a) the **residue mechanism `ker δ/im δ`** each page computes —
  `delta` (`Delta/Core.lean:54`), `dsq_zero_universal_delta4`/`leibniz_universal_delta4` (`V4Capstone.lean:41,62`,
  5/0), `reduced_betti_d4_contractible`/`kerSizeDelta` (`BettiKernel.lean:63,42`, 11/0), and the nonzero-residue
  witness `nonzero_cohomology_class`/`betti_one_cycle`/`cycle_vs_contractible_qpm` (`NonzeroBetti.lean:143,111,173`,
  56/0); (b) ★ the **iteration = residue re-entry** — `residue_perpetually_reenters`/`residue_reentry_never_closes`
  (`ResidueReentry.lean:85,63`, 14/0); (c) ★ the **resolution dial indexing `r`, grades add** —
  `IsResolutionShift`/`IsResolutionShift_compose`/`cutHalfIter`/`IsResolutionShift_cutHalfIter`
  (`ResolutionShift.lean:73,130,158`, 17/0); (d) ★ the **`q=+1` convergence / fixed point** —
  `converge_residue_fixed`/`golden_is_converge`/`residue_tag_two_poles` (`ResidueTag.lean:160,180,228`, 55/0),
  `orbit_to_center_completion` (`DyadicCompletion.lean:366`, 32/0), `banach_fixed_point_modulated`
  (`BanachFixedPointModulated.lean:111`, under namespace `BanachFixedPoint.CompleteMetricModulusMod`); (e) the
  **`q=−1` escape** — `escape_residue_outside`/`object1_not_surjective` (`ResidueTag.lean:133`,
  `FlatOntologyClosure.lean:61`); (f) the **growing iteration-character** (the page tower ascends) —
  `succ_not_idempotent` (`MuNuMirror.lean:80`, 8/0); (g) the **`q=+1` split/closure** an exact page collapses to —
  `clo_idempotent` (`GaloisConnection.lean:126`, 15/0), `biconj_idempotent` (`FenchelMoreau.lean:134`, 18/0).
- *Conceptual-only / the precise missing leg (the `homological_algebra.md`/`sheaf_theory.md`-style gap): the
  `SpectralSequence`/`Page`/`E_r`/`d_r`/`Filtration`/`E_∞`/abutment OBJECTS are ABSENT.* Grep over `lean/E213`
  for `SpectralSequence`/`spectral_sequence`/`Page`/`E_r`/`pageDiff`/`d_r`/`Filtration`/`gradedAssoc`/`abutment`/
  `Einfty`/`E_infty`/`leray`/`serre` returns **zero Lean declarations** — the only hit is a *physics docstring
  comment* in `Lib/Physics/AlphaEM/LoopVertexGraduation.lean:45` ("Filtration spectral sequence: the `d_r`
  differential increases filtration depth by `r`… recorded at the interpretive level, NOT a derivation"), which
  itself flags the object as unbuilt. There is **no** filtered/bigraded complex object, **no** `Page` indexed by
  `r` with a `d_r` field, **no** `E_{r+1}=H(E_r)` recursion as a Lean def, **no** `E_∞`/abutment, **no** Leray/
  Serre/Grothendieck instance. This is the SAME shape as `homological_algebra.md`'s missing `Ext^n`/resolution/
  exact-sequence object: the *residue mechanism* (`ker δ/im δ`), the *iteration* (`residue_perpetually_reenters`),
  the *resolution-dial index* (`IsResolutionShift_compose`), the *`d_r²=0` per page* (`dsq_zero`), and the
  *`q=±1` stabilization tag* (`ResidueTag`, `golden_is_converge`) are each built and PURE; the
  **filtered/bigraded `E_r`-with-`d_r` object that would weld them into a named spectral sequence** is the
  precise open leg.

So: **PREDICTION on the consolidation (a spectral sequence = the residue operation iterated ∘ the resolution
dial ∘ the q=+1 convergence; each page = `Residue(L,C)`; the page recursion = the residue re-entering as its
own operand; `r` = the resolution dial counting iterations; `d_r²=0` = `dsq_zero` per page; `E_∞` = the q=+1
fixed point with `r` as modulus; non-degeneration = the q=−1 escape), cashed at the residue-mechanism /
iteration / resolution-dial / convergence-tag level; PARTIAL because the `SpectralSequence`/`Page`/`E_∞`
OBJECTS are absent — the named open legs, not hand-waves.**

## Revelation (the residue-taking operation, ITERATED — homological_algebra.md's "the normal form is an OPERATION" extends to its own orbit)

**Collapse — the pages, the page differentials, `d_r²=0`, convergence, and the abutment are ONE machine: the
calculus's `Residue(L,C)` recipe applied to its own output, indexed by `r`, converging to a fixed point.**
`homological_algebra.md`'s deepest find was that the README's normal form `⟨C|L⟩ ⊕ Residue(L,C)` is not a
description but an *operation* — a derived functor = `Residue(L,C)` graded by degree. That note ran the
operation **once per degree** and stopped. A spectral sequence is what the calculus produces when the operation
is **closed under self-composition**: feed `H(E_r)` back in as the operand of `H(E_{r+1})`, index the
re-applications by the resolution dial `r`, and ask whether the orbit reaches a fixed point. The single forcing
sentence, read at both poles:

- **`q=+1` (convergence = the iteration stabilizes = `E_∞`).** For large `r`, `d_r=0` and `E_{r+1}=E_r`: the
  page-residue is a fixed point of the residue-iteration — the converging/closure pole
  (`converge_residue_fixed`, `golden_is_converge`, `orbit_to_center_completion`). The page number at which it
  stabilizes IS the convergence modulus (`banach_fixed_point_modulated`'s `N(m)`); the abutment
  `E_∞ ⟹ gr(filtration)` reads the fixed point off by fold-height. The `q=+1` corner: "the residue stops
  moving; the iteration closes."
- **`q=−1` (non-degeneration = the residue re-enters forever).** A differential nonzero at every page is the
  escape: the residue **re-enters as the next operand without end** — `residue_reentry_never_closes`,
  "naming the residue yields a fresh object, leaving a fresh residue, the cover never closes"
  (`escape_residue_outside`, `object1_not_surjective`). The `q=−1` pole `homological_algebra.md`'s `Ext^{>0}`
  occupied, now read on the *iteration* rather than a single degree.

This passes the re-skin guard at the deepest level the notebook has reached, and it does NOT restate
`homological_algebra.md`: that note identified a derived functor with `Residue(L,C)` (one application); **this
note's new datum is that the residue operation is closed under iteration, that the iteration index is the
resolution dial (`IsResolutionShift_compose`, grades add), and that convergence is the `q=+1` fixed point of
that iteration with the page number as modulus.** The page recursion is grounded by a foundational theorem the
earlier note never used — `residue_perpetually_reenters` ("the residue is the perpetual next operand") — which
is *precisely* the spectral-sequence move `E_{r+1}=H(E_r)`. The deepest line: **a spectral sequence is
`Residue(−,−)` orbiting under self-composition, the residue-taking operation `homological_algebra.md` named now
shown to be ITERABLE — converging (`q=+1`, `E_∞`, fixed point) or escaping (`q=−1`, the cover never closes),
the `q=±1` tag read on the orbit.** `homological_algebra.md` showed the normal form is an operation; this shows
the operation is a *dynamical system* whose fixed points are abutments and whose `q=±1` tag is the
degeneration dichotomy. **EXTEND by consolidation + the iteration datum; no new axis; interior model v7.1
holds.** The one genuine absence — the `SpectralSequence`/`Page`/`E_∞` object — is located precisely: the
filtered/bigraded twin of `homological_algebra.md`'s missing `Ext^n`/resolution object, the named iteration-
of-the-residue object that would weld the (all-built) re-entry + resolution-dial + convergence mechanism.

## Note for the technique

**No new primitive; the deepest test of "the normal form is an OPERATION" yet — and it extends: the operation
ITERATES.** A spectral sequence does not extend model v7.1; it *iterates the operation v4 introduced and
`homological_algebra.md` named* (`Residue(L,C)`):
- the **residue mechanism** (`homology.md`/`homological_algebra.md`, `ker δ/im δ`, `reduced_betti_d4_contractible`)
  supplies each page `E_r`;
- the **residue re-entry** (`ResidueReentry.residue_perpetually_reenters`) supplies the page recursion
  `E_{r+1}=H(E_r)` — the operand of one residue is the output of the last;
- the **resolution dial** (`continuity.md`/`derivative.md`, `IsResolutionShift_compose`, grades add) supplies
  the index `r` counting the iterations;
- the **`q=+1` convergence** (`ResidueTag`/`DyadicCompletion`/`banach_fixed_point_modulated`) supplies `E_∞`
  as the fixed point of the iteration, with the page number `r` as the modulus;
- the **`q=±1` sign-propagation** (`dsq_zero_universal_delta4`) supplies `d_r²=0` *on every page*.

The lesson for the model: **the residue-taking operation `Residue(L,C)` is closed under iteration, the
iteration index is the resolution dial, and convergence is the `q=+1` fixed point of the iteration.** A
spectral sequence is the orbit of `Residue(−,−)` under self-composition — `homological_algebra.md`'s "the
normal form is an operation" promoted to "the operation is a dynamical system on residues, whose fixed points
are abutments (`q=+1`) and whose non-stabilizing orbits are the `q=−1` escape". This is the sharpest
confirmation that the residue-first normal form was the right primitive: it not only *names* the operation
homological algebra performs, it supports that operation's *iteration*, and the convergence/degeneration
dichotomy falls out as the `q=±1` tag read on the orbit (with the page number as the finite-signature
modulus, never a transcendent `E_∞` above the finite). The one genuine absence — the
`SpectralSequence`/`Page`/`E_∞` object — is located precisely: the iteration-of-the-residue twin of
`homological_algebra.md`'s missing graded `Ext^n` and `sheaf_theory.md`'s missing presheaf-bundle. Every leg
the object would need *structurally* — the per-page `ker δ/im δ` residue, the re-entry that IS the iteration,
the resolution-dial index `r`, the `d_r²=0` per page, the `q=+1` stabilization — is present and PURE; only the
named filtered/bigraded object is open.

---

## Verified Lean anchors (file:line — all grep/Read-verified on `lean/E213`; purity scanned via `tools/scan_axioms.py` from repo root this session)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| **★ page recursion `E_{r+1}=H(E_r)` = the residue RE-ENTERS as the next operand (the iteration)** | `Lens/Foundations/ResidueReentry.lean:85 residue_perpetually_reenters`, `:63 residue_reentry_never_closes`, `:165 residue_reentry_concrete` | **∅-axiom PURE, scanned 14/0** ✓ |
| **★ the index `r` = the resolution dial counting iterations; grades ADD under page-composition** | `Lib/Math/Analysis/ResolutionShift.lean:73 IsResolutionShift`, `:130 IsResolutionShift_compose`, `:158 cutHalfIter` (+ `IsResolutionShift_cutHalfIter`) | **∅-axiom PURE, scanned 17/0** ✓ |
| **★ convergence `E_∞` = `q=+1` fixed point of the iteration (page number `r` = modulus)** | `Lib/Math/Foundations/ResidueTag.lean:160 converge_residue_fixed`, `:180 golden_is_converge`, `:228 residue_tag_two_poles`, `:133 escape_residue_outside`, `:86 multiplier_unimodular` | **∅-axiom PURE, scanned 55/0** ✓ |
| convergence as a genuine completion-limit (reached-by-none, modulus-narrowed) | `Lib/Math/Probability/Limit/DyadicCompletion.lean:366 orbit_to_center_completion` | **∅-axiom PURE, scanned 32/0** ✓ |
| the modulated converge engine `E_∞` delegates to | `Lib/Math/Analysis/BanachFixedPointModulated.lean:111 banach_fixed_point_modulated` (namespace `…BanachFixedPoint.CompleteMetricModulusMod`) | ∅-axiom ✓ (cited via `ResidueTag.converge_residue_fixed`) |
| each page `E_r = ker d_r / im d_r` = `Residue(L,C)` (= homological_algebra.md's residue) | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 reduced_betti_d4_contractible`, `:42 kerSizeDelta`, `:47/:52 kerSize_5_0/1` | **∅-axiom PURE, scanned 11/0** ✓ |
| nonzero page-residue witness (`q=−1` obstruction surfaces; vs contractible `q=+1`) | `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:143 nonzero_cohomology_class`, `:111 betti_one_cycle`, `:134 loopClass_not_coboundary`, `:173 cycle_vs_contractible_qpm` | **∅-axiom PURE, scanned 56/0** ✓ |
| **★ `d_r²=0` on every page = `q=±1` sign-propagation REPEATED** | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 dsq_zero_universal_delta4`; `:62 leibniz_universal_delta4` (the spectral-sequence product / graded-relation slot) | **∅-axiom PURE, scanned 5/0** ✓ |
| the page differential `d_r` = the connecting `δ` (one `delta` op, shifted by `r`) | `Lib/Math/Cohomology/Delta/Core.lean:54 delta`, `deltaAt` | ∅-axiom PURE ✓ (`homological_algebra.md`) |
| growing iteration-character (the page tower strictly ascends until it stabilizes) | `Theory/Raw/MuNuMirror.lean:80 succ_not_idempotent` | **∅-axiom PURE, scanned 8/0** ✓ |
| `q=+1` split/closure an exact page collapses to (a degenerate page = direct sum) | `Lib/Math/Order/GaloisConnection.lean:126 clo_idempotent`; `Lib/Math/Order/FenchelMoreau.lean:134 biconj_idempotent`, `:152 closed_iff_fixed` | **∅-axiom PURE, scanned 15/0, 18/0** ✓ |
| the escape / faithful residue (the `q=−1` pole's kernel) | `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective`, `:47 object1_injective` | ∅-axiom PURE ✓ |
| cross-frame | `homological_algebra.md` (derived functor = `Residue(L,C)`, the operation NAMED — this note ITERATES it), `homology.md` (`ker δ/im δ`, `∂²=0`), `de_rham.md` (`H*=ker d/im d`, Stokes), `sheaf_theory.md` (local-to-global SS = the resolution tower), `continuity.md`/`derivative.md` (resolution dial), `cardinality.md` (`q=−1` escape), `golden_ratio.md`/`gaussian_clt.md`/`differential_equations.md` (`q=+1` Banach fixed point) | prior, ∅-axiom ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root with the `E213.` module prefix):**
`E213.Lens.Foundations.ResidueReentry` **14/0**; `E213.Lib.Math.Analysis.ResolutionShift` **17/0**;
`E213.Lib.Math.Foundations.ResidueTag` **55/0**; `E213.Lib.Math.Probability.Limit.DyadicCompletion` **32/0**;
`E213.Lib.Math.Cohomology.Examples.BettiKernel` **11/0**; `E213.Lib.Math.Cohomology.Examples.NonzeroBetti`
**56/0**; `E213.Lib.Math.Cohomology.Delta.V4Capstone` **5/0**; `E213.Theory.Raw.MuNuMirror` **8/0**;
`E213.Lib.Math.Order.GaloisConnection` **15/0**; `E213.Lib.Math.Order.FenchelMoreau` **18/0** — all pure, 0
dirty. The purity claim rests on the fresh scan, not docstrings.

## Conceptual-only / absent legs (honest)

- **`SpectralSequence` / `Page` / `E_r` / `d_r` / `Filtration` / `gradedAssoc` / `E_∞` / `abutment` /
  Leray / Serre / Grothendieck OBJECTS — ABSENT, located.** Grep over `lean/E213` for `SpectralSequence`/
  `spectral_sequence`/`Page`/`E_r`/`pageDiff`/`d_r`/`Filtration`/`gradedAssoc`/`abutment`/`Einfty`/`E_infty`/
  `leray`/`serre`/`grothendieck spectral`/`hyperhomology` returns **zero Lean declarations**. The only hit is a
  *physics docstring comment* — `Lib/Physics/AlphaEM/LoopVertexGraduation.lean:45` ("Filtration spectral
  sequence: the `d_r` differential increases filtration depth by `r`; at page `r` the surviving classes have
  α-coupling order `r+1`. Hodge-De Rham spectral sequence formalisation is also a substantial undertaking…
  recorded at the **interpretive** level, NOT a cup-axiom derivation") — which itself flags the object as
  unbuilt and interpretive. There is **no** filtered/bigraded complex object, **no** `Page` indexed by `r` with
  a `d_r` field and the `E_{r+1}=H(E_r)` recursion as a Lean def, **no** `E_∞`/abutment, **no** Leray/Serre/
  Grothendieck instance. **This is the precise missing leg** — the iteration-of-the-residue twin of
  `homological_algebra.md`'s missing graded `Ext^n`/resolution/exact-sequence object and `sheaf_theory.md`'s
  missing presheaf-bundle. The *residue mechanism* (`reduced_betti_d4_contractible`, `delta`, `dsq_zero`), the
  *iteration / re-entry* (`residue_perpetually_reenters`), the *resolution-dial index* `r`
  (`IsResolutionShift_compose`, `cutHalfIter`), the *`d_r²=0` per page* (`dsq_zero_universal_delta4`), and the
  *`q=±1` convergence/escape tag* (`ResidueTag`, `golden_is_converge`, `orbit_to_center_completion` /
  `residue_reentry_never_closes`) are each built and PURE; the named filtered/bigraded `E_r`-with-`d_r` object
  that would weld them is the open target. A suggested buildable witness: a *finite, terminating* page tower on
  the built Δ⁴/`NonzeroBetti` cochain complex (a two-page example degenerating at `E_2`), exhibiting one
  concrete `E_{r+1}=H(E_r)` step + its `q=+1` stabilization — the spectral-sequence analogue of `NonzeroBetti`'s
  nonzero-`H¹` witness, decidable and `Quot`-free.
- **The bicomplex / filtered total-complex object — ABSENT.** The double grading (degree `n` × filtration `p`)
  has no Lean type; the single-grading cochain complex (`Cochain n k`) is built, the bigraded one is not. The
  two filtrations giving the two SS of a bicomplex (the heart of the classical theory) are conceptual.
- **`E_∞ ≅ gr_F(H*)` (the abutment isomorphism) — ABSENT as a theorem.** The fold-height grading and its
  per-level `ker/im` residue are built (`kerSizeDelta`); the statement that the stabilized page equals the
  filtration-graded total cohomology is conceptual at the named-object level (no `E_∞`/`gr_F` to equate). Same
  shape as `de_rham.md`'s missing de Rham comparison iso.
- **A spectral sequence = the residue operation iterated *as one theorem*** — this identification is the
  decomposition's reading. Lean certifies each leg separately (`residue_perpetually_reenters` for the iteration;
  `IsResolutionShift_compose` for the index `r`; `reduced_betti_d4_contractible`/`delta`/`dsq_zero` for each
  page-residue; `converge_residue_fixed`/`golden_is_converge` for `E_∞`); the single theorem welding a named
  `SpectralSequence` object into "the orbit of `Residue(−,−)` under self-composition, indexed by the resolution
  dial, converging to the `q=+1` fixed point" is conceptual framing on verified PURE objects — the same shape
  `homological_algebra.md`'s "derived functor = the residue-taking operation" identification has.

> Axiom-purity note: every theorem cited was freshly scanned with `tools/scan_axioms.py` this session (run from
> repo root with the `E213.` module prefix). `banach_fixed_point_modulated` lives under the sub-namespace
> `E213.Lib.Math.Analysis.BanachFixedPoint.CompleteMetricModulusMod` and is cited here via its canonical
> delegation `ResidueTag.converge_residue_fixed` (ResidueTag scanned 55/0); the standalone module tally is not
> claimed. The purity claim rests on the fresh scans, not docstrings.
