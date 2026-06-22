# Decomposition: Galois cohomology (group cohomology H^n(G,M), cocycles/coboundaries, H¹ = crossed-homs-mod-principal, Hilbert's Theorem 90, the long exact sequence, the Brauer group H²(G,L*), the connecting map / Kummer theory)

*A FRESH decomposition per `../README.md` (model v7.1), at the join of `homological_algebra.md` (the
residue-taking operation, NAMED) and `galois.md`/`galois_correspondence.md` (the Galois G-action,
`Fix⊣Inv`, the `q=±1` solvability tower). The hypothesis to **test, not re-skin**: Galois cohomology is
the calculus's **residue-taking operation applied SPECIFICALLY to the Galois group's action** —
`H^n(G,M) = Residue(L,C)` with `C` = the `M`-with-`G`-action complex, `L` = the **G-invariants reading**
on `M`, graded by `n`, tagged `q=±1`. The single NEW datum (beyond the two neighbors): **Hilbert's
Theorem 90 (`H¹(Gal(L/K), L*) = 0`) is a `q=+1` VANISHING of the MULTIPLICATIVE character's first
residue** — the `×↦·` arrow (`det2_mul`/`legendre_mul`/`det_holonomy_eq_one`) has no `H¹` obstruction,
tying a cohomology-vanishing to the calculus's central character arrow. And the closest GROUNDED analogue
of a nonzero `H¹` is the repo's `NonzeroBetti` hollow-triangle `b₁=1` (`loopClass_not_coboundary`), the
`q=−1` obstruction the multiplicative `H¹` does NOT have. The named `GroupCohomology`/`cocycle`/`Hilbert90`/
`Brauer`/`crossedHom` objects are predicted-ABSENT — grep-confirmed below.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **`G`-module complex**: the Galois group `G = Gal(L/K)` (a
  composition-closed family of `C`-preserving self-readings, `groups.md`'s `Aut(C)`,
  `galois.md`'s `Fix⊣Inv` data) **acting on** a coefficient module `M` (the additive group `L`, the
  multiplicative group `L*`, μ_n, …). The cochain complex is the **same simplicial nesting** every
  cohomology note reads (`homological_algebra.md`'s `C`): `Cⁿ(G,M) = {functions Gⁿ → M}`, graded by
  `n`, with the coboundary `δ : Cⁿ → Cⁿ⁺¹` between adjacent degrees (the `homology.md`/`de_rham.md`/
  `sheaf_theory.md` `delta`, `Delta/Core.lean`). `C` carries the README's two read-off axes — a
  **fold-height** (the degree `n`) and a **direction/orientation bit** (the alternating sign in `δ`'s
  face-sum). Nothing field-theoretic is a primitive: `C` is the `G`-action + the graded function-complex.
  The Galois group itself, in the in-repo cyclotomic instance, is `Gal(ℚ(ζ₅)/ℚ) ≅ C₄`
  (`galois_group_is_C4`) — a genuine, ∅-axiom Galois group to anchor "the `G` of `H^n(G,M)`".

- **Reading `L` — the G-INVARIANTS reading on `M`, and its derived functor.** This is the genuinely
  specific framing Galois cohomology supplies: the reading slot is occupied by **`M ↦ Mᴳ`** (the
  `G`-fixed submodule) — which is *exactly* `galois.md`'s `Fix` reading, here read on the coefficient
  module instead of on the sub-construction lattice. `Mᴳ` is **left-exact but NOT right-exact**: it
  fails to preserve `ker=im` past degree 0, and the failure is the residue. So Galois cohomology is
  `homological_algebra.md`'s recipe instantiated at `L = (−)ᴳ`: *resolve, apply the non-exact
  invariants functor, read the `ker δ/im δ` residue degree by degree* — `H^n(G,M) = R^n((−)ᴳ)(M) =
  Ext^n_{ℤG}(ℤ, M)`. The reading IS the residue-taking operation, with `(−)ᴳ` the non-exact functor.

- **Residue — the `q=±1` tag, graded by `n`, read on the `G`-action.**
  - **`q=+1` (the exact part) — `H⁰(G,M) = Mᴳ`.** In degree 0 the invariants functor is exact: the
    residue is empty, the readout IS `Mᴳ` itself — the `G`-fixed points. This is `galois.md`'s `Fix`,
    `galois_correspondence.md`'s closed/fixed elements, the `clo`-converging pole (`clo_idempotent`,
    `converge_residue_fixed`). The part that closes.
  - **`q=−1` (the first obstruction residue) — `H¹(G,M)` = crossed-homs mod principal.** A
    **1-cocycle** (crossed homomorphism) is `a : G → M` with `a(στ) = a(σ) + σ·a(τ)` (closed under
    `δ`); a **1-coboundary** (principal) is `a(σ) = σ·m − m` for some `m` (in `im δ⁰`); `H¹ = cocycles
    / coboundaries = ker δ¹ / im δ⁰`. This is the **SAME `ker δ/im δ` residue** as `de_rham`'s `H*_dR`
    and `sheaf`'s `H^{>0}` — the closed-not-exact obstruction, "forced (cocycle) but not captured (not
    a coboundary)". The first twists/torsors the invariants-reading cannot capture (the `q=−1` escape,
    `escape_residue_outside`/`object1_not_surjective`).
  - **The connecting map `δ` / the long exact sequence** = the `q=±1` sign-propagation threading the
    degrees: a short exact sequence of `G`-modules `0→A→B→C→0` gives `…→Hⁿ(A)→Hⁿ(B)→Hⁿ(C) →δ→
    Hⁿ⁺¹(A)→…` with `δ∘δ=0` so `ker=im` threads through. The connecting `δ` IS `homology.md`'s `∂`/
    `de_rham.md`'s `d` (one `delta` op); `δ²=0` IS `dsq_zero_universal_delta4` — orientation bits
    cancelling pairwise. **Kummer theory** is one application of this `δ`: the sequence
    `1→μ_n→L*→(x↦xⁿ)→L*→1` connects `K*/(K*)ⁿ → H¹(G,μ_n)` precisely through this connecting map.

## ★ Hilbert's Theorem 90 — the `q=+1` VANISHING of the multiplicative character's first residue

`H¹(Gal(L/K), L*) = 0`. The first cohomology of the **multiplicative** coefficient group is **empty**.
In the calculus this is not a sporadic fact: it is the statement that **the `×↦·` multiplicative
character has no first-degree obstruction residue.** The repo's `×↦·` arrow is one proven object read
across seven fields (`det2_mul`: `det(MN)=det M·det N`; `legendre_mul`: `QR(ab)⟺(QR(a)⟺QR(b))`;
`det_holonomy_eq_one`: the product around a loop is `1` — Noether/holonomy). Theorem 90 says: when the
coefficient module IS that multiplicative group `L*`, the first residue is the `q=+1` (converge/empty)
pole — `ker δ¹ = im δ⁰`, residue empty, the same shape as `reduced_betti_d4_contractible` (`ker δ = im
δ`, the contractible/exact case) rather than `NonzeroBetti`'s `q=−1` hollow cycle. So Theorem 90 is a
**cohomology-vanishing tied to the central character arrow**: the multiplicative reading is "exact at
degree 1" — every multiplicative 1-cocycle is principal (in the cyclic case, `a(σ)=σ(b)/b` for some
`b`, the classical norm-1 ⟹ coboundary statement). This is the single new tie this note adds: the
`×↦·` arrow that runs through parity/det/Legendre/Noether/holonomy ALSO governs *where the first Galois
residue vanishes*. The `det_holonomy_eq_one` flatness ("product around every loop = 1") is the same
`q=+1` triviality, read on a loop instead of on a 1-cocycle.

## H² = the Brauer group — the second residue

`H²(Gal(L/K), L*) = Br(L/K)` classifies central simple algebras split by `L` — the obstruction to
splitting (the relative Brauer group). In the calculus this is the **second-degree obstruction residue**
(`Ext^{>0}` at `n=2`): the `q=−1` residue of the multiplicative reading one degree up from where
Theorem 90 made it vanish. So the multiplicative character's residue **vanishes at `n=1` (Thm 90,
`q=+1`) but reappears at `n=2` (Brauer, `q=−1`)** — exactly `homological_algebra.md`'s pattern that a
non-exact functor's residue is empty in some degrees and nonempty in others, graded by `n`. A **2-cocycle**
(the factor set defining the algebra) mod 2-coboundaries IS `ker δ²/im δ¹` — the same `delta` residue at
degree 2. The repo's nearest grounded 2-cocycle is the physics `Ω` (the "unique non-trivial 2-cocycle",
`b₂=1` in `Filled3CellCohomology`/`OmegaH2Trace`) and `MinkowskiCocycle`'s Markov-valued 1-cocycle — the
*mechanism* (a `delta`-closed function mod coboundaries) is built; the named `Brauer`/`H²(G,L*)` object
is not (grep-confirmed below).

## Re-seeing — ⟨C | L⟩

```
   G-module complex C         =  ⟨ G acting on M | the graded function-complex Cⁿ(G,M), δ between degrees ⟩  (homological_algebra.md's C)
   G = Gal(L/K)               =  groups.md's Aut(C) / galois.md's Fix⊣Inv data (composeList; galois_group_is_C4 = C₄)
   the invariants reading (−)ᴳ =  galois.md's Fix, read on the coefficient module M (left-exact, not right-exact)
   H⁰(G,M) = Mᴳ              =  the q=+1 EXACT part: ker=im, residue empty = galois.md's Fix / closed elements (clo_idempotent)
   1-cocycle a(στ)=a(σ)+σa(τ) =  a δ-closed function G→M  (ker δ¹)
   1-coboundary a(σ)=σm−m     =  a function in im δ⁰
   H¹(G,M) = cocycle/coboundary = the q=−1 FIRST obstruction residue = ker δ¹/im δ⁰  =  de_rham's H*_dR  =  sheaf's H^{>0}
   ★ Hilbert Thm 90: H¹(Gal,L*)=0 = the q=+1 VANISHING of the ×↦· character's first residue (ker δ¹=im δ⁰; det2_mul/legendre_mul/det_holonomy_eq_one)
   H²(G,L*) = Brauer group    =  the q=−1 SECOND residue (split=q+1 / non-split=q−1), the same delta at degree 2
   connecting map δ (LES)     =  the q=±1 sign-alternation propagating  =  homology.md's ∂/d  (one delta op)
   "δ∘δ=0" (complex law)       =  ∂²=0  =  dsq_zero_universal_delta4  (orientation bits cancel pairwise)
   long exact sequence        =  δ threads ker=im across degrees; δ²=0 forces it
   Kummer theory              =  the connecting δ on 1→μ_n→L*→L*→1: K*/(K*)ⁿ → H¹(G,μ_n)
```

| classical Galois-cohomology object | = the 213 reading | tie | Lean anchor (grep-confirmed) |
|---|---|---|---|
| `H^n(G,M)` (derived functor of `(−)ᴳ`) | `Residue((−)ᴳ ∘ resolution, C)`, graded `q=±1` | `homological_algebra.md` (NAMED operation) | residue-mechanism legs below (object ABSENT) |
| `H⁰(G,M) = Mᴳ` (invariants) | the `q=+1` exact part: `ker=im`, residue empty | `galois.md`'s `Fix` (closed elements) | `clo_idempotent` (`GaloisConnection.lean:126`) |
| `H¹(G,M)` = crossed-homs mod principal | the `q=−1` first obstruction = `ker δ¹/im δ⁰` | `de_rham`/`sheaf` `H^{>0}`; `NonzeroBetti` `b₁=1` | `loopClass_not_coboundary` (`NonzeroBetti.lean:134`) |
| ★ Hilbert Thm 90 `H¹(Gal,L*)=0` | `q=+1` VANISHING of the `×↦·` character's 1st residue | the multiplicative character arrow | `det2_mul`, `legendre_mul`, `det_holonomy_eq_one`; contrast `reduced_betti_d4_contractible` |
| `H²(G,L*)` = Brauer group | the `q=−1` 2nd residue (split=`q+1`/non-split=`q−1`) | `homological_algebra.md` (graded residue) | 2-cocycle mechanism: `MinkowskiCocycle`, `Ω` (object ABSENT) |
| connecting map `δ` / LES | `q=±1` sign-propagation = `∂`/`d` | `homology.md` (`∂`), `de_rham.md` (`d`) | `Delta/Core.delta` (`Core.lean:54`) |
| `δ²=0` (complex law) | orientation bits cancel pairwise (`q=−1`) | `homology.md` (`∂²=0`) | `dsq_zero_universal_delta4` (`V4Capstone.lean:41`) |
| `G = Gal(L/K)` | `groups.md`'s `Aut(C)` / `galois.md`'s `Fix⊣Inv` | `groups.md`, `galois.md` | `galois_group_is_C4`, `PermGroup.composeList` |
| cocycle / coboundary (general) | a `delta`-closed function mod `im δ` | `homological_algebra.md` | `MinkowskiCocycle` (1-cocycle), `Ω` (2-cocycle) |

So **`H^n(G,M)`, the cocycle/coboundary residue, Theorem 90, the Brauer group, and the connecting `δ`
are ONE machine** — `homological_algebra.md`'s `Residue(L,C)` recipe with `L = (−)ᴳ` (the Galois
invariants reading), graded by `n` and tagged `q=±1`. Galois cohomology = (homological algebra's residue
operation) applied to (galois's G-action), fusing the two neighbor notes with one new tie: Thm 90 binds
the `×↦·` arrow to a `q=+1` vanishing.

## LEVERAGE — does Galois cohomology NAME a new primitive, or is it the residue operation on the G-action?

**Verdict: EXTEND by consolidation + one new cross-tie (PREDICTION at the named-object level).** Galois
cohomology adds **no new primitive**: it is `homological_algebra.md`'s already-named residue-taking
operation, instantiated at the specific reading `L = (−)ᴳ` (`galois.md`'s `Fix` on the coefficient
module), with the `G`-action `C` supplied by `groups.md`/`galois.md`. The genuinely new datum is the
**Theorem-90 tie**: the `q=+1` vanishing of the multiplicative character's first residue, binding the
calculus's central `×↦·` arrow to a cohomology-vanishing. The structural skeleton + every load-bearing
residue-mechanism leg is ∅-axiom built; the *named* `GroupCohomology`/`Hilbert90`/`Brauer`/`crossedHom`
objects are ABSENT (grep-confirmed), the precise missing leg located exactly like
`homological_algebra.md`'s missing `Ext^n` object. Leg by leg, honest.

**(1) `H^n(G,M)` = the residue operation on the G-action — the consolidation, not a new edifice.**
`H^n(G,M) = Ext^n_{ℤG}(ℤ,M) = R^n((−)ᴳ)(M)` is, term-for-term, `homological_algebra.md`'s
`Residue(L,C)` with `L` = "the non-exact functor `(−)ᴳ` composed with a resolution". The calculus
already takes this residue; Galois cohomology is the name for what it does when the non-exact functor is
the Galois invariants `Fix`. The `q=±1` grading is the residue tag (`ResidueTag`, `residue_tag_two_poles`
`:228`, PURE 55/0): `H⁰=Mᴳ` is the `q=+1` exact part (`converge_residue_fixed` `:160`), `H^{>0}` the
`q=−1` escape (`escape_residue_outside` `:133` → `object1_not_surjective`).

**(2) ★ `H¹(G,M)` = crossed-homs mod principal = the `ker δ/im δ` residue, with `NonzeroBetti` the
closest GROUNDED nonzero-`H¹` witness.** A crossed homomorphism is a `δ`-closed function (1-cocycle);
principal = a 1-coboundary (`im δ⁰`); `H¹ = ker δ¹/im δ⁰`. The repo's most literal grounded analogue of a
*nonzero first cohomology* is `NonzeroBetti.lean` (56/0 PURE, freshly scanned): the hollow triangle
S¹=∂Δ² has `loopClass_not_coboundary` (`:134` — the all-ones edge cochain `111` is a 1-cocycle that is
NOT a 1-coboundary), `betti_one_cycle` (`:111` — `kerSize1=8, imSize0=4`, so `|H¹|=2>1`, `b₁=1`), and
`nonzero_cohomology_class` (`:143` — a witnessed element of `ker δ¹/im δ⁰`). `cycle_vs_contractible_qpm`
(`:173`) tags the contrast via `ResidueTag`: the cycle = `escape` (`q=−1`, `im δ⁰ ⊊ ker δ¹`,
`multiplier=−1`) vs the contractible Δ⁴ (`reduced_betti_d4_contractible`, `ker=im`) = `converge`
(`q=+1`, `multiplier=+1`). This is *exactly* the `H¹≠0` vs `H¹=0` split Galois cohomology lives by — the
repo has a concrete ∅-axiom nonzero-`H¹` and its empty-`H¹` complement, the two poles a Galois `H¹`
witnesses for twists/torsors. (This is the closest BUILT analogue; the `H¹(G,M)` *for a Galois G-action*
as a named object is absent.)

**(3) ★ Hilbert Theorem 90 = the `q=+1` vanishing of the `×↦·` character's first residue — the new
tie.** `H¹(Gal(L/K),L*)=0` says the multiplicative coefficient group has empty first residue. The
calculus's `×↦·` arrow is PURE-built and runs through seven fields: `det2_mul` (`det(MN)=det M·det N`,
`SternBrocotMarkov.lean:104`, PURE), `legendre_mul` (`LegendreMultiplicative.lean:77`, PURE 5/0),
`det_holonomy_eq_one` (`HolonomyLattice.lean:136`, PURE 26/0 — the product around every loop is `1`).
Theorem 90 is the statement that *this very arrow*, read as the coefficient module of `H¹`, sits at the
`q=+1` empty-residue pole — the same `ker=im` shape as `reduced_betti_d4_contractible` (PURE), NOT the
`q=−1` `NonzeroBetti` shape. The `det_holonomy_eq_one` flatness ("loop product = 1") is the *same* `q=+1`
triviality of the multiplicative reading, read on a loop rather than a 1-cocycle — so Thm 90 and Noether
flatness are one `q=+1` multiplicative-character vanishing in two clothes. This passes the re-skin guard:
it is a *prediction tying two previously-separate corpus objects* (the `×↦·` arrow ⇄ the Galois `H¹`
vanishing), not a re-description. Honest: there is **no `Hilbert90` theorem object** — the tie is the
identification of Thm 90's `H¹=0` with the `q=+1` empty-residue pole the corpus proves for the
multiplicative character generally.

**(4) `H²(G,L*)` = the Brauer group = the second residue.** The Brauer group is the `q=−1` obstruction
residue at degree 2 — the multiplicative character's residue REAPPEARING one degree above where Thm 90
made it vanish, exactly `homological_algebra.md`'s "graded by `n`, empty in some degrees, nonempty in
others". A 2-cocycle (factor set) mod 2-coboundaries is `ker δ²/im δ¹`. The repo's nearest grounded
2-cocycle mechanism is the physics `Ω` (the "unique non-trivial 2-cocycle", `b₂=1`,
`OmegaH2Trace.lean:8`, `Filled3CellCohomology`) and `MinkowskiCocycle`'s 1-cocycle
(`minkowski_is_markov_valued_cocycle` `:46`, PURE 6/0): the *delta-closed-mod-coboundary mechanism* is
built; the named `Brauer`/`H²(G,L*)`/central-simple-algebra object is ABSENT.

**(5) The connecting map `δ` / long exact sequence / Kummer theory = `dsq_zero` sign-propagation.** The
connecting map of the long exact sequence is `homology.md`'s `∂`/`de_rham.md`'s `d` — one `delta` op
(`Delta/Core.lean:54`); the complex law `δ²=0` is `dsq_zero_universal_delta4` (`V4Capstone.lean:41`,
PURE) — orientation bits cancelling pairwise, the `q=−1` direction-bit at a two-step composite. The long
exact sequence is the `q=±1` tag *displayed degree by degree*. **Kummer theory** is one application: the
connecting `δ` on `1→μ_n→L*→L*→1` realizes `K*/(K*)ⁿ ≅ H¹(G,μ_n)` (when μ_n ⊆ K), the radical
extensions read as the first multiplicative residue — `galois_correspondence.md`'s `Gal(ℚ(ζ₅)/ℚ)≅C₄`
(`galois_group_is_C4`, PURE 4/0) is exactly a cyclotomic instance of the `G` such a sequence lives over.

**Honest boundary — Lean-built vs absent.**
- *Lean-built (∅-axiom, scanned PURE this session):* (a) the **residue mechanism `ker δ/im δ`** that IS
  `H^n` — `delta` (`Delta/Core.lean:54`), `dsq_zero_universal_delta4` (`V4Capstone.lean:41`),
  `reduced_betti_d4_contractible`/`kerSizeDelta` (`BettiKernel.lean:63,42`); (b) the **nonzero-`H¹`
  witness** (crossed-hom-mod-principal made concrete) — `loopClass_not_coboundary`, `betti_one_cycle`,
  `nonzero_cohomology_class`, `cycle_vs_contractible_qpm` (`NonzeroBetti.lean:134,111,143,173`, **56/0
  PURE**); (c) the **`q=±1` tag** grading it — `ResidueTag`/`escape_residue_outside`/
  `converge_residue_fixed`/`residue_tag_two_poles`/`multiplier_unimodular`
  (`ResidueTag.lean:73,133,160,228,86`, **55/0 PURE**); (d) the **`×↦·` character** (Thm 90's vanishing
  arrow) — `det2_mul` (`SternBrocotMarkov.lean:104`), `legendre_mul` (`LegendreMultiplicative.lean:77`,
  5/0), `det_holonomy_eq_one` (`HolonomyLattice.lean:136`, 26/0), all PURE; (e) the **`q=+1` closure**
  (`H⁰=Mᴳ` exact part / split) — `clo_idempotent` (`GaloisConnection.lean:126`, 15/0); (f) the **Galois
  `G`** — `galois_group_is_C4`/`golden_real_subfield` (`CyclotomicFive.lean:66,79`, **4/0 PURE**),
  `PermGroup.composeList` (`groups.md`'s `Aut`-family); (g) **cocycle exemplars** — `MinkowskiCocycle`
  (1-cocycle, `:46`, 6/0 PURE), the physics 2-cocycle `Ω` (`OmegaH2Trace`/`Filled3CellCohomology`); (h)
  the **escape/faithful residue** — `object1_not_surjective`/`object1_injective`
  (`FlatOntologyClosure.lean:61,47`, PURE).
- *Conceptual-only / the precise missing leg (the `homological_algebra.md`-style gap): the named
  Galois-cohomology OBJECTS are ABSENT.* Grep over `lean/E213` for `GroupCohomology`/`groupCohomology`/
  `Hilbert90`/`hilbert90`/`Brauer`/`crossedHom`/`crossed`(-as-cohomology) returns **zero Galois-cohomology
  declarations**. There is **no** `H^n(G,M)`/group-cohomology object, **no** `Hilbert90` theorem, **no**
  `Brauer` group / central-simple-algebra type, **no** `crossedHom`/principal-coboundary object on a
  `G`-action, **no** `groupRing`/`Ext_{ℤG}`. The only matches are: `crossed` = the ratio-Lens "crossed
  readings" (`RatioLensFounding.lean`, unrelated); `cocycle` = `MinkowskiCocycle` + the physics `Ω`
  2-cocycle (related mechanism, not group cohomology). This is the SAME shape as
  `homological_algebra.md`'s missing `Ext^n` object and `galois.md`'s missing field-theoretic instance:
  the *residue mechanism* (`ker δ/im δ`), the *grading tag* (`q=±1`), the *exact/`q=+1` part*
  (`clo`/`ker=im`), the *connecting `δ`* (`delta`/`dsq_zero`), the *Galois `G`* (`galois_group_is_C4`),
  the *cocycle mechanism* (`MinkowskiCocycle`/`Ω`), and the *`×↦·` character* (Thm 90's arrow) are each
  built and PURE; the **`H^n(G,M)`/`Hilbert90`/`Brauer` objects that would weld them** are the named open
  legs.

So: **EXTEND by consolidation (no new primitive — Galois cohomology = `homological_algebra.md`'s residue
operation at `L=(−)ᴳ` on `galois.md`'s G-action) + one new PREDICTION-grade tie (Thm 90 `H¹(Gal,L*)=0` =
the `q=+1` vanishing of the `×↦·` character's first residue), cashed at the residue-mechanism /
grading-tag / character-arrow level; PARTIAL because the `H^n(G,M)`/`Hilbert90`/`Brauer`/`crossedHom`
OBJECTS are absent — the named open legs, not hand-waves.**

## Revelation (consolidation: Galois cohomology = the residue operation applied to the Galois G-action; Thm 90 = the `q=+1` vanishing of the multiplicative character)

**Collapse — `H^n(G,M)`, crossed homs, Theorem 90, the Brauer group, and Kummer theory are ONE machine:
`homological_algebra.md`'s residue-taking operation, with the reading fixed to the Galois invariants
`(−)ᴳ`.** `homological_algebra.md` named the residue operation in the abstract (a derived functor =
`Residue(L,C)` graded by `n`); `galois.md` named the Galois G-action (`Fix⊣Inv`, the `q=±1` solvability
tower). Galois cohomology is their **product**: run the residue operation with `L = Fix = (−)ᴳ`. The
single forcing sentence, read across the degrees:

- **`q=+1` (the exact part = `H⁰=Mᴳ` = the invariants).** In degree 0 the invariants reading is exact —
  `ker=im`, residue empty, the readout IS `Mᴳ` = `galois.md`'s `Fix`/closed elements
  (`converge_residue_fixed`, `clo_idempotent`). The `q=+1` corner: "the invariants capture everything;
  no obstruction".
- **★ `q=+1` AGAIN, but at degree 1, for the MULTIPLICATIVE coefficient — Hilbert Theorem 90.** The
  one place a first cohomology *vanishes*: `H¹(Gal,L*)=0`. The `×↦·` character (`det2_mul`/`legendre_mul`/
  `det_holonomy_eq_one`) — the calculus's most-reused arrow — has **no first-degree obstruction**. The
  same `ker=im` empty-residue shape as `reduced_betti_d4_contractible`, NOT the `q=−1` `NonzeroBetti`
  hollow cycle. The multiplicative reading is "exact at degree 1": every multiplicative 1-cocycle is
  principal. This is the new datum: the character arrow that governs determinant/parity/Noether/holonomy
  ALSO governs *where the first Galois residue is empty* — Thm 90 and `det_holonomy_eq_one` flatness are
  one `q=+1` multiplicative vanishing.
- **`q=−1` (the obstruction = the residue escapes).** For a general coefficient at degree 1
  (`H¹(G,M)`, twists/torsors) and for the multiplicative coefficient at degree 2 (`H²(G,L*)`, the Brauer
  group), the invariants reading's failure to be exact IS the residue: `ker δ/im δ`, closed-not-exact
  (`escape_residue_outside`, `object1_not_surjective`), the `NonzeroBetti` `b₁=1` shape made concrete.
  The connecting `δ` propagating it between degrees (the long exact sequence, Kummer's `δ`) is
  `dsq_zero_universal_delta4`.

This passes the re-skin guard at the level `homological_algebra.md` reached: it does not re-describe
group cohomology — it **identifies `H^n(G,M)` with the calculus's residue operation at `L=(−)ᴳ`**,
grounded by the *same* PURE `ker δ/im δ` mechanism (`reduced_betti_d4_contractible`,
`loopClass_not_coboundary`, `delta`, `dsq_zero_universal_delta4`) and the *same* `q=±1` tag (`ResidueTag`)
that certify homology/de Rham/sheaf — AND it adds a genuinely new tie: **Theorem 90 binds the corpus's
central `×↦·` character to a `q=+1` cohomology-vanishing**, a prediction connecting two previously-separate
built objects (the character arrow and the empty-residue pole). The deepest line: **Galois cohomology is
`homological_algebra.md`'s residue operation with the Galois invariants as the reading — `H⁰=Mᴳ` the
`q=+1` exact part, `H¹` the `q=−1` first obstruction (empty for the `×↦·` character = Thm 90), `H²(G,L*)`
the Brauer second residue, the connecting `δ` the sign-alternation, Kummer the `δ` on the n-th-power
sequence.** **EXTEND by consolidation; no new axis; interior model v7.1 holds.** The one genuine absence
— the `H^n(G,M)`/`Hilbert90`/`Brauer`/`crossedHom` object — is located precisely: the Galois-action twin
of `homological_algebra.md`'s missing `Ext^n` and `galois.md`'s missing field-theoretic correspondence.

## Note for the technique

**No new primitive; a two-note fusion + one new cross-tie.** Galois cohomology does not extend model
v7.1; it *applies* one already-named reading-pair to another already-named operation:
- the **residue-taking operation** (`homological_algebra.md`, batch-4 `homology.md`) supplies the
  machine: resolve, apply a non-exact reading, read `ker δ/im δ` degree by degree, tag `q=±1`;
- the **Galois invariants reading `(−)ᴳ` = `Fix`** (`galois.md`/`galois_correspondence.md`) supplies the
  specific non-exact reading and the `G`-action `C` (`groups.md`'s `Aut`-family, `galois_group_is_C4`);
- the **`×↦·` character** (`determinant.md`/`quadratic_reciprocity.md`/`noether.md`) supplies the new
  tie: its coefficient-module reading vanishes at `H¹` (Theorem 90) — the `q=+1` empty-residue pole.

The lesson for the model: **a `Residue(L,C)` where `L` is the Galois invariants reading is Galois
cohomology; the character arrow that the residue reads decides which degrees vanish.** `H⁰=Mᴳ` is the
`q=+1` exact part; `H¹` the `q=−1` first obstruction; **but for the multiplicative character `L*` the
first obstruction is empty (Theorem 90, `q=+1`)** — the central `×↦·` arrow's first Galois residue is
the converge/empty pole, the same vanishing as `det_holonomy_eq_one` flatness. `H²(G,L*)`=Brauer revives
the obstruction one degree up. This is the sharpest confirmation that the residue operation is
*reading-parametric*: change `L` to `Fix`, feed it the Galois `G`-action, and homological algebra becomes
Galois cohomology with Theorem 90 falling out as the character arrow's `q=+1` corner. The one genuine
absence — the `H^n(G,M)`/`Hilbert90`/`Brauer` object — is located precisely: every leg it would need
*structurally* (the `ker δ/im δ` residue with a concrete nonzero-`H¹` witness, the `δ²=0` complex law,
the `q=±1` grading, the Galois `G`, the cocycle mechanism, the `×↦·` character) is present and PURE; only
the named graded object is open.

---

## Verified Lean anchors (file:line — all grep/Read-verified on `lean/E213`; purity scanned via `tools/scan_axioms.py` from repo root this session)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| **★ `H¹` = crossed-homs mod principal = `ker δ¹/im δ⁰` (the closest BUILT nonzero-`H¹` witness)** | `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:134 loopClass_not_coboundary`, `:111 betti_one_cycle`, `:143 nonzero_cohomology_class`, `:173 cycle_vs_contractible_qpm`, `:126 loopClass_is_cocycle` | **∅-axiom PURE, scanned 56/0** ✓ |
| **★ `H^n` = `Residue(L,C)` graded `q=±1` (the residue-recipe, NAMED)** | `Lib/Math/Foundations/ResidueTag.lean:73 ResidueTag`, `:86 multiplier_unimodular`, `:133 escape_residue_outside`, `:160 converge_residue_fixed`, `:180 golden_is_converge`, `:228 residue_tag_two_poles` | **∅-axiom PURE, scanned 55/0** ✓ |
| **★ `H⁰` exact part / Thm-90 empty-residue shape (`ker=im`, `q=+1`)** | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 reduced_betti_d4_contractible`, `:42 kerSizeDelta`, `:47/:52 kerSize_5_0/1` | **∅-axiom PURE** ✓ (contrast to NonzeroBetti) |
| **★ Hilbert Thm 90's vanishing arrow = the `×↦·` multiplicative character** | `…/Real213/Markov/SternBrocotMarkov.lean:104 det2_mul`; `…/ModArith/LegendreMultiplicative.lean:77 legendre_mul`; `…/Real213/ModularGeometry/HolonomyLattice.lean:136 det_holonomy_eq_one` | **∅-axiom PURE** ✓ (`legendre_mul` 5/0; `det_holonomy_eq_one` 26/0; `det2_mul` scanned PURE) |
| **★ connecting `δ` / LES / `δ²=0` (Kummer's `δ`) = `q=±1` sign-propagation** | `Lib/Math/Cohomology/Delta/Core.lean:54 delta`; `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 dsq_zero_universal_delta4` | **∅-axiom PURE** ✓ |
| `H⁰=Mᴳ` = the `q=+1` invariants / closure (`Fix`, split) | `Lib/Math/Order/GaloisConnection.lean:126 clo_idempotent`, `:104 clo` | **∅-axiom PURE, scanned 15/0** ✓ (`galois.md`) |
| the Galois group `G = Gal(L/K)` (the `G` of `H^n(G,M)`) | `Lib/Math/Algebra/Icosahedral/CyclotomicFive.lean:66 galois_group_is_C4` (`Gal(ℚ(ζ₅)/ℚ)≅C₄`), `:79 golden_real_subfield`; `Lib/Math/Algebra/Linalg213/PermGroup.lean : composeList` (`Aut`-family) | **∅-axiom PURE, CyclotomicFive scanned 4/0** ✓ |
| cocycle exemplars (the `delta`-closed-mod-coboundary mechanism) | `…/Real213/Minkowski/MinkowskiCocycle.lean:46 minkowski_is_markov_valued_cocycle` (1-cocycle); `Lib/Physics/AlphaEM/OmegaH2Trace.lean:8` + `Filled3CellCohomology` (the `Ω` 2-cocycle, `b₂=1`) | **∅-axiom PURE, MinkowskiCocycle scanned 6/0** ✓ |
| escape / faithful residue (the `q=−1` pole's kernel) | `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective`, `:47 object1_injective` | **∅-axiom PURE** ✓ |
| cross-frame | `homological_algebra.md` (the residue operation, NAMED; `Ext_{ℤG}`), `galois.md` / `galois_correspondence.md` (`Fix⊣Inv`, `galois_group_is_C4`, the `q=±1` solvability tower), `homology.md` (`∂`, `∂²=0`), `de_rham.md` (`H*_dR=ker d/im d`), `sheaf_theory.md` (`H^{>0}` obstruction), `groups.md` (`Aut`-family), `quadratic_reciprocity.md` / `determinant.md` / `noether.md` (the `×↦·` character) | prior, ∅-axiom ✓ |

**Fresh purity scans (this session, `tools/scan_axioms.py` from repo root):**
`E213.Lib.Math.Cohomology.Examples.NonzeroBetti` — **56 pure / 0 dirty** (incl. `loopClass_not_coboundary`,
`betti_one_cycle`, `nonzero_cohomology_class`, `cycle_vs_contractible_qpm`).
`E213.Lib.Math.Foundations.ResidueTag` — **55 pure / 0 dirty** (incl. `residue_tag_two_poles`,
`escape_residue_outside`, `converge_residue_fixed`, `golden_is_converge`, `multiplier_unimodular`).
`E213.Lib.Math.Algebra.Icosahedral.CyclotomicFive` — **4 pure / 0 dirty** (`galois_group_is_C4`,
`golden_real_subfield`). `E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative` — **5 pure / 0
dirty** (`legendre_mul`). `E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice` —
**26 pure / 0 dirty** (`det_holonomy_eq_one` PURE). `E213.Lib.Math.Order.GaloisConnection` —
**15 pure / 0 dirty** (`clo_idempotent`). `E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiCocycle`
— **6 pure / 0 dirty** (`minkowski_is_markov_valued_cocycle`). `object1_not_surjective`/`object1_injective`
PURE (`FlatOntologyClosure`, individual scan). `det2_mul` scanned PURE in `SternBrocotMarkov`. Build clean.

## Conceptual-only / absent legs (honest)

- **`GroupCohomology` / `H^n(G,M)` / `Hilbert90` / `Brauer` / `crossedHom` / `groupRing` / `Ext_{ℤG}`
  OBJECTS — ABSENT, located.** Grep over `lean/E213` for `GroupCohomology`/`groupCohomology`/`Hilbert90`/
  `hilbert90`/`Brauer`/`crossedHom`/`groupRing` returns **zero Galois-cohomology declarations**. The only
  `crossed` matches are the ratio-Lens "crossed readings" (`RatioLensFounding.lean`, unrelated to
  cohomology); the only `cocycle` matches are `MinkowskiCocycle` (a Stern-Brocot 1-cocycle) and the
  physics `Ω` 2-cocycle (`OmegaH2Trace`/`Filled3CellCohomology`/`OmegaPostGramFull`) — a *related
  mechanism*, NOT a group-cohomology object. There is **no** `H^n(G,M)` graded object, **no** `Hilbert90`
  vanishing theorem, **no** `Brauer` group / central-simple-algebra type, **no** `crossedHom`/principal
  pair on a `G`-action, **no** group ring / `Ext_{ℤG}`. **This is the precise missing leg** — the
  Galois-action twin of `homological_algebra.md`'s missing `Ext^n` object and `galois.md`'s missing
  field-theoretic correspondence. The *residue mechanism* (`ker δ/im δ`, `delta`, `dsq_zero`,
  `NonzeroBetti`'s nonzero-`H¹`, `reduced_betti_d4_contractible`'s empty-`H¹`), the *`q=±1` grading tag*
  (`ResidueTag`), the *exact/`q=+1` part* (`clo_idempotent`/`ker=im`), the *connecting `δ`*
  (`delta`/`dsq_zero`), the *Galois `G`* (`galois_group_is_C4`/`composeList`), the *cocycle mechanism*
  (`MinkowskiCocycle`/`Ω`), and the *`×↦·` character* (`det2_mul`/`legendre_mul`/`det_holonomy_eq_one`)
  are each built and PURE; the derived-functor object on the Galois action that would weld them is open.
- **Hilbert Theorem 90 as a theorem — ABSENT, identified not asserted.** There is no `H¹(Gal,L*)=0`
  Lean theorem. The note's claim is an *identification*: Thm 90's `H¹=0` IS the `q=+1` empty-residue pole
  (the `reduced_betti_d4_contractible` `ker=im` shape, not the `NonzeroBetti` `q=−1` shape) read on the
  multiplicative character `L*` whose `×↦·` law is PURE-built. The buildable witness this suggests: a
  *cyclic-group* `H¹(Cₙ, L*)` toy whose 1-cocycles are forced principal by the norm-1 condition — the
  multiplicative analogue of `reduced_betti_d4_contractible` (an empty first residue), contrasting
  `NonzeroBetti`'s nonzero first residue. Not built this session; flagged as the located target.
- **The Brauer group `H²(G,L*)` as a named object — ABSENT.** Grep returns zero `Brauer`/CSA declarations.
  The 2-cocycle mechanism is grounded (`MinkowskiCocycle`, `Ω` with `b₂=1`); the named relative-Brauer /
  central-simple-algebra object is open — the same shape as the missing graded `Ext²` object.
- **Galois cohomology = the residue operation on the G-action *as one theorem*** — this identification is
  the decomposition's reading. Lean certifies each leg separately (`NonzeroBetti`/`reduced_betti_*`/`delta`/
  `dsq_zero` for the residue + the `H¹≠0`/`H¹=0` poles; `ResidueTag` for the grading; `clo_idempotent` for
  the exact/`H⁰=Mᴳ` pole; `galois_group_is_C4`/`composeList` for the Galois `G`; `det2_mul`/`legendre_mul`/
  `det_holonomy_eq_one` for Thm 90's `×↦·` arrow); the single theorem welding a named `H^n(G,M)` object
  into "the `q=±1` residue of the Galois invariants functor, graded by `n`, with `H¹(Gal,L*)=0` the
  character's `q=+1` corner" is conceptual framing on verified PURE objects — the same shape
  `homological_algebra.md`'s "derived functor = the residue operation" identification has.

> Axiom-purity note: the load-bearing anchors (`NonzeroBetti` 56/0, `ResidueTag` 55/0, `CyclotomicFive`
> 4/0, `LegendreMultiplicative` 5/0, `HolonomyLattice` 26/0, `GaloisConnection` 15/0, `MinkowskiCocycle`
> 6/0, `reduced_betti_d4_contractible`/`dsq_zero_universal_delta4`/`delta`, `det2_mul`,
> `object1_not_surjective`/`object1_injective`) were grep/Read-verified at the cited file:line and scanned
> PURE this session via `tools/scan_axioms.py` (run from repo root with the `E213.` module prefix). The
> purity claim rests on the fresh scan, not docstrings. No `H^n(G,M)`/`Hilbert90`/`Brauer`/`crossedHom`
> object was cited because none exists — confirmed by grep returning zero such declarations.
