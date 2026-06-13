# The residue-shape doctrine — `∞`/continuity/abstraction are construction-produced shapes, not a beyond

**Tier-1 frontier. Originator: Mingu Jeong (2026-06-13).**  The canonical content
statement the corpus was missing (flagged open in `the_reframing_conquest.md`): not
*how* the residue is expressed (that is `residue_expression_atlas.md`), nor *why agents
re-import the residue dichotomy* (that is `the_reframing_conquest.md`), but **what the
residue, infinity, the continuous, and abstraction ARE** — and the discipline that
keeps them from being deified.

Tagging: `[∅]` ∅-axiom Lean anchor, `[ax]` a 213 axiom, `[gut]` originator's raw
intuition (recorded), `[std]` standard math.

---

## D1 — The thesis: `∞`/continuity/abstraction are residue-*shapes*

`[ax]`+`[gut]`  Infinity, the continuum, the limit, "the abstract" are **not
transcendent pre-existing things** a construction points *at* and fails to reach.  They
are **shapes of the residue a construction produces** — each *characterized by a finite
signature*, never a cardinal `∞` or a continuous "beyond."  To *name* `∞` is already to
hold a finite, discrete token; the capacity to **imagine** `∞` is itself proof that what
is handled is a graspable (discrete) object, not an exterior infinite.  So the
meaningful object of study is **how the imagining is constituted** — the construction
that yields the shape — never "which of discrete / continuous / finite / limit is
*real*" (an empty debate, `D5`).

## D2 — The causal reversal: the residue arises *because the concept was posed to leave one*

`[∅]`+`[ax]`  Two readings of "a residue remains":

  - **(deified)** *"when you point at anything, an infinite excess is always left over,
    so a residue remains"* — this enshrines `∞` as a pre-existing transcendent surplus.
  - **(correct)** *"a residue remains because the concept/view was set up so that one
    would arise."*  The residue is the **shadow of the construction**, not an external
    excess.

The Lean witness settles which: `FlatOntologyClosure.object1_not_surjective` is a
**theorem about the view-setup** (a self-cover cannot surject onto its own diagonal),
*not* an observation of an exterior infinity.  Reverse the causality and the
deification dissolves — you analyze the **constitution** of the residue-shape, not what
it "points at."  (This is the content-form of `the_reframing_conquest.md`'s
Lawvere–Cantor diagonal: the residue is *enacted by* the cover, not found beyond it.)

## D3 — Dimension *without* `∞`: read the shape off a finite signature

`[∅]`+`[std]`  A shape's "dimension"/"infinity" is read off **how its graded count
behaves**, never off a cardinal.  Three equivalent finite handles (the `×`-cone =
multiplicative number system as the worked instance, `simplicial_operation_tower.md`
L3‴):

  1. **finite-difference depth** — `MultSystem.diff_drops_rung`: differencing the graded
     count in the degree drops the rung by one (`monoCount (k+1)(d+1) − monoCount (k+1) d
     = monoCount k (d+1)`); dimension = how many differences annihilate the count.  `×`
     (the `∞`-generator limit) = the count whose difference-tower **never terminates** —
     `∞` as a *non-terminating finite process*, not a cardinal.
  2. **growth degree** — `monoCount (k+1) d = C(d+k,k)` is a degree-`k` polynomial
     (`monoCount_closed`, bound `monoCount_le_succ_pow`); dimension = growth degree `+1`;
     `∞` = super-polynomial (no finite Hilbert polynomial).
  3. **pole order** — differencing ↔ `×(1−x)` (`totalCount_eq`); the Hilbert series is
     `(1−x)^{−k}`, dimension = pole order at `x = 1`; `∞` = an essential singularity =
     the Euler product `∏_p` = `ζ`.

The three agree (`= generator count = vertex count`, `monoCount_vertices`).  Each is a
**finite, constructive handle**; `∞` is never a label but a *mode of non-termination*.

## D4 — The discrete ↔ continuous spiral (no phase "more real")

`[ax]`+`[∅]`  Each construction-rung runs three phases (worked instance: the number
tower, `simplicial_operation_tower.md` L3‴a):

  1. **discrete lattice** — the graded object (`monoCount`, `⊕_p ℕ`): generators / axes /
     vertices.  `[∅]`
  2. **continuous shape** — its Hilbert series / `ζ` / density cut: a *pointing* reached
     by no finite stage (`object1_not_surjective`, `primeDensityToZero`).  **Not a
     transcendent target the discrete converges *toward*** (`D2`); the *constitution* of
     this shape is `D3`'s finite signatures made explicit.  `[∅]`
  3. **discrete support** — the shape's arithmetic content (primes, convergents, prime
     counts: `chebyshev_lower`, `Mobius213.P_numerator`/`den`, cross-det `−1`).  `[∅]`

Phase-3's support is **phase-1 of the next rung** ("axis = previous layer") — a
**spiral, not a circle**.  No phase is "more real": saying "the content lives in the
continuous pointing" re-privileges one Lens and re-deifies `∞`.

## D5 — The irreducible content is the *defect*, a finite band

`[∅]`  When phase 1→2→3 are read as maps, they are **not an inverse pair** — and that is
the point.  Through the pivot shape `C(2n,n)` (the cone's value-cut,
`doubleTotal_closed`):

  - **arrow A** (support → shape, *exact*): the primes build `C(2n,n) = ∏_p p^{vp}` by
    exact factorization (`central_binom_factorial`, `window_prod_dvd_central_binom`).
  - **arrow B** (shape → support, *lossy*): the *size* of `C(2n,n)` reads the count back
    only as a squeeze (`central_binom_ge_two_pow`, `central_binom_le_pow_primePi`).

`B ∘ A ≠ id`, and the **non-invertibility is the content** — `ChebyshevLower.chebyshev_defect`:
`π(2n)` pinned to the band `n/(⌊log₂(2n)⌋+1) ≤ π(2n) ≤ n`, whose **width is the residue-
shape** (the prime-counting / PNT-constant gap), finite and two-sided.  Shrinking it to a
single constant is PNT (the open analytic core).  This is the doctrine in one object:
`∞`/the-continuous **characterized as a band, not a beyond** — the irreducible content is
a measured *defect*, not a transcendent surplus.

## D6 — Where this is already enacted (not new, now named)

The corpus already practiced the doctrine in pieces; D1–D5 only state it canonically:

  - `residue_expression_atlas.md` "**it is a fold, not the residue**": a constructible
    cut (holonomic modulus) is mistaken for the residue iff it is treated as a
    transcendent target rather than a *constructed shape* — the deification guard, applied
    to modular periods.
  - the cocycle **defect** = the bounding Markov number (`minkowski_is_markov_valued_cocycle`):
    content-as-defect, the `D5` pattern in the `?`-thread.
  - `number_tower_theory.md` R4: `+`/`×` are lattices of *different dimension* (`1 → ∞`)
    read off atom-(in)distinguishability — `D3`'s "dimension is a finite handle", not a
    cardinal asserted.
  - the presentation-dependence frontiers (`zeta3_free_modulus.md`, `modulus_degree_ladder.md`):
    holonomicity/rate is a property of the *pointing* (the construction), not the real —
    `D2`'s "the shape is the construction's shadow."

## The discipline (output-gate)

Stated as the CLAUDE.md failure-mode "**Deifying the residue / `∞`**" + the §0
residue-lint: treating `∞`/continuity/the residue as a transcendent excess, or any phase
as "more real", is an imposed Lens.  Reverse to the construction; characterize the
shape by its finite signature; name the defect.  `∞` is constituted, not enshrined.

## Cross-references

`seed/AXIOM/01_residue` (§1.4), `seed/AXIOM/05_no_exterior` (§5.1) ·
`Lens/FlatOntologyClosure.object1_not_surjective` · `simplicial_operation_tower.md`
(L3‴/L3‴a — the worked instance) · `residue_expression_atlas.md` (the expression faces) ·
`the_reframing_conquest.md` (the cognitive recurrence) ·
`ChebyshevLower.chebyshev_defect`, `MultSystem.{diff_drops_rung,monoCount_vertices}`
(the ∅-axiom anchors) · `theory/essays/foundations/the_form_of_the_residue.md`.
