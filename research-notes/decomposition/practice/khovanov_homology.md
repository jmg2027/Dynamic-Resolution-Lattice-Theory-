# Decomposition: Khovanov homology / categorification (the cube of resolutions, the Khovanov chain complex, Kh(L) bigraded, graded Euler characteristic = the Jones polynomial, Lee/s-invariant, functoriality)

*A FRESH decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants, the
q=±1 spine, the residue-taking operation, the "decategorify = take the Euler characteristic" pattern).
Builds directly on `knots.md` (the Jones polynomial = the Kauffman bracket state sum over the
crossing-resolution cube, and the **located break**), `homological_algebra.md` (the residue-taking
operation = `ker δ/im δ`, graded, tagged q=±1), `game_theory.md` (the cube = the `{0,1}^n` bit-cube =
`BoolXORFold`'s hypercube), and `derived_categories.md`/the categorification pattern. **The thesis to
test, not re-skin:** Khovanov homology is the calculus's **residue-taking operation applied to knots'
Kauffman state sum** — it CATEGORIFIES the Jones polynomial (a count, a Laurent polynomial) into a
bigraded homology `Kh(L)` (the residue `ker δ/im δ`) whose **graded Euler characteristic = the Jones
polynomial** — exactly the corpus's `decategorify = Σ(−1)ⁱ alternating count` pattern (index_theory's
McKean–Singer, the q=±1 alternating sum). The cube of resolutions = the `{0,1}^crossings` bit-cube
(game_theory's `BoolXORFold` hypercube, 𝔽₂); the Khovanov differential = the `∂` (q=±1 sign,
`dsq_zero`); the bigrading = two fold-height axes; Lee/s = a deformation (the resolution dial).
NO new primitive — it is the residue machine run on knots' resolution cube, the Jones polynomial its
Euler characteristic. Honest grounding up front: **there is no Khovanov / Jones / Kauffman / skein /
categorification object in `lean/E213/`** (grep-confirmed below — the same field-object absence
`knots.md` and `homological_algebra.md` recorded); the legs that are PURE-built are the **bit-cube**
(`BoolXORFold`), the **residue mechanism** (`delta`/`dsq_zero`/`ker δ/im δ`), the **q=±1 alternating
Euler count** (`simplex_face_euler_zero`), and the **q=±1 tag** (`ResidueTag`). The named field object
is the predicted-not-built leg.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **cube of resolutions** of a knot diagram. A diagram with `n` crossings:
  each crossing is *resolved* in one of two ways (the `0`-smoothing or the `1`-smoothing), so a *choice
  of resolution* is a vertex of the hypercube `{0,1}^n`. This is **exactly** `knots.md`'s
  crossing-resolution reading and **exactly** `game_theory.md`'s bit-vector cube: each crossing → a bit,
  the cube of all resolutions = `{0,1}^n` = the 𝔽₂-hypercube `BoolXORFold` folds over. `C` carries the
  README's two read-off axes that the bigrading will read: a **fold-height** (the *homological* degree =
  the number of `1`-smoothings, the Hamming weight = the height up the cube) and a second **fold-height**
  (the *quantum* degree, the count of circles in each resolution, shifted). The crossing's over/under is
  `knots.md`'s **direction bit q=±1** (the writhe shift `[−r]{...}`), exactly as there. Nothing
  classically Khovanov is a primitive: `C` is the bit-cube of resolutions + the graded face-maps along
  its edges. (No `KhovanovComplex`, no Frobenius algebra `A=ℤ[X]/X²`, no `Cob` category enters — see
  Residue / verdict.)

- **Reading `L` — the residue-taking operation applied to the cube (CATEGORIFICATION).** This is the
  genuinely new datum the field supplies, and it is *not* a new reading-axis — it is
  `homological_algebra.md`'s residue recipe with the cube as `C`. The Kauffman bracket state sum
  (`knots.md`) reads each cube vertex to a *number* (a `±q`-power weighted by circle count) and **sums
  with signs** — a *count*, the decategorified output. Khovanov **categorifies** this: instead of
  summing numbers per vertex, assign a *graded vector space* `V^{⊗(circles)}` to each vertex (the
  Frobenius algebra `A`), and a *differential* `δ` along the cube edges (merge/split maps). The reading
  `L` is then **"build the chain complex over the cube, then take homology"** — `homological_algebra.md`'s
  `Residue(F ∘ resolution, C) = ker δ/im δ`, with `F` = the per-vertex vector-space assignment and the
  resolution dial = the cube grading. The Khovanov differential δ is `knots.md`'s/`homology.md`'s `∂`:
  it goes along the cube edges (one `0→1` smoothing flip = one Hamming step up = one fold-height step),
  with a **q=±1 sign per edge** chosen so that **δ²=0** (the alternating-sign edge assignment that makes
  the cube's square faces anticommute — `homology.md`'s "opposite-order face removals carry opposite
  orientation signs that cancel pairwise"). So the Khovanov chain complex = the cube as a chain complex,
  δ = the q=±1-signed cube-edge differential.

- **Residue — `Kh(L) = ker δ/im δ`, BIGRADED, tagged q=±1; and its q=±1 alternating count = the Jones
  polynomial (the categorification identity).** Read the cube-complex's homology degree by degree:
  - `Kh^{i,j}(L) = ker δ / im δ` at homological degree `i`, quantum degree `j` — **verbatim**
    `homological_algebra.md`'s/`homology.md`'s/`de_rham.md`'s `ker δ/im δ` residue, now *bigraded* (two
    fold-height axes). A trivial/contractible direction in the cube leaves no homology (`ker δ = im δ`,
    residue empty, the q=+1 exact part); a non-trivial cycle leaves a nonzero class (q=−1 obstruction
    residue) — exactly `NonzeroBetti`'s "cycle = escape vs contractible = converge".
  - **★ The categorification identity = the q=±1 alternating Euler count.** The defining theorem of
    Khovanov homology is `Σ_{i,j} (−1)ⁱ qʲ dim Kh^{i,j}(L) = V_L(q)` — the **graded Euler
    characteristic** of `Kh(L)` recovers the (unnormalized) Jones polynomial. This is the corpus's
    **`decategorify = take the q=±1 alternating count`** pattern: the alternating sign `(−1)ⁱ` down the
    homological height is the **same** alternating sum as `simplex_face_euler_zero`
    (`Σ_k(−1)ᵏ binom d k = 0`, the Euler/`∂²=0` cancellation) and index_theory's McKean–Singer
    `Σ(−1)ⁱ`. The Jones polynomial *is* the Euler characteristic of the residue; Khovanov homology is the
    **residue whose alternating count is that polynomial** — the count `knots.md` decomposed, *lifted
    back up to the residue it counts*. This is the precise inverse of `knots.md`: there the Jones
    polynomial was read DOWN from the cube as a state-sum count; here the count is read as the Euler
    characteristic of the residue read UP from the same cube.
  - **Lee deformation / s-invariant = a deformation of the differential (the resolution dial /
    direction toggle).** Lee theory perturbs δ (the Frobenius algebra `X²=1` instead of `X²=0`); the
    perturbed homology collapses to two generators per component, and the surviving filtration degree is
    the s-invariant. In the calculus this is the README's **resolution/deformation dial** on the residue
    (a one-parameter dial that changes which part of the cube is exact): the s-invariant is the q=±1
    filtration-height that survives the deformation — a fold-height readout of the deformed residue, the
    same shape as the spectral-sequence convergence-page (`spectral_sequences.md`: the Lee→Khovanov
    spectral sequence is the residue operation *iterated*, the s-invariant living on a later page).
  - **Functoriality = the 2-cell (a cobordism induces a chain map).** A cobordism between links induces a
    map on Khovanov homology — a morphism between two residues. In the calculus this is the
    **2-category of readings**: a map of constructions induces a map of their residues, the naturality
    2-cell `view_factors_through_morphism`/`IsLensMorphism` (`two_cells.md`); functoriality up to sign is
    the same q=±1 direction bit on the 2-cell. (The *ambient* cobordism category `Cob` itself sits at the
    isotopy/colimit break — see verdict.)

## Re-seeing — `⟨C | L⟩ ⊕ Residue(q=±1)`

```
  cube of resolutions C        =  ⟨ {0,1}^n bit-cube of crossing-smoothings | the cube edges ⟩   (knots.md's cube = game_theory's BoolXORFold hypercube, 𝔽₂)
  one resolution vertex        =  a bit-vector in {0,1}^n                                          (each crossing → a bit; Hamming weight = homological height)
  Kauffman state sum (Jones)   =  ⟨ cube | read each vertex to a ±q-power, SUM with signs ⟩        (knots.md: the count = decategorified output)
  Khovanov chain complex       =  CATEGORIFY: a graded V^{⊗circles} per vertex + δ along edges       (homological_algebra's Residue recipe on the cube)
  Khovanov differential δ      =  the q=±1-signed cube-edge map (one 0→1 smoothing = one height step)  (homology.md's ∂; signs make δ²=0)
  δ²=0                          =  cube square-faces anticommute (orientation bits cancel pairwise)    (dsq_zero_universal_delta4)
  Kh^{i,j}(L) = ker δ/im δ     =  Residue(L,C), BIGRADED (two fold-heights: homological i, quantum j)  (homological_algebra's ker δ/im δ, graded)
  Σ(−1)ⁱ qʲ dim Kh^{i,j} = V_L(q)  =  the graded EULER CHARACTERISTIC = the Jones polynomial            (the q=±1 alternating count; simplex_face_euler_zero / McKean–Singer)
  contractible cube direction  =  ker δ = im δ, residue empty                                          (q=+1 exact; reduced_betti_d4_contractible)
  nonzero Kh class             =  closed-not-exact cycle                                               (q=−1 obstruction; NonzeroBetti.nonzero_cohomology_class)
  Lee deformation / s-invariant =  a deformation dial on δ; surviving filtration height = s            (resolution/deformation dial; Lee→Kh spectral sequence)
  functoriality (cobordism → chain map) =  a 2-cell between residues (q=±1 up to sign)                  (view_factors_through_morphism / IsLensMorphism)
  the knot itself              =  Residue(diagram → isotopy class) — the AMBIENT QUOTIENT             (knots.md's BREAK: Reidemeister/colimit, NOT a self-application residue)
```

Set against the notes it consolidates, the rows fall into two clean groups. **Everything from "cube of
resolutions" through "functoriality" FITS** — the cube is the `{0,1}^n` bit-cube the calculus already
folds (`BoolXORFold`), the Khovanov complex/δ/`ker δ/im δ`/δ²=0 is `homological_algebra.md`'s residue
machine verbatim (one `delta`, one `dsq_zero`, one bigrading), and the categorification identity
(Euler char = Jones) is the corpus's `decategorify = q=±1 alternating count` pattern, the *same*
alternating sum as `simplex_face_euler_zero`. **The break is inherited, not new**: it sits in the last
row — the *knot itself* (the isotopy/colimit quotient `knots.md` located) — and in the *named field
objects* (the Frobenius algebra, the `KhovanovComplex`, `Cob`), which are absent exactly as in
`homological_algebra.md` (the `Ext`/`Tor`/resolution objects are absent there too).

## VALIDATE — does Khovanov homology categorify the Jones polynomial as the calculus's residue operation?

**Verdict: PREDICTION + PARTIAL (EXTEND by consolidation) — the deepest single confirmation that the
calculus's "decategorify = take the q=±1 alternating Euler count" pattern is REAL on a famous instance,
with the same two inherited absences `knots.md`/`homological_algebra.md` recorded.** Khovanov homology
does not add an axis; it is `homological_algebra.md`'s residue-taking operation run on `knots.md`'s
resolution cube, with the Jones polynomial as the Euler characteristic. The structural skeleton + every
load-bearing leg (bit-cube, residue mechanism, alternating Euler count, q=±1 tag) is ∅-axiom PURE; the
*named Khovanov/Jones/Kauffman/Frobenius/cobordism objects* are ABSENT — the precise missing leg,
located like `knots.md`/`homological_algebra.md`. Leg by leg, honest.

**(1) ★ The cube of resolutions = the `{0,1}^n` bit-cube = `BoolXORFold`'s hypercube (game_theory's
cube), PURE.** Each crossing resolves to one bit; the set of resolutions is `{0,1}^crossings`, the
exact 𝔽₂-hypercube `game_theory.md` decomposed. The repo folds over this cube PURE:
`BoolXORFold.psiNatPos` (the XOR-fold over a `Nat → Bool` family = a cube vertex's bits) and
`psiNatPos_linear` (the fold distributes over pointwise XOR, `BoolXORFold.lean:38`, 6/0 PURE) — the
cube's 𝔽₂-linear structure. The same hypercube `game_theory.md` used for nim-sum and `knots.md`'s
Kauffman state sum runs over. This is the construction `C`, grounded.

**(2) ★ The Khovanov chain complex / δ / `ker δ/im δ` / δ²=0 = `homological_algebra.md`'s residue
machine, VERBATIM, PURE.** The Khovanov differential is `homology.md`'s `∂`: a map raising the
homological degree by one (one cube-edge / one `0→1` smoothing flip), with a q=±1 sign per edge so the
cube's square faces anticommute. The defining law δ²=0 (what makes the cube a *complex*) IS
`dsq_zero_universal_delta4` (`V4Capstone.lean:41`, **PURE, scanned 5/0**: `∀σ ∀i, δ(δσ) i = false`) —
the orientation bits cancelling pairwise, the q=±1 direction-bit at a two-step composite, exactly the
edge-sign anticommutation Khovanov's δ needs. The coboundary op is `delta` (`Delta/Core.lean:54`), one
op shared with homology/de Rham/sheaf/Khovanov. `Kh^{i,j} = ker δ/im δ` is then
`reduced_betti_d4_contractible`'s residue (`BettiKernel.lean:63`, **PURE, scanned 11/0**: on the
contractible/exact piece `ker δ = im δ`, residue empty = the q=+1 part) versus
`NonzeroBetti.nonzero_cohomology_class` (`NonzeroBetti.lean:143`, **PURE, scanned 56/0**: a witnessed
element of `ker δ/im δ`, `betti_one_cycle` `b₁=1`, `loopClass_not_coboundary` = closed-not-exact = the
q=−1 obstruction). So a nonzero Khovanov class is the **same** q=−1 residue these built witnesses
exhibit; a contractible cube direction is the q=+1 exact part — one `delta`, one `dsq_zero`, one
bigrading. (The cup-product companion `leibniz_universal_delta4`, `V4Capstone.lean:62`, PURE, is the
graded-relation slot — the same shape as the skein relation `knots.md` Gap 1 located; the Khovanov
differential's merge/split maps are the categorified skein.)

**(3) ★ The categorification identity (graded Euler char = Jones) = the q=±1 alternating count — the
`decategorify` pattern, PURE.** `Σ_{i,j}(−1)ⁱ qʲ dim Kh^{i,j} = V_L(q)`. The alternating sign `(−1)ⁱ`
down the homological height is the corpus's q=±1 alternating Euler sum: `simplex_face_euler_zero`
(`FaceTerms.lean:125`, **PURE, scanned 10/0**: `Σ_k(−1)ᵏ binom d k = 0`, the Euler/`∂²=0`
cancellation), the same `Σ(−1)ⁱ` as index_theory's McKean–Singer and Lefschetz `L(id)=χ`
(`lefschetz_degree.md`). This is the load-bearing new datum: **categorification ⟷ decategorification is
the calculus's residue ⟷ its q=±1 alternating count**, and Khovanov is the cleanest named instance —
the Jones polynomial is literally `Σ(−1)ⁱ` of the residue's bigraded ranks. The q=±1 tag
(`ResidueTag.lean`, **PURE, scanned 55/0**: `escape_residue_outside` q=−1 → `object1_not_surjective`,
`converge_residue_fixed` q=+1, `residue_tag_two_poles`, `golden_is_converge`) is what grades each
Kh^{i,j} as it is alternately counted. So "take the Euler characteristic to decategorify" is the
calculus's "read the q=±1 alternating count of the residue" — Khovanov is the lift, Jones the count.

**(4) Lee deformation / s-invariant = the resolution/deformation dial on the residue; the Lee→Kh
spectral sequence = the residue operation iterated.** Lee theory deforms δ (a one-parameter dial); the
s-invariant is the surviving filtration height — a fold-height readout of the deformed residue. This is
the README's resolution/deformation dial (`continuity.md`/`derivative.md`) applied to the
chain-complex, and the Lee→Khovanov spectral sequence is `spectral_sequences.md`'s residue operation
*re-entering as its own operand* (the s-invariant living on a convergence page, the q=+1 fixed point of
the iteration). Grounded at the dial / spectral-iteration level (`ResolutionShift.IsResolutionShift`,
the residue-reentry machinery cited in `spectral_sequences.md`); the named `LeeComplex`/`s` object is
absent.

**(5) Functoriality (cobordism → chain map) = the 2-cell between residues.** A cobordism inducing a map
`Kh(L₀)→Kh(L₁)` is a morphism between two residues = the 2-category-of-readings naturality 2-cell
(`view_factors_through_morphism`, `IsLensMorphism`, `two_cells.md`); functoriality-up-to-sign is the
q=±1 direction bit on the 2-cell. The *ambient cobordism category `Cob`* itself sits at the
isotopy/colimit break (leg 6). Grounded at the 2-cell level; the named `Cob`/functoriality object is
absent.

**(6) The inherited BREAK — the knot itself (isotopy/colimit quotient) and the named field objects.**
Two absences, both inherited, neither new:
- **The isotopy quotient** — invariance of `Kh(L)` under Reidemeister moves is `knots.md`'s Gap 2
  *verbatim*: the knot is the residue of the diagram→isotopy-class reading, a **topological/ambient
  quotient** that is **not** a self-application residue (no q=±1 diagonal generates it). It sits at the
  un-built colimit/q=−1 corner + an absent ambient-space construction (`SYNTHESIS.md §5` item 1, the
  "one genuine structural break" recurring down the six-field chain). The *cube*, *complex*, *residue*,
  and *Euler-char-=-Jones* are all built/grounded; the **invariance under Reidemeister is the open leg**
  (a theorem-grade obstruction, the same one `knots.md`/`fundamental_group.md` hit). NOTE the Side-A
  refinement: the Kauffman-bracket *state sum* is a terminating crossing-resolution fold (the
  confluent+terminating q+1 corner `SYNTHESIS.md §5` says is BUILT via `FreeReduction`/normal-form) —
  so the *bracket itself* sits in the buildable corner; only the *isotopy invariance of the resulting
  homology* is Side B.
- **The named objects** — grep over `lean/E213` for `Khovanov`/`Jones`/`Kauffman`/`skein`/
  `Reidemeister`/`categorif` returns **zero Lean declarations** (only false positives matching
  "invariant"/"invariants" — see anchors). There is no `KhovanovComplex`, no Frobenius algebra
  `A=ℤ[X]/X²`, no `JonesPolynomial`, no `Cob`/cobordism category, no `s`-invariant object. This is the
  **same shape** as `homological_algebra.md`'s absent `Ext`/`Tor`/resolution objects: the residue
  mechanism (`ker δ/im δ`, `delta`, `dsq_zero`), the grading (`ResidueTag`, the two fold-heights), the
  exact/q=+1 part (`reduced_betti_d4_contractible`), the q=−1 obstruction (`NonzeroBetti`), the bit-cube
  (`BoolXORFold`), and the alternating Euler count (`simplex_face_euler_zero`) are each built and PURE;
  the **named Khovanov object that would weld them into a bigraded `Kh^{i,j}`** is the open leg.

So: **PREDICTION on the consolidation (Khovanov homology = the calculus's residue-taking operation on
knots' resolution cube; the cube = the `{0,1}^n` bit-cube; the complex/δ/δ²=0 = the residue machine;
the graded Euler char = the Jones polynomial = the q=±1 alternating count; Lee/s = the deformation
dial / spectral-iteration; functoriality = the 2-cell), cashed at the bit-cube / residue-mechanism /
alternating-Euler-count / q=±1-tag level; PARTIAL because the named Khovanov/Jones/Kauffman/Frobenius/
cobordism objects and the Reidemeister-invariance leg are absent — the inherited knots.md/
homological_algebra.md gaps, not hand-waves.**

## Revelation (collapse + forcing + the q=±1 spine)

**★ Collapse — categorification IS the calculus's residue-taking, and decategorification IS its q=±1
alternating count; Khovanov homology and the Jones polynomial are the residue and its Euler
characteristic of ONE cube.** `knots.md` decomposed the Jones polynomial as a *count* — the Kauffman
state sum over the `{0,1}^n` resolution cube (each vertex read to a `±q`-power, summed with signs).
This note's datum: **lift that count back up to the residue it counts.** Assign a graded vector space
per cube vertex and a q=±1-signed differential along the cube edges (δ²=0 forced by the square-face
anticommutation, `dsq_zero_universal_delta4`); the homology `Kh^{i,j} = ker δ/im δ`
(`homological_algebra.md`'s residue machine, now bigraded) is the categorified invariant, and its
**graded Euler characteristic `Σ(−1)ⁱ qʲ dim Kh^{i,j}` = the Jones polynomial** — the *same* q=±1
alternating sum as `simplex_face_euler_zero` / McKean–Singer / `L(id)=χ`. So:

- **`decategorify = take the q=±1 alternating Euler count`** is not a metaphor — it is the calculus's
  `Residue(L,C)` followed by its `ResidueTag`'s ±1 alternating sum, and Khovanov/Jones is the famous
  named instance: the Jones polynomial is the Euler characteristic of the Khovanov residue, just as the
  Euler characteristic of a complex is `Σ(−1)ⁱ` of its homology ranks. **Categorification = lift the
  count to the residue; decategorification = read the residue's q=±1 alternating count back down.** One
  cube, two readings: down to the count (knots.md's Jones), up to the residue (this note's Kh).

- **The forcing.** δ²=0 is *forced* by the q=±1 direction bit (the square faces of the
  `{0,1}^n` cube must anticommute, opposite-order smoothing-flips carry opposite signs that cancel —
  `dsq_zero_universal_delta4`), exactly as `homology.md`'s `∂²=0` is forced. The bigrading is *forced*
  by `C`'s two fold-height axes (homological = Hamming weight up the cube, quantum = circle count); the
  Euler characteristic recovering Jones is *forced* because the per-vertex graded dimension, alternately
  summed down the height, telescopes to the state-sum count (the categorification theorem = the
  alternating-count identity `simplex_face_euler_zero`'s shape).

- **The q=±1 spine.** A contractible cube direction = `ker δ = im δ`, residue empty = the q=+1 exact
  pole (`reduced_betti_d4_contractible`, `converge`); a nonzero Khovanov class = closed-not-exact = the
  q=−1 obstruction (`NonzeroBetti.nonzero_cohomology_class`, `escape`). Khovanov homology *detects more
  than Jones* (e.g. it distinguishes knots Jones cannot, and the s-invariant bounds the slice genus)
  precisely because the residue carries the q=−1 obstruction the alternating count *cancels away* —
  the categorified residue sees what the decategorified count erases, the same way `H^{>0}` sees what
  the Euler characteristic's cancellation hides.

This passes the re-skin guard: it does not re-describe Khovanov homology — it **identifies it with the
calculus's residue-taking operation applied to knots' resolution cube**, grounded by the *same* PURE
`ker δ/im δ` mechanism (`reduced_betti_d4_contractible`, `delta`, `dsq_zero_universal_delta4`,
`NonzeroBetti`), the *same* `{0,1}^n` bit-cube (`BoolXORFold`), the *same* q=±1 alternating Euler count
(`simplex_face_euler_zero`), and the *same* q=±1 tag (`ResidueTag`) that already certify homology, de
Rham, sheaf, and game theory. The new datum is the **categorify/decategorify = residue/Euler-count**
identity on a famous named instance, with the Jones polynomial as the Euler characteristic — and the
honest inherited break (the isotopy quotient + the named objects) located precisely.

**EXTEND by consolidation; no new axis; interior model v7.1 holds.** Khovanov homology is the calculus's
residue operation run on `knots.md`'s cube; the Jones polynomial is its q=±1 alternating Euler count;
the break is `knots.md`'s isotopy/colimit quotient (Side B) plus the named-object absence
(`homological_algebra.md`'s shape), not a fresh gap.

## Note for the technique

**No new primitive; the cleanest named instance yet of `decategorify = q=±1 alternating Euler count`.**
The lesson for the model: the README's residue-first normal form `⟨C|L⟩ ⊕ Residue(L,C)` has a
*counting shadow* — every residue has a q=±1 alternating count (its Euler characteristic), and
**categorification is the act of recovering the residue from the count, decategorification the act of
taking the count from the residue.** `knots.md` lived on the count side (the Jones state sum);
Khovanov homology is the residue side of the *same* cube; the two are bound by the Euler-characteristic
identity, which is the calculus's q=±1 alternating sum (`simplex_face_euler_zero`/McKean–Singer). This
sharpens `homological_algebra.md`'s "the field names the residue operation": Khovanov homology shows the
residue operation's *Euler-count inverse* is a named field move (categorification), and that the
resulting residue strictly dominates the count (it detects what the alternating cancellation erases =
the q=−1 obstruction). The one genuine absence — the named Khovanov/Jones/Kauffman/Frobenius/cobordism
object, and Reidemeister-invariance — is located precisely: the *cube* (BoolXORFold), the *residue
mechanism* (delta/dsq_zero/ker δ/im δ), the *q=±1 grading* (ResidueTag), the *exact/q=+1 part*
(reduced_betti_d4_contractible), the *q=−1 obstruction witness* (NonzeroBetti), and the *alternating
Euler count* (simplex_face_euler_zero) are present and PURE; the named bigraded `Kh^{i,j}` and the
isotopy-invariance theorem (`knots.md` Side B) are the open legs.

---

## Verified Lean anchors (file:line:theorem — all grep/Read-verified on `lean/E213`; purity scanned via `tools/scan_axioms.py` from repo root this session)

| Leg | Theorem / structure (file:line : name) | Scan |
|---|---|---|
| **★ cube of resolutions = `{0,1}^n` bit-cube = game_theory's hypercube** | `Lib/Math/Cohomology/Infrastructure/BoolXORFold.lean:32 psiNatPos`, `:38 psiNatPos_linear` (fold distributes over pointwise XOR — the cube's 𝔽₂-linear structure) | **6/0 PURE** ✓ |
| **★ Khovanov complex / δ / δ²=0 = the residue machine (q=±1 sign-propagation)** | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 dsq_zero_universal_delta4` (δ²=0, scanned PURE), `:62 leibniz_universal_delta4` (graded-relation/skein slot); `Lib/Math/Cohomology/Delta/Core.lean:54 delta`, `:42 deltaAt` | **5/0 PURE** ✓ |
| **★ `Kh^{i,j}=ker δ/im δ` — q=+1 exact part (contractible cube direction)** | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 reduced_betti_d4_contractible`, `:42 kerSizeDelta`, `:47 kerSize_5_0`, `:52 kerSize_5_1` | **11/0 PURE** ✓ |
| **★ nonzero Kh class — q=−1 obstruction residue (the categorified-detects-more witness)** | `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:111 betti_one_cycle`, `:134 loopClass_not_coboundary`, `:143 nonzero_cohomology_class`, `:173 cycle_vs_contractible_qpm` | **56/0 PURE** ✓ |
| **★ graded Euler char = Jones = the q=±1 alternating count (decategorify pattern)** | `Lib/Physics/Simplex/FaceTerms.lean:125 simplex_face_euler_zero` (`Σ_k(−1)ᵏ binom d k = 0`, the Euler/`∂²=0` alternating cancellation = McKean–Singer's `Σ(−1)ⁱ`) | **10/0 PURE** ✓ |
| **q=±1 tag grading each Kh^{i,j}** | `Lib/Math/Foundations/ResidueTag.lean:73 ResidueTag`, `:86 multiplier_unimodular`, `:133 escape_residue_outside` (q=−1), `:160 converge_residue_fixed` (q=+1), `:180 golden_is_converge`, `:228 residue_tag_two_poles` | **55/0 PURE** ✓ |
| Lee/s = resolution/deformation dial; Lee→Kh spectral seq = residue iterated | `Lib/Math/Analysis/ResolutionShift.lean:73 IsResolutionShift` (graded refinement, additive grades; `IsResolutionShift_compose`) | ∅-axiom ✓ (`spectral_sequences.md`/`homological_algebra.md`) |
| functoriality (cobordism → chain map) = the 2-cell between residues | `Lens/Foundations/SemanticAtom.lean:412 raw_initial`, `:108 universalMorphism`; `Lens/Foundations/UniversalDistinguishing.lean:103 dhom_unique_pointwise`; `view_factors_through_morphism`/`IsLensMorphism` (`two_cells.md`) | ∅-axiom ✓ (cited prior) |
| escape / faithful residue (the isotopy/colimit break's q=−1 pole) | `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective`, `:47 object1_injective` | ∅-axiom PURE ✓ |
| cross-frame — the cube's character (knots' Kauffman / game's nim-sum) & writhe sign-count | `Lib/Math/NumberTheory/ModArith/Zolotarev.lean:133 psign_mulPerm_hom` (the q=±1 sign character = the writhe's signed crossing count, knots.md), `:106 mulPerm_comp`; `Lib/Physics/Symmetry/AutKGroup.lean:82 C2_6.mul` (the 𝔽₂-cube group) | ∅-axiom ✓ (`knots.md`/`game_theory.md`) |
| cross-frame notes | `knots.md` (Jones = Kauffman state sum over the cube; the located break), `homological_algebra.md` (the residue operation = `ker δ/im δ`, graded, tagged q=±1; the absent-object shape), `game_theory.md` (the `{0,1}^n` bit-cube = `BoolXORFold`), `spectral_sequences.md` (Lee→Kh = residue iterated), `derived_categories.md`/`two_cells.md` (categorification / the 2-cell) | prior, ∅-axiom ✓ |

**Fresh purity scans (this session, `tools/scan_axioms.py <module>` from repo root):**
`E213.Lib.Math.Cohomology.Delta.V4Capstone` **5/0** (incl. `dsq_zero_universal_delta4`,
`leibniz_universal_delta4`); `E213.Lib.Math.Cohomology.Examples.BettiKernel` **11/0**
(`reduced_betti_d4_contractible`, `kerSizeDelta`); `E213.Lib.Math.Cohomology.Examples.NonzeroBetti`
**56/0** (`nonzero_cohomology_class`, `betti_one_cycle`, `loopClass_not_coboundary`,
`cycle_vs_contractible_qpm`); `E213.Lib.Math.Cohomology.Infrastructure.BoolXORFold` **6/0**
(`psiNatPos`, `psiNatPos_linear`); `E213.Lib.Math.Foundations.ResidueTag` **55/0**
(`residue_tag_two_poles`, `escape_residue_outside`, `converge_residue_fixed`, `golden_is_converge`,
`multiplier_unimodular`); `E213.Lib.Physics.Simplex.FaceTerms` **10/0** (`simplex_face_euler_zero`).
`lake build` of the cohomology targets completed successfully. The purity claims rest on the fresh
scans, not docstrings.

## Dropped / flagged (could not verify or predicted-not-built)

- **`Khovanov` / `Jones` / `Kauffman` / `skein` / `Reidemeister` / `categorif` OBJECTS — ABSENT,
  grep-confirmed.** Grep over `lean/E213` (case-insensitive) for
  `Khovanov|categorif|Jones|Kauffman|cube_of_resolutions|s_invariant|skein|Reidemeister` returns
  **zero Lean declarations** — the only 4 file hits (`CoResidue.lean`, `MonovariantFlow.lean`,
  `Mobius213CDBridge.lean`, `Cantor.lean`) are **false positives** matching the substring
  "invariant"/"invariants" (e.g. `cantor_as_invariant`, `reaches_invariant`,
  `type_C_asymptote_eq_mobius_invariants`), none knot-theoretic. No `KhovanovComplex`, no Frobenius
  algebra `ℤ[X]/X²`, no `JonesPolynomial`, no `Cob`/cobordism category, no `s`-invariant. The named
  field object is the predicted-not-built leg — **identical to the ceiling `knots.md` (no knot/braid
  object) and `homological_algebra.md` (no `Ext`/`Tor`/resolution object) hit.**
- **Reidemeister-invariance of `Kh(L)` — ABSENT (Side B of the knots.md break).** The isotopy/colimit
  quotient (invariance under the topological moves) is `knots.md`'s Gap 2 / `SYNTHESIS.md §5` item 1 —
  a theorem-grade obstruction at the un-built colimit/q=−1 corner + an absent ambient-space
  construction, recurring verbatim. The Kauffman-bracket *state sum* (the terminating
  crossing-resolution fold) sits in the buildable Side-A corner (`FreeReduction`/normal-form); only the
  *homology's invariance* is Side B. Flagged as the located structural break, not a gap to close here.
- **Lee/s-invariant and functoriality OBJECTS — ABSENT.** Grounded at the dial / spectral-iteration /
  2-cell level (`IsResolutionShift`, `spectral_sequences.md`'s residue-reentry, `view_factors_through_morphism`);
  no named `LeeComplex`/`s`/`Cob`-functor object. Flagged predicted-not-built; the *mechanism* (residue
  deformation, the 2-cell) is PURE-built, the *named object* is open.
- **Verified buildable witness (the q=−1 obstruction the categorified residue carries).** The
  "categorification detects more than the count" phenomenon already has a concrete ∅-axiom witness:
  `NonzeroBetti.lean` (56/0) — a nonzero `H¹` (`nonzero_cohomology_class`, `betti_one_cycle` `b₁=1`)
  with `cycle_vs_contractible_qpm` tagging cycle = q−1 `escape` vs contractible = q+1 `converge` via
  `ResidueTag`. This is the explicit complement of the exact case (`reduced_betti_d4_contractible`) and
  is the calculus's standing model of "a residue class the alternating Euler count cancels but the
  homology retains" — the Khovanov-over-Jones detection phenomenon at the `ker δ/im δ` level. The
  remaining open weld is only the *bigraded* `Kh^{i,j}` on a *cube-of-resolutions* `C` (BoolXORFold)
  with the Euler-char-=-Jones identity stated as one theorem — each leg PURE, the named welding object
  absent.
