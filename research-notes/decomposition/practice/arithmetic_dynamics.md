# Decomposition: arithmetic dynamics (iteration of a map on ℙ¹ over a number field, (pre)periodic points, the canonical/Néron–Tate height ĥ, Northcott finiteness, dynatomic polynomials)

*213-decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`).*
*The iteration-axis entry meeting `golden_ratio.md` (the self-applying iterator `T`, the q=+1
fixed point), `continued_fractions.md` (the periodic/aperiodic = q=±1 dichotomy,
`golden_aperiodic` vs `finite_order_divides_twelve`), `ergodic_theory.md` (the orbit / iteration),
`dimension.md` (the height = a size reading of the fold-height), and `padic.md`/`modular_forms.md`
(the Stern–Brocot/Markov height-cocycle `minkowski_is_markov_valued_cocycle`).*
*The NEW datum: the canonical height ĥ is the q=±1 preperiodic-detector made a **size reading** —
ĥ=0 ⟺ q=+1 finite orbit ⟺ preperiodic; ĥ>0 ⟺ q=−1 height-escape — and the functional equation
ĥ(fⁿ(P)) = (deg f)ⁿ·ĥ(P) is literally `CassiniUnimodular.det_closed`'s `det s n = qⁿ·det s 0`.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **self-applying distinguishing iteration**, the SAME `C` as
  `golden_ratio.md` and `ergodic_theory.md`. A point `P` on a number-pair carrier, and a map `f`
  whose next operand is its own output: the orbit `P, f(P), f²(P), …` is the count iterating the
  step (`Meta/OrbitIsIter.lean:42` `orbit_eq_iter`: an orbit *is* `iter`). The rational/polynomial
  map `f` is the Möbius/recurrence iterator already in the repo (`MobiusSelfForm.mobius_iteration_master`,
  the iterator `T(p,q)` written in pure integer arithmetic; `seed/AXIOM/05_no_exterior.md` §5.6,
  the iterator read straight off the residue's self-pointing). The partial-quotient / orbit history
  is the construction-history; each application of `f` is one re-entry of the fold. So a "dynamical
  system on ℙ¹" is the `golden_ratio.md` construction with the all-1s recurrence relaxed to an
  arbitrary `f`.

- **Reading `L_height` at residue resolution** — the **canonical/Néron–Tate height ĥ as a size
  reading of the fold-height**. `dimension.md` established that fold-height reads out as
  dimension/degree/pole-order/nesting (the well-founded measure already in `C`). The canonical
  height ĥ is exactly this measure adapted to the iteration: a size assigned to each orbit point,
  read at residue resolution (the limit ĥ = limₙ (1/deg fⁿ)·h(fⁿ P) is the `derivative.md` modulus
  dial — the naive height `h` averaged down the orbit, the limit never the operand). The corpus's
  built height-cocycle is the Stern–Brocot/Markov height `minkowski_is_markov_valued_cocycle`
  (the residue→number defect valued in `SL₂(ℤ)`, the Eichler–Shimura cocycle on the tree), and the
  height-tower `HeightTowerResidue.height_tower_residue` (the fold-height as a tower with no top).

- **Residue, tagged `q = ±1`** — the **preperiodic/escape dichotomy of the orbit**, read out by ĥ:
  - **q = +1 (converge / finite orbit / preperiodic / ĥ = 0).** When the orbit closes — `f`
    eventually periodic on `P` — the height the iteration cannot grow: ĥ(P) = 0. This is the SAME
    finite-order/periodic pole as `continued_fractions.md`'s `finite_order_divides_twelve` (disc<0
    ⟹ periodic floor) and `golden_ratio.md`'s conserved Cassini `q=+1`. The height is *bounded by
    the iteration* — the conserved multiplier `qⁿ = 1` (`CassiniUnimodular.qpow_one`).
  - **q = −1 (escape / infinite orbit / ĥ > 0).** When the orbit never closes, the height grows
    without bound under iteration: ĥ(P) > 0, the q=−1 escape. The SAME aperiodic pole as
    `golden_aperiodic` (disc>0 ⟹ the boost has infinite order, never returns) and
    `height_diagonal_escapes` (the height-tower diagonal escapes every stage). The reached-by-none
    surplus of the height-reading's self-application (`object1_not_surjective`).

  **The functional equation IS `det_closed`.** Silverman's defining property
  ĥ(f(P)) = (deg f)·ĥ(P), iterated to ĥ(fⁿ(P)) = (deg f)ⁿ·ĥ(P), is *structurally identical* to
  `CassiniUnimodular.det_closed`: `det s n = qpow q n · det s 0` — the orbit-invariant at layer `n`
  is the initial value scaled by the `n`-th power of the multiplier. The canonical height is the
  Cassini determinant of the orbit with `deg f` in the multiplier role; ĥ=0 ⟺ the scaled quantity
  stays 0 ⟺ the q=+1 conserved/finite pole.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   "P on a number-pair"     =  ⟨ directed count-pair | — ⟩                  (C, before any reading)
   map f, orbit fⁿ(P)       =  ⟨ self-applying iterator | iter ⟩            (= golden_ratio's T)   orbit_eq_iter
   canonical height ĥ(P)    =  ⟨ orbit | L_height ⟩ at residue res.         a SIZE reading (dimension.md)
   "ĥ(fⁿP) = (deg f)ⁿ·ĥ(P)" =  det s n = qⁿ·det s 0                          CassiniUnimodular.det_closed
   ĥ(P)=0 ⟺ P PREPERIODIC   =  q=+1 finite orbit (height the iteration can't grow)  qpow_one / finite_order_divides_twelve
   ĥ(P)>0  (infinite orbit) =  q=−1 height-escape (grows without bound)     golden_aperiodic / height_diagonal_escapes
   NORTHCOTT (bounded ⟹ finite) =  q=+1 finiteness/compactness corner       heineBorel / gridMax_attained
   dynatomic Φ_n (period-n pts) =  the count reading per period             finite-order spectrum count
   Julia/Mandelbrot dichotomy   =  the q=±1 escape vs bounded-orbit split   cassini_law_one_at_two_multipliers
   the q=±1 tag                  =  multiplier ∓1                            ResidueTag.multiplier_unimodular
```

The single move: arithmetic dynamics is **not** a new field — it is the **iteration axis**
(`golden_ratio.md`/`ergodic_theory.md`) with the **canonical height = the q=±1 fixed-point detector
made a size reading** (ĥ=0 ⟺ q=+1 preperiodic; ĥ>0 ⟺ q=−1 escape), plus the **q=+1 bounded⟹finite
compactness corner** for Northcott. No new primitive.

## Revelation (collapse + forcing + the q=±1 spine)

**Collapse 1 — the iteration of `f` IS golden_ratio's φ-iteration / ergodic's orbit.** `f` re-fed
its own output is `orbit_eq_iter` (an orbit = the count iterating the step), the SAME `C` as
`golden_ratio.md`'s `T(p,q)=(2p+q,p+q)` (`mobius_iteration_master`) and `ergodic_theory.md`'s `Tⁿ`.
φ = [1;1,1,…] is the all-1s instance; a general `f` is the same self-applying distinguishing with an
arbitrary recurrence. "Arithmetic dynamics" and "the golden ratio's iteration" collapse to one `C`.

**Collapse 2 — ĥ(P)=0 ⟺ preperiodic IS the q=±1 fixed-point/finite-order detector, read as size.**
This is the load-bearing NEW datum. The canonical-height theorem ĥ(P)=0 ⟺ P preperiodic is
*exactly* `continued_fractions.md`'s periodicity dichotomy and `golden_ratio.md`'s conserved-vs-
alternating Cassini multiplier, with the multiplier read as a **height**:
- q=+1 (finite orbit, preperiodic): the height is conserved/bounded — `qpow_one`
  (`qpow 1 n = 1`, the multiplier stays the unit at every layer), the SAME finite-order pole as
  `finite_order_divides_twelve`/`no_order_five` (disc<0 ⟹ periodic floor).
- q=−1 (infinite orbit, ĥ>0): the height escapes — `golden_aperiodic` (the disc>0 boost has
  infinite order, `pow G (n+1) ≠ I` for all `n`), `height_diagonal_escapes` (the height-tower
  diagonal lies outside every stage). The reached-by-none surplus, `object1_not_surjective`.
The functional equation ĥ(fⁿP)=(deg f)ⁿ·ĥ(P) is `det_closed`'s `det s n = qⁿ·det s 0` with `deg f`
in the multiplier slot — the canonical height IS the Cassini orbit-determinant read as a size, and
ĥ=0 is the q=+1 corner where the scaled quantity can never leave 0. This is the calculus's deepest
collapse (`ResidueTag.residue_tag_two_poles`, 55/0) made concrete on a *height*: the limitative
escape and the converging fixed point are one residue at its two signs, and ĥ is that sign read off
as magnitude.

**Forcing — Northcott finiteness is the q=+1 bounded⟹finite compactness corner, not a separate
theorem.** Northcott's "finitely many points of bounded height and bounded degree" is *the same*
finiteness as `topology.md`/compactness: `heineBorel` (a cover of a dyadic bracket reduces to a
finite subcover) and `gridMax_attained` (the max is attained at every *finite* resolution, the
q=+1 corner; `Msup` the reached-by-none q=−1 limit). Bounded height = a bounded region of the
count-reading; the q=+1 finiteness collapse forces finitely many lattice points inside it — the
contrapositive of `cardinality.md`'s q=−1 escape diagonal. Northcott is *forced* by the same
finiteness corner already proved, not asserted. (The repo even names it: `Foundations/Positivity.lean:20`
"Mordell / Faltings — finiteness from a nonnegative *height* (Northcott)" — prose, not a Lean object.)

**The spine — one residue, two signs, read as a height.** Arithmetic dynamics is the q=±1 spine
(`SYNTHESIS.md` §3) made a size reading: the escape pole (Cantor/Gödel/measure/quintic, q=−1) =
ĥ>0 infinite orbit; the converge pole (φ/Gaussian/ODE/ergodic, q=+1) = ĥ=0 preperiodic. The
Julia/Mandelbrot bounded-vs-escaping dichotomy is `cassini_law_one_at_two_multipliers` (one
parametric law at two multipliers) read over the orbit's height. No new primitive: arithmetic
dynamics = (the iteration axis) + (ĥ = the q=±1 detector as a size reading) + (Northcott = the q=+1
bounded⟹finite corner). The dynatomic polynomials Φ_n (cutting out exact-period-n points) are the
**count reading per period** — the same per-period enumeration as the finite-order spectrum, with no
named `dynatomic` object in the repo.

## VALIDATE verdict — **PREDICTION** (the iteration axis + the height-as-q=±1-detector; the named dynamics objects predicted-not-built)

No new primitive, no break. Arithmetic dynamics slots entirely into model v7.1: `C` = the
self-applying iterator (= `golden_ratio.md`/`ergodic_theory.md`'s orbit), `L` = the canonical height
= a size reading (`dimension.md`) of the fold-height at residue resolution, `Residue` = the orbit's
(pre)periodic/escape dichotomy tagged `q=±1`. It is a PREDICTION (not pure collapse) because the
calculus *derives the field's shape* — ĥ=0 ⟺ preperiodic is *which* residue (the q=±1 detector),
*why* (conserved vs escaping multiplier), and *what fails* (Northcott = the q=+1 finiteness corner) —
from existing slots, exactly the `ergodic_theory.md`/`differential_equations.md` profile (engines and
consolidating ties built; the field-specific named objects absent).

**The honest line: every named arithmetic-dynamics object is ABSENT.** Grep-confirmed
(`canonical_height`/`canonicalHeight`/`preperiodic`/`Preperiodic`/`periodic_point`/`Northcott`/
`dynatomic`/`Julia`/`Mandelbrot` — **0 theorem hits in `lean/E213`**; only prose mentions of
"Northcott" in `Positivity.lean`/`ProofISALifts.lean` and "dynamics" as a filename word in
`ProbeTwistDynamics.lean`/`Real213/INDEX.md`). What is built is the **engine + the ties**: the
self-applying iterator (`orbit_eq_iter`, `mobius_iteration_master`), the q^n height-growth law
(`det_closed`), the conserved/escape multiplier poles (`qpow_one`/`golden_aperiodic`/
`finite_order_divides_twelve`), the height-cocycle (`minkowski_is_markov_valued_cocycle`,
`height_tower_residue`), the q=+1 finiteness corner for Northcott (`heineBorel`/`gridMax_attained`),
and the formal q=±1 tag (`ResidueTag`). The **welds** — a named canonical height ĥ with
ĥ(f(P))=(deg f)·ĥ(P), the equivalence ĥ(P)=0 ⟺ preperiodic, a Northcott finiteness theorem, the
dynatomic Φ_n object — are unbuilt.

## Verified Lean anchors (file:line:theorem — all grep-confirmed; scans `python3 tools/scan_axioms.py E213.<module>` from repo root, this session)

**The self-applying iterator = golden_ratio/ergodic's orbit (the iteration axis):**
- `lean/E213/Meta/OrbitIsIter.lean:42` `orbit_eq_iter` — an orbit IS `iter` (the count iterating the step).
- `lean/E213/Lib/Math/Algebra/Mobius213/Px/MobiusSelfForm.lean:119` `mobius_iteration_master`
  (the iterator `T` in pure integer arithmetic), `:263` `self_reconstruction_master`
  (the construction re-entering itself). **MobiusSelfForm 11/0 PURE.**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HyperbolicEllipticTrace.lean:71`
  `golden_hyperbolic` (`det G=1, tr G=3, disc G=5>0` — the φ-iterator's hyperbolic spectrum).

**★ The canonical-height functional equation ĥ(fⁿP)=(deg f)ⁿ·ĥ(P) = the q^n orbit-determinant law
— `CassiniUnimodular` (13/0 PURE):**
- `lean/E213/Lib/Math/Algebra/CassiniUnimodular.lean:142` `det_closed` — `det s n = qpow q n · det s 0`
  (the orbit-invariant at layer `n` = initial value scaled by `qⁿ`; `deg f` in the multiplier slot).
- `:123` `det_step` (`det s (n+1) = q · det s n`, one iteration), `:135` `qpow` (the `qⁿ` power).
- `:170` `qpow_one` (`qpow 1 n = 1`, q=+1 conserved = ĥ bounded = preperiodic).
- `:163` `cassini_law_one_at_two_multipliers` (one parametric law at two multipliers = Julia/Mandelbrot
  bounded-vs-escape), `:60` `det_golden`, `:68` `det_period2_alternates`.
- `:188` `multiplier_unit_magnitude_sign_order_NT` — the buildable witness (below).

**★ ĥ(P)=0 ⟺ preperiodic = the q=±1 finite-order/aperiodic detector:**
- q=+1 (preperiodic / finite orbit): `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/FiniteOrderSpectrum.lean:503`
  `finite_order_divides_twelve`, `:527` `no_order_five`, `:603` `crystallographic_spectrum`
  (disc<0 ⟹ periodic floor). **FiniteOrderSpectrum 29/0 PURE.**
- q=−1 (ĥ>0 / infinite orbit): `lean/E213/Lib/Math/NumberSystems/Real213/Phi/GoldenAperiodic.lean:57`
  `golden_aperiodic` (`pow G (n+1) ≠ I` ∀n — disc>0 boost has infinite order = escape). **GoldenAperiodic 3/0 PURE.**
- the height-escape: `lean/E213/Lib/Math/Analysis/Cauchy/DepthHeightDiagonal.lean:56`
  `height_diagonal_escapes` (the height-tower diagonal outside every stage). **DepthHeightDiagonal 43/0 PURE.**

**The height-cocycle / height-tower (the built height machine = the Stern–Brocot/Markov height):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Minkowski/MinkowskiCocycle.lean:46`
  `minkowski_is_markov_valued_cocycle` (the residue→number defect = `SL₂(ℤ)`-valued unimodular
  1-cocycle, the Eichler–Shimura/Markov height-cocycle). **MinkowskiCocycle 6/0 PURE.**
- `lean/E213/Lib/Math/NumberSystems/Real213/Completability/HeightTowerResidue.lean:52`
  `height_tower_residue`, `:42` `height_tower_no_top` (the fold-height as a tower with no top).
  **HeightTowerResidue 40/0 PURE.**

**★ Northcott (bounded height ⟹ finitely many points) = the q=+1 finiteness/compactness corner:**
- `lean/E213/Lib/Math/Geometry/Topology/Compactness.lean:42` `heineBorel` (cover of a dyadic bracket
  ⟹ finite subcover). **Compactness 7/0 PURE.**
- `lean/E213/Lib/Math/Analysis/ExtremeValue.lean:275` `ModContOnGrid.gridMax_attained` (max attained
  at every *finite* resolution, the q=+1 corner; `Msup` = the q=−1 reached-by-none limit).

**The formal q=±1 tag (Invariant B) + the residue (reached by none):**
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:86` `multiplier_unimodular`, `:228`
  `residue_tag_two_poles`, `:180` `golden_is_converge`, `:133` `escape_residue_outside`, `:160`
  `converge_residue_fixed`. **ResidueTag 55/0 PURE.**
- `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:61` `object1_not_surjective`, `:47`
  `object1_injective`, `:138` `distinguishing_always_leaves_residue` (faithful yet never total =
  the residue, ĥ>0's reached-by-none). **FlatOntologyClosure 7/0 PURE.**

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root, this session):**
CassiniUnimodular 13/0 · ResidueTag 55/0 · MobiusSelfForm 11/0 · MinkowskiCocycle 6/0 ·
GoldenAperiodic 3/0 · FiniteOrderSpectrum 29/0 · Compactness 7/0 · DepthHeightDiagonal 43/0 ·
HeightTowerResidue 40/0 · FlatOntologyClosure 7/0. All PURE, 0 DIRTY.

## Dropped / flagged

- **No `canonical_height` / `preperiodic` / `Northcott` / `dynatomic` / `Julia` / `Mandelbrot`
  object — predicted-not-built (grep-confirmed).** Zero theorem hits in `lean/E213` for any of these
  names; only prose: `Foundations/Positivity.lean:20` and `Foundations/ProofISALifts.lean:102`
  mention "Mordell heights (Northcott)" as positivity examples, and `ProbeTwistDynamics.lean` /
  `Real213/INDEX.md` use "dynamics" as a filename word. The field's named objects are absent; the
  calculus's engines and ties are present and PURE — the `ergodic_theory.md`/`differential_equations.md`
  profile (predicted structure is the deliverable; the named object is the open weld).
- **The canonical-height functional equation tie is structural, not a same-object identity.**
  `det_closed`'s `det s n = qⁿ·det s 0` has the *same shape* as ĥ(fⁿP)=(deg f)ⁿ·ĥ(P) (an orbit
  invariant scaling by the `n`-th power of a multiplier), and `det` here is a Cassini orbit-determinant,
  not a literal Néron–Tate height. The claim is "the height is this size-reading of the orbit
  multiplier", grounded by the shared `det_closed` law — not a built `canonicalHeight` welded to it.
- **The "Markov/Stern–Brocot height" is the built height-cocycle, but not named a `height`.**
  `minkowski_is_markov_valued_cocycle` is the Eichler–Shimura/Markov 1-cocycle (the height-cocycle
  the brief names); the repo's `height` files (`HeightTowerResidue`, `DepthHeightDiagonal`) are the
  fold-height tower, not a canonical-height-on-ℙ¹ object. Both cited as the height *machine*, with
  the canonical-height-on-an-orbit weld marked absent.
- **Buildable witness (verified PURE, in-repo): `CassiniUnimodular.multiplier_unit_magnitude_sign_order_NT`
  (`:188`)** — `(∀ n, qpow 1 n = 1) ∧ qpow (-1) NT = 1 ∧ qpow (-1) 1 ≠ 1 ∧ NT = 2`, proved
  `⟨qpow_one, by decide, by decide, rfl⟩`. This IS the preperiodic detector at the multiplier level:
  q=+1 ⟹ the orbit-height stays the unit at every layer (`qpow 1 n = 1`, bounded ⟹ preperiodic/ĥ=0),
  while q=−1 returns to the unit only after `NT=2` steps (`qpow (-1) NT = 1`, `qpow (-1) 1 ≠ 1`) — the
  alternating-overshoot escape. Confirmed PURE in the CassiniUnimodular 13/0 scan. No false witness is
  asserted; the named dynamics objects (ĥ, preperiodic, Northcott, Φ_n) are honestly marked absent.
