# Decomposition: quantum mechanics (the observable, measurement, the commutator, uncertainty, superposition, the Born rule, unitary evolution)

*213-decomposition per `../README.md` (model v7.1). A **fresh** field in the repo's PHYSICS deployment
direction, LEVERAGE phase — the bar is PREDICTION/REVELATION, consolidating `spectral.md` (the
`q=+1` real-spectrum reading) + `lie_theory.md` (the `q=−1` antisymmetry bracket) + `probability.md`
(the weight-reading) + `curvature.md` (det/holonomy = 1). This entry tests one thesis: **QM's operator
structure is the `q=±1` duality** — measurement reads the `q=+1` real eigenvalue (a fixed point); the
canonical commutator / uncertainty is the `q=−1` bracket-residue (the obstruction to a common fixed
point). The two are the two poles of one residue tag, the dual of each other.*

**PHYSICS-BRANCH CAVEAT (read first, per CLAUDE.md "DRLT-validation-as-the-goal").** This is a
**math-structure decomposition** of QM's *operator algebra*, NOT a physics validation claim. Nothing
here asserts a prediction of a measured constant, a falsifier, or that QM is "derived from the
residue". The deliverable is: *QM's Hermitian-observable / commutator / unitary skeleton is the same
`q=±1` operator structure the calculus already built for spectral theory and Lie theory* — a
consolidation, with the genuinely-physics objects (a Hilbert space, the Born rule, the measurement
collapse) honestly located as absent.

The hypotheses under test (from the task):
1. An **observable** = a **symmetric/Hermitian operator** = the `q=+1` real-spectrum reading
   (`spectral.md`/`Mat2SymmetricSpectrum.disc_symmetric_nonneg`). Measurement outcomes = the
   eigenvalues = the `q=+1` real scale-residues (a measurement reads off a fixed point).
2. The **canonical commutator `[X,P]=iℏ≠0`** = the `q=−1` antisymmetry residue
   (`lie_theory.md`/`Mat2Bracket`). The **uncertainty principle** = the bracket being the obstruction
   to a *common* eigenstate — the `q=−1` residue forbidding a shared `q=+1` fixed point.
3. **Superposition** = the linear reading; the **Born rule** `P=|⟨ψ|φ⟩|²` = the weight-reading
   (`probability.md`) squared (the `|·|²` = the `q=±1` pair-magnitude); **unitary evolution** =
   norm-preserving = the det/holonomy = 1 reading (`curvature.md`).
4. **Spectral decomposition / collapse** = the `q=+1` eigenprojector; **commuting observables =
   simultaneously diagonalizable** = sharing the `q=+1` eigenbasis.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the same `Mat2` ×-construction of `spectral.md`/`lie_theory.md`, nothing new.**
  A quantum observable, in the discrete `d=2` setting, is a `Mat2` (`HyperbolicEllipticTrace.Mat2`):
  the same directed-count bundle built by `mul`, carrying the orientation/swap bit (sign of `det`) and
  fold-height `2`. QM introduces **no new construction** — the observable, the propagator, and the
  commutator are all *readings* of this one `C`. (The repo's physics deployment confirms the atomic
  side independently: `Quantum.Qubit` identifies the qubit with the NT = 2 state-count, `qubit_state_count : NT = 2` —
  the state space is the temporal atom, not a new object.)

- **Reading — the `q=±1` operator pair.** QM is `C` read at **both poles of the residue tag at once**:
  - **`L_obs` (the observable / `q=+1` reading):** an observable is a **symmetric** operator
    (`IsSymmetric M := M.b = M.c`), read through its spectrum. By `disc_symmetric_nonneg` the
    discriminant `disc = (a−d)² + (2b)²` is a sum of squares, hence `≥ 0`: **the spectrum is REAL**
    — the elliptic `disc<0` (complex-eigenvalue) escape is *structurally unavailable* to a symmetric
    operator. So "observables have real spectra" is exactly the `q=+1` corner `spectral.md` built. A
    measurement outcome = an eigenvalue = a `q=+1` real scale-residue of the linear reading
    (`A·v=λ·v`: `v` fixed up to the multiplier `λ`).
  - **`L_[,]` (the commutator / `q=−1` reading):** non-commuting observables fold to the
    `lie_theory.md` bracket `[A,B] = AB − BA` (`Mat2Bracket.bracket`), antisymmetric by the `q=−1`
    pair-swap (`bracket_antisymm`). The canonical `[X,P] ≠ 0` is a nonzero bracket; uncertainty is the
    bracket *obstructing a common eigenstate* (below).
  - **`L_evol` (unitary evolution / norm-preserving = `q=+1` det1):** the propagator `e^{−iHt}` is the
    holonomy reading constrained to `det = 1` — `curvature.md`'s flat = `det_holonomy_eq_one`: every
    norm-preserving step composes to total det 1, the elliptic generators `S` (`S⁴=I`), `U` (`U⁶=I`)
    as the concrete finite unitaries.

- **Residue — the `q=±1` tag, read at *both* poles simultaneously — and that simultaneity IS QM.**
  Spectral theory read the `q=+1` pole (real eigenvalue, the fixed point); Lie theory read the `q=−1`
  pole (the antisymmetry bracket). QM is the field where **both are imposed on the *same* operator
  algebra at once**: the observables are `q=+1` (real spectra, measurement fixed points), their
  mutual structure is `q=−1` (the commutator), and the uncertainty principle is precisely the
  **clash** — the `q=−1` residue (`[X,P]≠0`) is the obstruction to two `q=+1` readings sharing a
  fixed point (a common eigenbasis). The residue that surfaces is not a *new* residue: it is the
  `ResidueTag` escape/converge pair, here forced to coexist on one `C`. The genuinely-physics residue
  (the amplitude `|·|²`, a Hilbert inner product, the collapse) sits at the same `Real213`/ℂ +
  uncountable-self-cover place `probability.md`/`spectral.md` already located as open.

## Re-seeing (⟨C | L⟩)

```
   an observable A        =  ⟨ Mat2 ×-construction | symmetric reading (b=c) ⟩       (IsSymmetric)
   "A has real spectrum"  =  disc = (a−d)²+(2b)² ≥ 0 — the q=+1 corner               (disc_symmetric_nonneg)
   measurement outcome    =  an eigenvalue λ = a q=+1 real scale-residue (A·v=λ·v)   (spectral.md, golden_hyperbolic)
   spectral decomposition =  the q=+1 fixed-point projection (the eigenprojector)    (eigenbasis; conceptual at d>1)
   [X,P] = iℏ ≠ 0         =  the q=−1 antisymmetry commutator-residue                (Mat2Bracket.bracket, bracket_antisymm)
   uncertainty principle  =  the q=−1 bracket forbids a common q=+1 fixed point      (no shared eigenbasis when [A,B]≠0)
   commuting observables  =  [A,B]=0 ⟺ simultaneously diagonalizable (shared q=+1 basis)
   [A,A]=0 (self-commute) =  every observable commutes with itself = its own eigenbasis  (bracket_self)
   tr[A,B]=0 (traceless)  =  the canonical commutator lands in sl — the iℏ·I trace-free residue  (tr_bracket_zero)
   superposition          =  the LINEAR reading (a state = a linear combination of eigenvectors)
   unitary evolution U    =  norm-preserving = det/holonomy = 1 (q=+1)               (det_holonomy_eq_one; S⁴=I, U⁶=I)
   the Born rule |⟨ψ|φ⟩|² =  the weight-reading SQUARED (the q=±1 pair-magnitude)    (probability weight; |·|² CONCEPTUAL)
```

Side by side, QM is **one operator-`C` read at the two `ResidueTag` poles**, the same picture
`spectral.md` (q=+1) and `lie_theory.md` (q=−1) each read at one pole:

| reading | what it does to the operator `C` | pole | built anchor |
|---|---|---|---|
| `L_obs` symmetric spectrum (`spectral.md`) | reads the real fixed-points (eigenvalues) | **q=+1** | `disc_symmetric_nonneg` |
| `L_[,]` commutator (`lie_theory.md`) | reads non-commutativity as a difference | **q=−1** | `bracket_antisymm` |
| `L_evol` holonomy det1 (`curvature.md`) | reads norm-preserving evolution | **q=+1** | `det_holonomy_eq_one` |
| `L_weight²` Born (`probability.md`) | reads amplitude→probability | (modulus) | weight built; `|·|²` conceptual |

**The leverage**: the measurement/uncertainty duality is the `q=±1` duality *made into a single
physical statement* — you cannot simultaneously diagonalize two operators whose bracket is the `q=−1`
residue. Measurement (q=+1, real eigenvalue, fixed point) and uncertainty (q=−1, bracket, no common
fixed point) are **the two poles of one residue tag**, the dual of each other.

## Revelation (collapse + forcing: QM's operator skeleton = the `q=±1` duality on one `C`)

**Forcing — "observables have real spectra" is the `q=+1` corner, not a QM axiom.** The classical
postulate "an observable is Hermitian, so its eigenvalues are real" is *not* an independent
assumption: it is `spectral.md`'s `q=+1` corner. `disc_symmetric_nonneg` (PURE) proves that a
symmetric `Mat2` has `disc = (a−d)²+(2b)² ≥ 0`, so the spectrum is real — the complex-eigenvalue
(elliptic, `q=−1`) escape is *structurally impossible* for a symmetric operator. The Hermitian
postulate **is** "stay at `q=+1`", exactly the corner discipline `measure.md`/`topology.md` named.
Measurement outcomes are the real eigenvalues = the `q=+1` scale-residues; the worked example is φ as
the dominant eigenvalue of `G` (`golden_hyperbolic`, PURE).

**Forcing — the canonical commutator `[X,P]≠0` is the `q=−1` antisymmetry residue, and traceless.**
`Mat2Bracket.bracket A B = AB − BA` (PURE) is the `q=−1` reading: antisymmetry `[A,B]=−[B,A]`
(`bracket_antisymm`) is the same pair-swap that signs `det`, `∂`, and ℤ's `−` — *forced, not posited*.
Two structural facts the canonical commutation relation exhibits fall straight out:
- `[A,A]=0` (`bracket_self`): every observable commutes with itself — it has its own eigenbasis (its
  own `q=+1` fixed-point family). The diagonal `q=−1`-vanishing.
- `tr[A,B]=0` (`tr_bracket_zero`): every commutator is **traceless** — it lands in `sl`. This is the
  algebra-side shadow of the canonical `[X,P]=iℏ·I`: the *physical* commutator is a pure `iℏ`-multiple
  of the identity (trace `2iℏ` for a genuine Heisenberg pair, which the finite `Mat2` cannot host —
  no `iℏ·I` is a commutator over a finite trace, see located break), but the *structural* fact
  certified here is that the commutator-residue is trace-free, the `q=−1` kernel of `tr`.

**Collapse — uncertainty = the `q=−1` bracket obstructing a `q=+1` common fixed point.** This is the
load-bearing collapse and the leverage. Two observables are *simultaneously measurable* iff they share
an eigenbasis iff they commute (`[A,B]=0`). The calculus reads this as: a **common `q=+1` fixed point**
(a shared eigenvector) exists iff the **`q=−1` residue vanishes**. The uncertainty principle is then
not a separate physical law — it is *the statement that the `q=−1` bracket-residue is the obstruction
to the two `q=+1` readings agreeing on a fixed point*. Measurement (the q=+1 fixed point) and
uncertainty (the q=−1 bracket) are the **two poles of one `ResidueTag`**, dual to each other: where the
bracket is zero the two real-spectrum readings co-diagonalize (a shared `q=+1` residue); where it is
nonzero they cannot (the `q=−1` residue is outside *every* common eigenbasis, the
`escape_residue_outside` shape one level up). **This is the consolidation**: QM's two defining
operator facts — real measurement outcomes and the uncertainty bound — are `spectral.md`'s `q=+1` and
`lie_theory.md`'s `q=−1` *read on the same operator algebra*, with uncertainty literally the
incompatibility of the two poles.

**Collapse — unitary evolution = the `q=+1` det/holonomy = 1 reading.** "Time evolution `U=e^{−iHt}`
is norm-preserving (unitary)" is `curvature.md`'s flat = `det_holonomy_eq_one` (PURE): every
norm-preserving step has `det=1`, and the lattice transport composes to total det 1 — a *flat*
(`q=+1`, conserved-character) evolution. The concrete finite unitaries are the elliptic generators
`S` (order 4, `S_elliptic_order4`) and `U` (order 6, `U_elliptic_order6`), each `det=1`, on the unit
circle — the rotation (norm-preserving) sector. Unitarity is the `q=+1` det1 corner; non-unitarity
(measurement collapse) would be its `q=−1` escape (see located break — collapse is not built).

**Superposition + the Born rule — the linear reading, and the weight-reading squared (honest).**
Superposition is the bare *linear* reading: a state is a linear combination of eigenvectors, the
`spectral.md` eigenbasis read additively. The Born rule `P=|⟨ψ|φ⟩|²` is `probability.md`'s
weight-reading (`P = ratio∘count`, the `ProbabilityCut` `num/den` clamp) with the amplitude's `|·|²`
in front — and the `|·|²` is the `q=±1` pair-magnitude (the count-Lens modulus of
`integers_as_difference_lens`, the squared-modulus of an amplitude pair). **Honest:** the *weight*
side is fully built (`ProbabilityCut`, `joint` = the `×↦·` independence character, `discreteNum` =
expectation); the *amplitude* side — a genuine complex inner product `⟨ψ|φ⟩` and its `|·|²` — is **not**
built as a Hilbert-space object. The closest built structure is the Cayley–Dickson norm
(`SignedCut/CD/CDNorm`, `CDConjugation`) — a level-indexed `normSq` with conjugation — but it is not
welded to the probability weight as an amplitude→probability map, and there is no inner-product space.
So the Born rule is the **predicted form** (weight² , the `q=±1` modulus of an amplitude), with the
amplitude object the named open leg.

## LEVERAGE — verdict

**PREDICTION (consolidation), with the measurement/uncertainty `q=±1` duality as the genuine
leverage, and three honest located breaks.** Comparable to `representation.md`/`lie_theory.md`: QM
introduces **no new construction** and consolidates four prior files under the two standing invariants,
with the genuinely-missing pieces (the Hilbert space, the amplitude `|·|²`, the measurement/collapse
object) located precisely, not hand-waved.

- **Leg 1 — observable = symmetric operator = the `q=+1` real-spectrum reading. PREDICTION, BUILT.**
  `disc_symmetric_nonneg` (PURE, `Mat2SymmetricSpectrum`) proves the symmetric discriminant is a sum
  of squares ⟹ real spectrum: the Hermitian postulate IS "stay at `q=+1`". Measurement outcome =
  eigenvalue = `q=+1` scale-residue (φ the worked example, `golden_hyperbolic`). The `d=2` symmetric
  spectral theorem is built; general `d>1` is the inherited open (below).

- **Leg 2 — `[X,P]≠0` / uncertainty = the `q=−1` bracket-residue. PREDICTION, bracket BUILT.**
  `Mat2Bracket` (10/0 PURE): `bracket`, `bracket_antisymm` (the `q=−1` pair-swap), `bracket_self`
  (`[A,A]=0`, self-commute = own eigenbasis), `tr_bracket_zero` (the canonical commutator is
  traceless / sl — the `iℏ·I` structure's trace-free shadow), `jacobi`, `bracket_leibniz`. The
  uncertainty principle = "the `q=−1` bracket obstructs a common `q=+1` fixed point (shared
  eigenbasis)" — the duality of Leg 1. This is the genuine leverage: measurement and uncertainty are
  the two poles of one residue tag, dual. **Honest:** the *quantitative* uncertainty inequality
  `ΔX·ΔP ≥ ½|⟨[X,P]⟩|` (variances, the Cauchy–Schwarz/Robertson form) is **not** built — the
  *structural* obstruction (no common eigenbasis when `[A,B]≠0`) is the certified content; the
  variance bound needs a Hilbert inner product (located break).

- **Leg 3 — unitary evolution = the `q=+1` det/holonomy = 1 reading. PREDICTION (consolidation).**
  `det_holonomy_eq_one` (PURE, `HolonomyLattice`) = norm-preserving evolution composes to det 1;
  `S_elliptic_order4`/`U_elliptic_order6` (PURE) = the concrete finite unitaries (det 1, on the unit
  circle). Unitarity = the `q=+1` det1 corner, the same Noether-invariant `curvature.md` read as flat.
  No new primitive.

- **Leg 4 — superposition (linear reading) + Born rule (weight² ). PARTIAL.** Superposition = the
  linear/additive reading of the eigenbasis (`spectral.md`). The Born rule = `probability.md`'s
  weight-reading (`ProbabilityCut`, `joint` = `×↦·` independence, `discreteNum` = expectation — all
  PURE) **squared**, the `|·|²` = the `q=±1` pair-magnitude. **PARTIAL:** the *weight* is built; the
  *amplitude* `⟨ψ|φ⟩` and its `|·|²` (a complex inner product) are not — the closest is the
  Cayley–Dickson `normSq`/conjugation, not welded to the probability weight. The form is predicted;
  the amplitude object is the open leg.

**The located breaks (honest, in the `knots.md`/`lie_theory.md` spirit).** QM pins where the calculus
stops — the genuinely-physics objects, all at the `Real213`/ℂ + Hilbert-space place:
1. **A Hilbert space / inner product `⟨ψ|φ⟩`** — absent. The discrete `Mat2` hosts symmetric operators
   and the commutator; there is no inner-product vector space, hence no amplitude, no `|·|²`, no
   Cauchy–Schwarz → no quantitative Robertson uncertainty bound. The closest built structure
   (Cayley–Dickson `CDNorm`) is a norm without an inner-product/QM weld.
2. **The Born rule as an object** — the *form* is predicted (weight² ), the *amplitude→probability map*
   is not built. The weight (`probability.md`) and a multiplicative norm (`CDNorm`) both exist; their
   composition into `P=|⟨ψ|φ⟩|²` is the named open target.
3. **The measurement collapse / projection** — the `q=+1` eigenprojector and the non-unitary collapse
   map are absent (the spectral-decomposition projector exists only at `d=2` conceptually; the collapse
   is the `q=−1` escape of the otherwise-`q=+1` unitary evolution, un-built). Same `Real213`/ℂ +
   `d>1` spectral-theorem residue `spectral.md`/`representation.md` located.

**Net verdict: PREDICTION.** QM's operator skeleton consolidates `spectral.md` + `lie_theory.md` +
`probability.md` + `curvature.md` under the `q=±1` tag with **no new primitive**: the observable is
the `q=+1` real-spectrum symmetric reading (BUILT, `disc_symmetric_nonneg`); the canonical commutator /
uncertainty is the `q=−1` antisymmetry bracket-residue (bracket BUILT, `Mat2Bracket`); unitary
evolution is the `q=+1` det/holonomy = 1 reading (BUILT, `det_holonomy_eq_one`); the Born rule is the
weight-reading squared (weight BUILT, amplitude `|·|²` conceptual). **The measurement/uncertainty
`q=±1` duality is the leverage**: a real-eigenvalue fixed point (q=+1) and a non-commuting
bracket-obstruction to a common fixed point (q=−1) are the two poles of one residue tag, dual to each
other. The missing legs are the Hilbert space / amplitude `|·|²` / measurement-collapse object — the
`Real213`/ℂ + inner-product residue.

## Does it consolidate spectral + bracket + probability + curvature? — YES (math-structure level).

`spectral.md` read the `q=+1` pole (symmetric ⟹ real spectrum, the measurement fixed point);
`lie_theory.md` read the `q=−1` pole (the antisymmetry bracket); `probability.md` built the weight;
`curvature.md` built det/holonomy = 1. QM is the field that imposes **all four on one operator algebra
at once**, and the uncertainty principle is precisely the *incompatibility of the two poles* (the
`q=−1` bracket forbidding a shared `q=+1` eigenbasis). The consolidation is at the **math-structure**
level — the operator skeleton — NOT a physics-validation claim (per the caveat). The physics-deployment
pieces the repo built independently (`Quantum.Qubit` NT=2, `Quantum.Bell` CHSH bound 12) are atomic
*counts*, orthogonal to this operator decomposition and not claimed as validation here.

## Touches on model v7.1?

**No new primitive; EXTEND + one consolidation note.** The two invariants (character arrow, `q=±1`
residue) and four axes absorb QM with nothing added. The note for the README's batch log:

> **Quantum mechanics is the `q=±1` operator duality on one `C` — measurement = q=+1, uncertainty =
> q=−1.** An observable = the `q=+1` real-spectrum symmetric reading (`disc_symmetric_nonneg`, PURE):
> the Hermitian postulate IS "stay at q=+1", measurement outcomes the real eigenvalues. The canonical
> commutator `[X,P]≠0` = the `q=−1` antisymmetry bracket-residue (`Mat2Bracket`, 10/0 PURE,
> `bracket_antisymm`/`tr_bracket_zero`); the uncertainty principle = the bracket obstructing a common
> `q=+1` fixed point (shared eigenbasis) — measurement and uncertainty are the two poles of one
> `ResidueTag`, dual. Unitary evolution = the `q=+1` det/holonomy = 1 reading (`det_holonomy_eq_one`;
> `S⁴=I`, `U⁶=I`). The Born rule = `probability.md`'s weight-reading squared (weight BUILT; the
> amplitude `|·|²` the open leg). Consolidates spectral + bracket + probability + curvature. Located
> breaks: the Hilbert space / amplitude `⟨ψ|φ⟩` / measurement-collapse object — the `Real213`/ℂ +
> inner-product residue. PHYSICS-branch: a math-structure decomposition, no validation claim.

## Verified Lean anchors (file:line — all grep + `scan_axioms.py`-verified this session; all PURE)

| Leg | Theorem (file:line) | Purity |
|---|---|---|
| ★★★★ observable = symmetric ⟹ real spectrum (the q=+1 corner; the Hermitian postulate) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean:83` `disc_symmetric_nonneg`; `:67` `disc_symmetric_sum_of_squares`; `:52` `IsSymmetric` | **PURE** (9/0, `scan_axioms` this session) ✓ |
| ★ symmetric spectrum-real bundle; non-scalar ⟹ distinct real eigenvalues; gap² ≥ 0 | `…/Mat2SymmetricSpectrum.lean:137` `symmetric_spectrum_real`; `:111` `disc_symmetric_pos_of_nonscalar`; `:156` `symmetric_gap_squared_nonneg`; `:93` `disc_zero_iff_scalar` | **PURE** ✓ |
| ★★★★ canonical commutator `[X,P]=AB−BA` = the q=−1 antisymmetry residue | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:66` `bracket`; `:76` `bracket_antisymm` | **PURE** (10/0, `scan_axioms` this session) ✓ |
| ★★★★ `[A,A]=0` (self-commute = own eigenbasis); `tr[A,B]=0` (traceless / sl — the `iℏ·I` trace-free shadow) | `…/Mat2Bracket.lean:86` `bracket_self`; `:101` `tr_bracket_zero` | **PURE** ✓ |
| ★ Jacobi + Leibniz (the q=−1 graded-relation pole; the bracket's algebra closure) | `…/Mat2Bracket.lean:118` `jacobi`; `:135` `bracket_leibniz` | **PURE** ✓ |
| ★★★★ unitary evolution = norm-preserving = det/holonomy = 1 (the q=+1 flat reading) | `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:136` `det_holonomy_eq_one`; `det_mul` | **PURE** (26/0) ✓ |
| ★★★ concrete finite unitaries: `S` order 4 (`S⁴=I`, det 1), `U` order 6 (`U⁶=I`, det 1) | `…/ModularGeometry/HyperbolicEllipticTrace.lean:78` `S_elliptic_order4`; `:85` `U_elliptic_order6` | **PURE** (5/0) ✓ |
| ★★★ measurement outcome = eigenvalue = q=+1 scale-residue (φ = dominant eigenvalue of `G`) | `…/HyperbolicEllipticTrace.lean:71` `golden_hyperbolic` | **PURE** ✓ |
| ★★ Born rule weight-side = the probability weight-reading (`P=num/den` clamp; independence `×↦·`; expectation) | `Lib/Math/Probability/Foundation/Cut.lean:27` `ProbabilityCut`; `Independence.lean:27` `joint`, `:87` `joint_assoc_num`; `Expectation.lean:27` `discreteNum`, `:62` `discreteNum_append` | **PURE** (per `probability.md`) ✓ |
| physics-branch atomic side (orthogonal counts, NOT operator structure — context only) | `Lib/Physics/Quantum/Qubit.lean:23` `qubit_state_count : NT=2`; `Bell.lean:37` `chsh_bound_value = 12` | **PURE** (grep + Read this session) ✓ |
| cross-frame | `spectral.md` (`Mat2Spectrum` det/tr=e₁/e₂, Cayley–Hamilton), `lie_theory.md` (bracket), `probability.md` (weight), `curvature.md` (`det_holonomy_eq_one`), `ResidueTag` (`Lib/Math/Foundations/ResidueTag.lean` escape/converge) | prior, ∅-axiom ✓ |

## Conceptual-only legs / located breaks (honest — not cited as anchors)

- **A Hilbert space / inner product `⟨ψ|φ⟩` and the amplitude `|·|²`** — absent. No inner-product
  vector space in `lean/E213`; the discrete `Mat2` hosts symmetric operators + the commutator but no
  amplitude. The closest built structure is the Cayley–Dickson norm (`Lib/Math/NumberSystems/SignedCut/CD/CDNorm.lean`
  `cdNormSq`, `CDConjugation`) — a level-indexed norm-squared with conjugation, NOT welded to the
  probability weight as an amplitude→probability map. CONCEPTUAL.
- **The Born rule as an object / the quantitative uncertainty bound `ΔX·ΔP ≥ ½|⟨[X,P]⟩|`** — the
  *forms* are predicted (weight² ; the bracket as obstruction), but the amplitude→probability map and
  the variance/Cauchy–Schwarz inequality need the absent inner product. The *structural* uncertainty
  (no common eigenbasis when `[A,B]≠0`) is the certified content. PARTIAL.
- **The measurement collapse / spectral-decomposition projector at `d>1`** — the eigenprojector and
  the non-unitary collapse map are absent; only the `d=2` symmetric spectral theorem is built. The
  collapse is the `q=−1` escape of the otherwise-`q=+1` unitary evolution, un-built. Same `Real213`/ℂ
  + `d>1` spectral-theorem residue `spectral.md`/`representation.md` located. LOCATED BREAK.
- **The physical `[X,P]=iℏ·I` over ℂ** — the finite `Mat2` cannot host a commutator equal to a nonzero
  multiple of `I` (a commutator is traceless, `tr_bracket_zero`, but `tr(iℏ·I)=2iℏ≠0`); the canonical
  relation is an infinite-dimensional / `Real213`-ℂ fact. The certified content is the *structural*
  trace-free antisymmetry residue, not the `iℏ` value. HONEST CEILING (the same finite-trace cap
  `lie_theory.md` hit for the infinitesimal `ε`).
