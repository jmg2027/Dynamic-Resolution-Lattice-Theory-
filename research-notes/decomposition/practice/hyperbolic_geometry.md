# Decomposition: hyperbolic / non-Euclidean geometry

*213-decomposition of "the three constant-curvature geometries (elliptic `K>0` / Euclidean `K=0` /
hyperbolic `K<0`), the angle-sum-vs-π trichotomy, the parallel postulate's three fates, the
Gauss–Bonnet theorem `∫K = 2πχ`, the isometry group `PSL(2,ℝ)`, the upper-half-plane model", per
`../README.md` (model v7.1) and `../SYNTHESIS.md` §3 (the q=±1 spine, the discriminant-sign trichotomy).
A **fresh** field, LEVERAGE phase — the bar is PREDICTION/REVELATION. Sits directly atop `spectral.md`
(the `disc` sign, `Mat2SymmetricSpectrum.disc_symmetric_nonneg`), `golden_ratio.md` (`golden_hyperbolic`,
the hyperbolic vs elliptic split), `continued_fractions.md` (`GoldenAperiodic` vs `FiniteOrderSpectrum`),
`curvature.md` (the discrete Gauss–Bonnet `Σκ=2χ`), and `modular_forms.md` (the `PSL(2,ℤ)` action, the
upper half-plane).*

The thesis under test: **hyperbolic geometry is the calculus's q=±1 / discriminant-sign trichotomy made
the curvature sign.** The three constant-curvature geometries are the *same* trichotomy the corpus already
proves — `disc>0` hyperbolic (real spectrum, two real eigenvalues, the q=−1 escaping/expanding pole,
`golden_hyperbolic`/`golden_aperiodic`) / `disc<0` elliptic (complex spectrum, rotation, finite order, the
q=+1 periodic pole, `FiniteOrderSpectrum.finite_order_divides_twelve`) / `disc=0` parabolic (flat, the
marginal cusp). The isometry group `PSL(2,ℝ)` = `modular_forms.md`'s `PSL(2,ℤ)`/Stern–Brocot Möbius
holonomy; Gauss–Bonnet `∫K=2πχ` = the curvature–Euler telescope already built discretely. No new primitive.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the `Mat2` ×-construction acting by Möbius transformations on the cusp/geodesic
  lattice, nothing new.** A geometry's isometry group is `curvature.md`/`modular_forms.md`'s holonomy
  monoid `(Mat2, mul)` (`HolonomyLattice.holonomy`, a `List Mat2` of transitions folded to its net
  transition by `holonomy_append`). `PSL(2,ℝ)` is this same `Mat2` Möbius action `z ↦ (az+b)/(cz+d)` read
  on the upper half-plane; `PSL(2,ℤ)` is its arithmetic restriction `det=1` on the Stern–Brocot/Farey
  cusps (`ModularGeodesicLens.mediantLens`, whose `view` is "one geodesic on `ℍ/PSL(2,ℤ)`", `Raw`'s own
  self-pointing read as a Farey position). The "point of the plane" / "geodesic" the geometry talks about
  is read off this lattice — `mediantLens_view_reachable` proves every `Raw` view lands on a Stern–Brocot
  geodesic. So hyperbolic geometry **introduces no new construction** — it reads the same `Mat2`
  ×-construction the spectral/modular cluster already uses.

- **Reading `L_curv` — the curvature sign = the discriminant sign of the Möbius generator.** The geometry
  of a constant-curvature space is fixed by the *sign of one number*: the discriminant `disc = tr²−4·det`
  of the isometry generator, which is the squared eigenvalue gap `(μ−ν)²` (`spectral.md`,
  `disc_eq_gap_squared`). Reading `L_curv` projects each generator to this sign — and that sign **is** the
  curvature sign, the angle-sum verdict, and the parallel-postulate fate, all at once:

  | sign | geometry | isometry type | spectrum | angle sum | parallels | q-tag |
  |---|---|---|---|---|---|---|
  | `disc > 0` | hyperbolic (`K<0`) | boost / translation along a geodesic | two distinct **real** eigenvalues (a *scaling*, `golden_hyperbolic`) | `< π` (defect) | **many** | q=−1 escape (infinite order, `golden_aperiodic`) |
  | `disc = 0` | Euclidean (`K=0`) | parabolic shear (fixed point at the cusp `∞`) | repeated real eigenvalue | `= π` | **one** | the marginal boundary (`fixForm T`, the cusp) |
  | `disc < 0` | elliptic (`K>0`, sphere) | rotation | complex-conjugate pair on the unit circle (a *rotation*) | `> π` (excess) | **none** | q=+1 converge (finite order, `finite_order_divides_twelve`) |

  This is *literally* `CrossDetTraceField`'s **line/cusp/curve** trichotomy `disc_sign_is_line_cusp_curve`
  (`traceDisc G > 0 ∧ traceDisc T = 0 ∧ traceDisc U < 0`) — the hyperbolic geodesic (real-quadratic
  `ℚ(√5)`, the "line"), the parabolic cusp (rational, the boundary), the elliptic torus (imaginary-quadratic
  `ℚ(ω)`, the bounded "curve"). The curvature reading is the discriminant-sign reading.

- **Residue, tagged q=±1** — the curvature itself, as the loop-reading's surplus, with the sign of the
  surplus carried by the multiplier bit. Two strata:
  - **the holonomy deficit `q=±1` bit** (`curvature.md`): curvature = the deficit by which the loop-fold
    `holonomy w` fails to be `I`; flat = the q=+1 conserved character `det_holonomy_eq_one`, curved = the
    deficit pole. The hyperbolic/elliptic *type* is the `disc`-sign reading of that surplus.
  - **the smooth Riemannian curvature `K` / the analytic `∫K`** — the `Real213`-cut RESIDUE, reached by no
    finite resolution (the smooth metric, `lim_{loop→0}(holonomy−I)/area`). The discrete Gauss–Bonnet
    `Σκ=2χ` is the computable modulus; the smooth `∫K=2πχ` is its reached-by-none limit (the `2π` is a
    `Real213`-cut, the angle measure). The named `HyperbolicPlane`/`PSL2R`/`sectionalCurvature` objects are
    **ABSENT** (grep-confirmed below) — predicted-not-built.

## Re-seeing — ⟨C | L_curv⟩ ⊕ Residue

```
   PSL(2,ℝ) / PSL(2,ℤ) action   =  ⟨ List Mat2 | L_loop holonomy ⟩          (the Möbius holonomy, holonomy_append)
   the upper half-plane ℍ        =  the cusp/geodesic lattice                (ModularGeodesicLens, ℍ/PSL(2,ℤ))
   curvature SIGN                =  L_curv = sign(disc = tr²−4det) = sign(μ−ν)²   (disc_eq_gap_squared)
   K < 0  hyperbolic / line      =  disc > 0, two real eigenvalues (scaling)  (golden_hyperbolic; traceDisc G > 0)
   K = 0  Euclidean / cusp       =  disc = 0, repeated eigenvalue (shear)      (parabolic; traceDisc T = 0)
   K > 0  elliptic / curve       =  disc < 0, complex pair (rotation)          (S/U elliptic; traceDisc U < 0)
   angle sum  <π / =π / >π       =  the curvature sign read on a triangle       (= the disc-sign trichotomy)
   parallel postulate's 3 fates  =  the same three disc signs (many/one/none)   (one trichotomy, three names)
   hyperbolic = infinite order   =  q=−1 escape, the boost never returns         (golden_aperiodic, disc>0)
   elliptic = finite order       =  q=+1 converge, periodic floor                (finite_order_divides_twelve, disc<0)
   flat connection               =  the q=+1 conserved character det = 1         (det_holonomy_eq_one)
   curvature                     =  Residue(L_loop): holonomy w ≠ I deficit       (first_loop_is_the_fold, q=−1)
   Gauss–Bonnet  ∫K = 2πχ        =  Σκ = 2χ = 2(1−b₁), the curvature–Euler telescope  (gauss_bonnet_Kmn, totalCurv_eq)
```

The single move: the three constant-curvature geometries are **not three spaces** — they are the **one
discriminant-sign trichotomy** the spectral/golden/CF cluster already proves, read as the curvature sign.
The angle-sum trichotomy (`<π`/`=π`/`>π`), the parallel postulate's three fates (many/one/no parallels),
and the isometry types (boost/shear/rotation) are **one number's sign read three ways**, and the isometry
group is the same `Mat2` Möbius holonomy `modular_forms.md` uses.

## Re-seeing table (the unification)

| classical hyperbolic-geometry object | the calculus's reading | repo status |
|---|---|---|
| the curvature sign `K ≷ 0` of a constant-curvature geometry | `L_curv` = sign of `disc = tr²−4det = (μ−ν)²` | **BUILT** (`disc_sign_is_line_cusp_curve`, `wick_discriminant_split`) |
| hyperbolic `K<0` (Lobachevsky) | `disc>0`: two real eigenvalues, a scaling boost, infinite order (q=−1 escape) | **BUILT** (`golden_hyperbolic`, `golden_aperiodic`) |
| elliptic `K>0` (sphere) | `disc<0`: complex pair, a rotation, finite order (q=+1 converge) | **BUILT** (`S_elliptic_order4`, `U_elliptic_order6`, `finite_order_divides_twelve`) |
| Euclidean `K=0` (flat) | `disc=0`: repeated eigenvalue, parabolic shear, the marginal cusp | **BUILT** (`traceDisc T = 0`, `signature_trichotomy` parabolic) |
| angle sum `<π / =π / >π`; parallel postulate's 3 fates | the curvature sign read on a triangle = the disc-sign trichotomy | structural prediction (the *number* built; no triangle/angle object) |
| isometry group `PSL(2,ℝ)` acting on `ℍ` | the `Mat2` Möbius holonomy (`PSL(2,ℤ)` arithmetic restriction) | **BUILT** (`holonomy_append`, `mediantLens_view_reachable`) |
| Gauss–Bonnet `∫K = 2πχ` | the curvature–Euler telescope `Σκ = 2χ = 2(1−b₁)` | **BUILT discretely** (`gauss_bonnet_Kmn`, `totalCurv_eq`) |
| flat connection / `K=0` everywhere | the q=+1 conserved character `det=1` | **BUILT** (`det_holonomy_eq_one`) |
| the smooth metric / `sectionalCurvature K` / `HyperbolicPlane` / `PSL2R` object | the `Real213`-cut smooth residue | **ABSENT** (the located break) |

## Revelation (collapse + forcing + the q=±1 spine)

**Collapse — the three geometries ARE the one disc-sign trichotomy the corpus already proves; this is the
NEW datum.** `spectral.md` proved `disc>0` real spectrum (hyperbolic/φ) vs `disc<0` complex spectrum
(elliptic/rotation); `golden_ratio.md` and `continued_fractions.md` proved `golden_aperiodic` (`disc=5>0`,
infinite order) vs `finite_order_divides_twelve`/`crystallographic_spectrum` (`disc<0`, periodic floor);
`CrossDetTraceField` proved the line/cusp/curve trichotomy `disc_sign_is_line_cusp_curve`. **Hyperbolic
geometry is these three theorems read as the curvature sign**: the constant-curvature geometry of a space is
exactly the discriminant sign of its isometry generator. So the geometric trichotomy (elliptic/Euclidean/
hyperbolic), the spectral trichotomy (complex/repeated/real spectrum), the dynamical trichotomy (finite-
order/parabolic/infinite-order), and the arithmetic trichotomy (`ℚ(ω)`/`ℚ`/`ℚ(√5)`) are **ONE trichotomy**
— the sign of `(μ−ν)²` = `tr²−4det`. This unifies `spectral.md` + `golden_ratio.md` +
`continued_fractions.md`'s separately-recorded trichotomies as one *geometric* trichotomy, which is the new
contribution beyond re-skinning `curvature.md`/`spectral.md`.

**Forcing — the curvature sign is FORCED to be the discriminant sign, not chosen.** The geometry's type is
fixed the moment the generator is fixed: `disc = tr²−4det` is a pure `ℤ` polynomial in the generator's
entries, and its sign decides real-vs-complex spectrum (`disc_symmetric_nonneg`: a symmetric generator has
`disc≥0`, structurally barring the elliptic/rotation case — the real spectrum is forced by symmetry, exactly
the spectral theorem's "real eigenvalues from positivity"). The isometry *type* (boost/shear/rotation) is
not an added classification — it is read off the one discriminant by `wick_discriminant_split`. The
parallel postulate is not three independent axioms but the three signs of one number; "the parallel
postulate is independent" = "the disc sign is a free parameter of the generator", and the *absence* of a
distinguished sign is the structural absence of an exterior dialer (no privileged geometry).

**The q=±1 spine (`SYNTHESIS.md` §3) made the curvature sign.** The hyperbolic/elliptic split is the
`ResidueTag` `±1` bit (`residue_tag_two_poles`, `multiplier_unimodular`):
- **q=−1 escape = hyperbolic.** The boost has infinite order (`golden_aperiodic`: `Gⁿ⁺¹≠I` ∀n), the orbit
  expands toward the dominant real eigendirection and **never returns** — the `disc>0` expanding pole, the
  same q=−1 escape as `golden_ratio.md`'s reached-by-none φ and `cardinality.md`'s diagonal. Negative
  curvature = exponential geodesic divergence = the escaping residue.
- **q=+1 converge = elliptic.** The rotation has finite order (`finite_order_divides_twelve`,
  `S_elliptic_order4`, `U_elliptic_order6`), the orbit is periodic and bounded — the `disc<0` converging
  pole, the same q+1 corner as φ's fixed point and the Banach contraction. Positive curvature = bounded
  periodic geodesics = the converging residue.
- **the parabolic cusp = the marginal boundary** between the two poles (`signature_trichotomy`'s
  semi-definite middle, `fixForm T` disc 0), exactly `SYNTHESIS.md`'s "Euclidean is the boundary the spine
  is symmetric about".

So hyperbolic geometry = (the q=±1 disc-sign trichotomy = the curvature sign) + (`PSL(2,ℝ)` = the Möbius
holonomy) + (Gauss–Bonnet = the curvature–Euler telescope) — **no new primitive**.

## VALIDATE verdict — **EXTEND** (deep consolidation: three trichotomies unified as one geometric one; one PREDICTION leg; one located break)

No new primitive, no break in the interior. Hyperbolic geometry slots entirely into the v7.1 model: `C` =
the `Mat2` Möbius ×-construction (direction/`q=±1` + fold-height carried), `L_curv` = the discriminant-sign
reading, `Residue` = the holonomy deficit / smooth curvature tagged `q=±1`. It is a **decisive
consolidation**: the discriminant-sign trichotomy that `spectral.md`, `golden_ratio.md`, and
`continued_fractions.md` each recorded separately is now seen as **one geometric trichotomy** (elliptic/
Euclidean/hyperbolic = the curvature sign), with `PSL(2,ℝ)` the Möbius holonomy and Gauss–Bonnet the
curvature–Euler telescope already built discretely.

- **PREDICTION leg (honest):** the *angle-sum / parallel-postulate trichotomy as named geometric theorems*
  (a triangle object, an `angleDefect`, a `parallelCount`) is grounded only at the *number* altitude — the
  disc-sign trichotomy is built (`disc_sign_is_line_cusp_curve`, `signature_trichotomy`), but no
  triangle/angle/parallel-line object reads it off. The calculus *predicts* the angle sum is the curvature
  sign read on a triangle (Gauss–Bonnet on a geodesic triangle: `area = |∫K| = |angle sum − π|`); the
  smooth version is the named open leg.

- **Located break (the `knots.md`/`modular_forms.md` spirit):** the **smooth Riemannian geometry object** —
  a `HyperbolicPlane`/`UpperHalfPlane`-with-metric, `PSL2R` as a Lie group, `sectionalCurvature K` as a
  smooth `Real213`-cut function, the smooth Gauss–Bonnet `∫K=2πχ` with the `2π` angle measure — is ABSENT
  (grep-confirmed). The discrete parallel theory is the worked instance; the smooth curvature *field* is the
  `Real213`-cut residue, exactly the boundary `curvature.md` already located (no smooth metric, no
  transported curvature tensor, only the abstract-index `TensorCalculus.riemUp` Riemann tower and the
  discrete Gauss–Bonnet).

## Verified Lean anchors (file:line:theorem) — all grep-confirmed, scans from repo root

**The discriminant-sign trichotomy = the curvature sign (the central NEW collapse):**
- `lean/E213/Lib/Math/NumberSystems/Real213/CrossDet/CrossDetTraceField.lean:248` `disc_sign_is_line_cusp_curve`
  — `traceDisc G > 0 ∧ traceDisc T = 0 ∧ traceDisc U < 0`, the **line/cusp/curve = hyperbolic/parabolic/
  elliptic** trichotomy (`ℚ(√5)` line / rational cusp / `ℚ(ω)` curve); `:70` `traceDisc`, `:88`
  `fixForm_disc_eq_traceDisc` (the universal identity `formDisc(fixForm M) = tr²−4det`, ∀M). **PURE (20/0).**
- `lean/E213/Lib/Math/Algebra/CayleyDickson/Integer/ParabolicSignature.lean:71` `signature_trichotomy`
  — golden indefinite (disc+5, line) / parabolic semi-definite (disc 0, cusp) / Eisenstein definite (disc−3,
  curve); `:50` `parab_nonneg`. **PURE (4/0).**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HyperbolicEllipticTrace.lean:71`
  `golden_hyperbolic` (`det G=1 ∧ tr G=3 ∧ disc G=5 ∧ 0<disc G` — the hyperbolic boost, two real eigenvalues
  `φ²,φ⁻²`); `:78` `S_elliptic_order4`, `:85` `U_elliptic_order6` (the elliptic rotations, `disc<0`); `:96`
  `wick_discriminant_split` (the trichotomy as the discriminant's sign). **PURE (5/0 scanned; the nested
  `disc`/`I` constants are not directly probeable by the scanner but the theorems scan PURE).**

**The spectrum / discriminant = squared eigenvalue gap (ties to `spectral.md`):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean:83` `disc_symmetric_nonneg`
  (`IsSymmetric M → 0 ≤ disc M` — symmetric generator ⟹ real spectrum ⟹ elliptic/rotation barred, the
  q=+1 corner); `:67` `disc_symmetric_sum_of_squares`, `:93` `disc_zero_iff_scalar`, `:111`
  `disc_symmetric_pos_of_nonscalar`. **PURE (9/0).**
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2CayleyHamilton.lean:37` `cayley_hamilton`
  (`M²=tr·M−det·I`, the order-2 dial the trichotomy specializes); `:50` `char_poly_discriminant`; `:57`
  `dial_is_char_discriminant`. **PURE (4/0).**
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2Spectrum.lean:167` `disc_eq_gap_squared`
  (`disc M = (μ−ν)²`); `:103` `det_eq_e2`, `:115` `tr_eq_e1`, `:204` `det_tr_split_is_e1_e2`. (per `spectral.md`)

**q=−1 hyperbolic escape vs q=+1 elliptic converge (the dynamical trichotomy):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Phi/GoldenAperiodic.lean:57` `golden_aperiodic`
  (`pow G (n+1) ≠ I` ∀n — `disc>0` ⟹ infinite order = q=−1 escape, the expanding boost); `:25`
  `golden_trace_mono`. **PURE (3/0).**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/FiniteOrderSpectrum.lean:503`
  `finite_order_divides_twelve` (`det M=1 → order divides 12` — `disc<0` ⟹ periodic floor = q=+1 converge);
  `:603` `crystallographic_spectrum`, `:527` `no_order_five`. **PURE (29/0).**
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:228` `residue_tag_two_poles`; `:86` `multiplier_unimodular`;
  `:180` `golden_is_converge`; `:133` `escape_residue_outside`; `:160` `converge_residue_fixed`. **PURE (55/0).**

**`PSL(2,ℝ)`/`PSL(2,ℤ)` = the Möbius holonomy on `ℍ`; the upper-half-plane lattice:**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:108` `holonomy_append`
  (the loop-fold is a monoid homomorphism = functorial Möbius transport); `:136` `det_holonomy_eq_one` (flat
  = q=+1 conserved character `det=1`); `:313` `first_loop_is_the_fold` (`holonomy[S,S]=−I≠I`, the curvature
  deficit q=−1); `:292` `positive_loop_trivial`. **PURE (26/0).**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/ModularGeodesicLens.lean:67`
  `mediantLens_view_reachable` (every `Raw` view lands on a Stern–Brocot geodesic on `ℍ/PSL(2,ℤ)`); `:37`
  `mediantLens`. (the upper-half-plane = the cusp/geodesic lattice; per `modular_forms.md`/`continued_fractions.md`)

**Gauss–Bonnet = the curvature–Euler telescope (discrete, per `curvature.md`):**
- `lean/E213/Lib/Math/Geometry/DiscreteCurvature/DiscreteGaussBonnet.lean:42` `gauss_bonnet_Kmn`
  (`totalVertexCurv = 2·eulerChar`, the discrete `Σκ=2χ`); `:53` `totalCurv_eq` (`= 2−2·cyclomatic`, total
  `=2−2b₁`); `:59` `curvature_sign_topology`. **PURE (12/0).**
- `lean/E213/Lib/Math/Geometry/DiscreteCurvature/DiscreteRicci.lean:63` `forman_K11` (`=2>0`, tree/positive
  curvature); `:69` `forman_K32` (`=−1<0`, cyclic/negative curvature); `:75` `discrete_curvature_topology`.
  **PURE (9/0).**

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root):**
`CrossDetTraceField` 20/0 · `ParabolicSignature` 4/0 · `HyperbolicEllipticTrace` 5/0 (nested-constant probe
errors only, theorems PURE) · `Mat2SymmetricSpectrum` 9/0 · `Mat2CayleyHamilton` 4/0 · `GoldenAperiodic` 3/0 ·
`FiniteOrderSpectrum` 29/0 · `ResidueTag` 55/0 · `HolonomyLattice` 26/0 · `DiscreteGaussBonnet` 12/0 ·
`DiscreteRicci` 9/0. All PURE, 0 DIRTY.

## Dropped / flagged (honest)

- **The smooth Riemannian geometry object — ABSENT, predicted-not-built.** grep over `lean/E213` for
  `HyperbolicPlane`/`UpperHalfPlane`/`PSL2R`/`sectional`/`Lobachevsky`/`constant_curvature`/`hyperbolic_metric`
  returns **no Lean object** (only doc-comment mentions of `ℍ/PSL(2,ℤ)` in `ModularGeodesicLens`,
  `MinkowskiModularSymbol`, `CrossDetTraceField`). The named `HyperbolicPlane`/`PSL2R`/`sectionalCurvature K`/
  smooth `∫K=2πχ` are confirmed absent — the located break, the `Real213`-cut smooth-metric residue (the same
  boundary `curvature.md`/`SYNTHESIS.md` §5.5 locate: no smooth metric, no transported curvature field).
- **`angle_sum`/`parallel`/`defect` grep hits are FALSE FRIENDS** — `parallel` appears only as "parallel to
  the … spine" (prose in `MarkovTree`), `defect` only as the cocycle defect in `MinkowskiCocycle`; neither is
  a geometric angle/parallel-line object. Confirmed not load-bearing; not cited.
- **The angle-sum / parallel-postulate trichotomy as a named geometric theorem** (a triangle, an
  `angleDefect`, a `parallelCount`) — predicted-not-built. Grounded only via the disc-sign *number*
  trichotomy (`disc_sign_is_line_cusp_curve`, `signature_trichotomy`). Stated as the open leg, not asserted.
- **The smooth Gauss–Bonnet `∫K=2πχ` with the `2π` angle measure** — the `2π` is a `Real213`-cut; only the
  discrete `Σκ=2χ` (integer-valued, `gauss_bonnet_Kmn`) is built. Cited scope-honest.
- **Verified buildable witness (decidable, TRUE — proposed):** the curvature-sign trichotomy is already a
  `decide`-checked theorem (`disc_sign_is_line_cusp_curve`, by `decide`); a clean additional smoke confirming
  the three signs as one number's sign on the standard generators — `disc G = 5 ∧ disc T = 0` style — is
  already covered by `golden_hyperbolic`/`wick_discriminant_split` (both PURE by `decide`). No new
  count-inequality is asserted beyond the grep-confirmed, scanned-PURE anchors above; no decide witness is
  proposed that was not actually checked.
