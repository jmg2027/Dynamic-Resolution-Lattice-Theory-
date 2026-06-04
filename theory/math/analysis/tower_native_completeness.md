# Tower-native completeness — completability is a comparison of two growth-axes

**Status**: Closed.  Source of truth (all ∅-axiom):
`lean/E213/Lib/Math/NumberSystems/Real213/{CrossDetOvertake, LiouvilleModulus, TowerNativeCompleteness,
IntensionalCompletability, ScalingOrbit, FloorReferenceForm}`,
`lean/E213/Lib/Math/Analysis/Cauchy/{DepthClosure, DepthCoordGenerator, DepthCeilingResidue}`,
`lean/E213/Lib/Math/Algebra/CayleyDickson/Integer/{EisensteinSignature, ParabolicSignature}`,
`lean/E213/Lib/Math/FiveFloorUnification`.

## Overview

A Real213 real is a decision procedure against ℚ that completes by a *modulus*; the
constructed-modulus mechanism (`holonomic_modulus.md`) reduces "does this real
complete freely?" to a single inequality on the convergents' **cross-determinant**
`W_i = a_{i+1}d_i − a_i d_{i+1}` against the **denominator** `d` —
`Htel_of_crossdet`'s smallness condition

> `i·(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}`   (`CrossDetSmall W d`).

Both sides are objects *inside* the resolution tower (`completeness_without_completeness.md`).
So the classical, external "irrationality measure" is replaced by an internal
comparison of two growth-axes.  This chapter closes that comparison: it stratifies
completability by where the cross-determinant axis sits relative to the denominator
axis, shows the finite-coordinate trajectories form a class closed under the tower's
operations, exhibits a generator that realizes every coordinate, and ties the
top-lessness of the tower to the residue of pointing.

## Lean source

| File | PURE / dirty | Content |
|---|---|---|
| `Real213/CrossDetOvertake.lean` | 11 / 0 | the boundary: `CrossDetSmall`, below ⟹ free, the overtake break |
| `Real213/LiouvilleModulus.lean` | 13 / 0 | Liouville: `W = d`, factorial denominator dominates ⟹ free modulus |
| `Real213/CrossDetEqDenom.lean` | 3 / 0 | the `W = d` rung: one theorem behind both e and Liouville |
| `Real213/ReciprocalSeries.lean` | 12 / 0 | the `W = d` line as a ratio-parametrized reciprocal-series reference family (`Σ 1/d`); e = linear-ratio point |
| `Real213/CrossDetConstDenom.lean` | 13 / 0 | the `W = const` rung + φ (Fibonacci convergents) as its named instance |
| `Real213/ContinuedFractionFloor.lean` | 17 / 0 | the universal det-one floor: any partial-quotient sequence's convergent cross-determinant is a unit (`cf_det_sq`, `W² = 1`); even two-step `W'_{2n} = a_{2n+2}` |
| `Real213/ContinuedFractionModulus.lean` | 16 / 0 | every real `≥ 1` completes through its continued fraction (`cf_universal_total_modulus`); the `W = const` φ-rung over an arbitrary partial-quotient sequence |
| `Real213/GeometricThreshold.lean` | 6 / 0 | the exact growth-rate boundary: geometric `W=r^i` over `d=q^i` free **iff** `r < q` |
| `Real213/PresentationDependence.lean` | 6 / 0 | `CrossDetSmall` reads the representation, not the real (`rcut` rescaling-invariant) |
| `Real213/IntensionalCompletability.lean` | 3 / 0 | the test is presentation-relative, the completion presentation-invariant |
| `Real213/ScalingOrbit.lean` | 7 / 0 | the rescaling orbit is one cut; `CrossDetSmall` antitone; unique reduced base |
| `Cauchy/DepthClosure.lean` | 16 / 0 | finite-coordinate class closed under `×` and the exponent axis |
| `Cauchy/DepthCoordGenerator.lean` | 10 / 0 | the tower as a coordinate system, generated top-down |
| `Real213/FloorReferenceForm.lean` | 2 / 0 | the det-one floor's golden form is indefinite (the completing line) |
| `CayleyDickson/Integer/EisensteinSignature.lean` | 13 / 0 | Eisenstein norm definite; det-one floor = the 6-unit group (`PolyInt2`) |
| `CayleyDickson/Integer/ParabolicSignature.lean` | 4 / 0 | the disc-`0` parabolic cusp completes the line / cusp / curve trichotomy |
| `FiveFloorUnification.lean` | 1 / 0 | the completability floor `P` = the McKay E₈ endpoint mod `5 = NS+NT` |
| `Cauchy/DepthCeilingResidue.lean` | — | the tower has no top = the residue of pointing |
| `Real213/TowerNativeCompleteness.lean` | — | `tower_native_completeness_program`, the five bundled |

Builds under the `E213.Lib.Math.NumberSystems.Real213` and `E213.Lib.Math.Analysis.Cauchy` umbrellas.

## Narrative

### The reframing

In the tower a real is not a *point* but a **divergence trajectory**: the
cross-determinant `W`, its ratio, its differences, descending the resolution axes to a
constant floor (`completeness_without_completeness.md`).  Each trajectory has a
coordinate.  `Htel_of_crossdet` says the trajectory carries a free modulus when its
cross-determinant axis stays below the denominator axis.  Completability is therefore
a relation between two tower-internal growth-axes, read off the coordinate — there is
no set of arbitrary reals to quantify over, only trajectories.

### The boundary (`CrossDetOvertake`)

Over the *fixed* single-exponential denominator `d_i = 2^i`, the position of the
cross-determinant decides completability:

  - **below ⟹ free** (`crossdet_small_total_modulus`): when `CrossDetSmall` holds, the
    smallness feeds `Htel_of_crossdet` then `rate_total_modulus`, giving the total
    modulus `N(m,k) = k+2`.  The free bottom is concrete — a **constant**
    cross-determinant `W_i = 1` (the det-one floor) satisfies `CrossDetSmall` against
    `2^i` (`const_crossdet_small`, since `i ≤ 2^i`);
  - **above ⟹ broken** (`overtake_breaks`): if the cross-determinant overtakes the
    *next* denominator (`d_{i+1} ≤ W_i`, `i ≥ 2`), the smallness condition is false.
    The witness `dexp_overtakes_denom` is the **double exponential** `W_i = 2^{2^i}` —
    the same object whose ratio-axis floor never exists (`DepthDoubleExp.dexp_not_const`)
    — which overtakes `2^i` via `2^{i+1} ≤ 2^{2^i}` (because `i+1 ≤ 2^i`).

`completability_boundary` bundles the two regimes.  The overtake falsifies the
*sufficient* bridge; it is the honest tower-internal boundary, not a proof that no
modulus whatsoever exists.

Between the constant and the double-exponential the boundary is a precise **growth-rate
threshold** (`GeometricThreshold`).  Over a geometric denominator `d_i = q^i` with a
geometric cross-determinant `W_i = r^i`, `CrossDetSmall (r^·) (q^·)` holds **iff** the
cross-determinant grows *strictly* slower than the denominator: an exact boundary
`geom_boundary_iff : CrossDetSmall (r^·) (q^·) ↔ r < q` (for `q ≥ 2`).  The threshold is
`r < q`, **not** `r ≤ q` — the equal-rate case `r = q` already fails, because the
polynomial factor `i(i+1)` on the cross-determinant side is linear in `i` while the
single extra denominator factor `q` is only linear in `q`.  The free side holds for all
`i ≥ 1` (`geom_crossdet_small`, sharpening the engine `succ_pow_ge`,
`r^{n+1} + (n+1)·r^n ≤ (r+1)^{n+1}`, which absorbs the polynomial factor into one base
increment); the broken side (`geom_crossdet_overtake_sharp`, every `q ≤ r`) is tested at
the single fixed witness index `i = q`, where smallness would force
`q(q+2)·q^q ≤ q(q+1)·q^q`.  Matching the denominator's exponential rate is not enough.

### Liouville is tame on this axis (`LiouvilleModulus`)

On the value axis the Liouville exponent `k!` is depth-∞ (`DepthLiouvilleCoord`:
`diff(k!) = k·k!` never floors), so a Liouville number looks maximally pathological.
The cross-determinant axis says the opposite.  Present the Liouville constant
`Σ_j c^{-j!}` by the recurrence with growth factor `g_k = c^{k·k!}`:

> `liouDen c 0 = c`,  `liouDen c (k+1) = g_k · liouDen c k`  (`= c^{k!}`),
> `liouNum c 0 = 1`,  `liouNum c (k+1) = g_k · liouNum c k + 1`.

Then the cross-determinant **collapses to the denominator** — `liou_cross_det`:
`liouNum_{k+1}·liouDen_k = liouNum_k·liouDen_{k+1} + liouDen_k`, i.e. `W_k = liouDen_k`
— exactly the e pattern (`euler_cross_det`).  The factorial denominator grows so fast
(`g_k = c^{k·k!} ≥ k+1`, `succ_le_g`, reusing `two_pow_ge_succ`) that `CrossDetSmall`
holds (`liou_crossDetSmall`), so `liouville_total_modulus` gives the free modulus
`N(m,k) = k+2`.  `liouville_W_eq_denom_coordinate` is the adjudication: `W` equals `d`,
`d`'s exponent **is** the factorial (`liouDen_closed`, `liouDen_k = c^{k!}`), and the
factorial sits at recursion-coordinate ratio-depth 1 one tier down (`ratioLift_fact`,
`k! ↦ k+1`).  So the recursion-coordinate of `W` coincides with that of `d` while `d`
strictly dominates — the comparison comes out `W ≤ d`, and a Liouville number completes
exactly like e.  The value-axis depth-∞ is irrelevant to completability.

### The W-relation rungs (`CrossDetEqDenom`)

The cross-determinant's relation to the denominator sorts the trajectories into rungs,
all read through the one bridge `CrossDetSmall ⟹ free`:

  - **`W` constant** — the algebraic det-one floor (`DepthFloorDetOne`, φ/√2 with
    `W = 1`); `crossdet_const_total_modulus` is the rung, and φ is its concrete named
    inhabitant (`CrossDetConstDenom.phi_total_modulus_via_const`): φ's even-indexed
    Fibonacci convergents `fib(2i+2)/fib(2i+1)` have constant cross-determinant `1` (the
    Cassini unit) and a denominator with φ²-step growth that dominates `i(i+1)` for all
    `i ≥ 1`, so φ completes through the *same* bridge as e and Liouville;
  - **`W = d`** — the self-similar rung (e and the Liouville constant); the one theorem
    `crossdet_eq_denom_total_modulus` covers both, with `CrossDetSmall d d` collapsing
    (`i(i+1)+i = i(i+2)`) to a denominator-growth condition, and
    `euler_total_modulus_via_eq_denom` / `liouville_total_modulus_via_eq_denom` the
    one-line instances.  The `W = d` relation cross-divides to
    `a_{i+1}/d_{i+1} − a_i/d_i = 1/d_{i+1}`, so this rung is exactly the
    **reciprocal-denominator series** `Σ 1/d_j` (`ReciprocalSeries.recip_unit_increment`):
    a *one-parameter reference family* indexed by the ratio `g_i = d_{i+1}/d_i`, built
    canonically from `g` (`den`/`num`, `recip_cross_det` gives `W = d` by construction)
    and completing exactly when the ratio grows at least linearly, `i+1 ≤ g_i`
    (`recip_total_modulus`).  e is the linear-ratio point `g_i = i+1`
    (`den_linear_is_factorial`: denominators `= j!`), the Liouville constants the
    fast-ratio points `g_i = c^{i·i!}` — the diagonal is a growth-graded family of
    self-completing reals, each named by its ratio sequence.  (Whether *every* real
    admits a reciprocal-series representation — a universal chart — is a deeper open
    question.)
  - **`W ≫ d`** — the overtake (`dexp_overtakes_denom`), where `CrossDetSmall` fails.

So "constant cross-determinant" (algebraic) and "cross-determinant equal to the
denominator" (the two structured transcendentals proven here) are two rungs *inside*
the free region, and the double exponential is the first rung outside it.

### Every real rides the floor (`ContinuedFractionFloor`, `ContinuedFractionModulus`)

The `W = const` rung is not special to φ.  Present **any** real by its continued
fraction `a : ℕ → ℕ` (partial quotients), with convergent numerators/denominators
`p_{n+2} = a_{n+2}·p_{n+1} + p_n`, `q` likewise.  The convergent cross-determinant
`W_n = p_{n+1}·q_n − p_n·q_{n+1}` runs through the universal Cassini engine
`cf_det_step`: `W_{n+1} = −W_n`, the partial-quotient terms cancelling by commutativity
(the `q = 1` case `cassini_one` of the general second-order recurrence determinant).
Hence `cf_det_sq`: `W_n² = 1` for **every** `n` and **every** partial-quotient sequence
— the det-one floor is the *universal* best-approximation locus, and `FibCassiniNat`'s
φ-instance is the all-`1`s case.

The even-indexed convergents `p_{2n}/q_{2n}` are a positive-denominator, strictly
increasing convergent system whose two-step cross-determinant is a partial quotient:
`cfDet2_even`, `W'_{2n} = p_{2n+2}·q_{2n} − p_{2n}·q_{2n+2} = a_{2n+2}·W_{2n} = a_{2n+2}`
(the `+1` even floor amplified to the quotient).  Over `ℕ` (`cfDet2_even_nat`, descended
from `ℤ` by `ofNat` injectivity) this is exactly the bridge's `hW` for `a' = p_{2·},
d' = q_{2·}, W' = a_{2·+2}`.  The denominators grow at least like Fibonacci
(`cfQn_fib`, `q_{n+2} ≥ q_{n+1} + q_n`, hence `cfQn_ge_self`, `n ≤ q_n`), which is
precisely enough to satisfy `CrossDetSmall` at every index (`cf_hcs`: the smallness
inequality reduces to `i ≤ q_{2i+1}`).  A single strict step gives across-layer
monotonicity for any positive-denominator system (`mono_of_step`, the reusable
`ratio_trans` chaining made generic), supplying `hmono`.  So
`cf_universal_total_modulus`: every real `≥ 1` carries a free total ∅-axiom modulus
`N(m,k) = k+2` through its own continued fraction.  This is
`phi_total_modulus_via_const` with the Fibonacci sequence replaced by an arbitrary
partial-quotient sequence — the algebraic-φ proof of completion generalised to the whole
real line.  (Shift-invariance reduces every real to a `≥ 1` representative, so the
hypothesis costs no generality.)

The continued fraction is the expansion engine at its terminus: a distinction (the
floor) leaves a unit residue (`cf_det_sq`), and that residue is the next operand
(`x ↦ 1/(x − ⌊x⌋)`), re-entering the same distinction one scale down — a self-similar
chain, gapless because the step is the indivisible unit `W = ±1` and the
Fibonacci-growing denominator shrinks the residue faster than it accrues, with no
exterior slot to leave empty.

### `CrossDetSmall` reads the representation, not the real (`PresentationDependence`)

The smallness condition is a *sufficient* test on a num/den presentation `a_i/d_i`, and
it is genuinely a fact about the **presentation**, not the number.  The real itself —
the decidable cut — is invariant under a common rescaling `(a, d) ↦ (c·a, c·d)`
(`rcut_rescale`: the cut cancels the factor `c`).  But the cross-determinant scales by
`c²` against a denominator scaling by `c` (`crossdet_rescale`), so the smallness
condition is strictly harder for `c ≥ 2`.  Concretely
(`crossDetSmall_is_presentation_dependent`): e's standard convergents
`eulerNum/eulerDen` satisfy `CrossDetSmall` (the `W = d` rung), but the `×2`
representation `2·eulerNum / 2·eulerDen` — *the same real* — carries cross-determinant
`4·eulerDen` and fails `CrossDetSmall` already at `i = 1` (`10 ≤ 8`).  So whether the
bridge applies is presentation-relative; the cut is the rescaling-invariant content.
This is the "deficiency of the presentation, not of the real" reading
(`holonomic_modulus.md`) made into a theorem.

### The intensional reduction (`IntensionalCompletability`, `ScalingOrbit`)

Because the bridge reads the presentation, completability splits into a presentation-
relative *test* and a presentation-invariant *truth*.  Rescaling only ever *loses* the
bridge — `CrossDetSmall (c²·W) (c·d) → CrossDetSmall W d` for `c ≥ 1`
(`crossDetSmall_rescale_antitone`) — so the gcd-reduced presentation is its canonical
home.  The completion itself, by contrast, transfers verbatim across the orbit: a total
modulus for `a/d` is one for `(c·a)/(c·d)` (`modulus_rescale_invariant`, via
`rcut_rescale`).  `completability_is_intensional` bundles the split: the test is
presentation-relative, the truth is not.  The rescaling presentations of one cut form a
monoid-action orbit (`scaleBy_one`/`scaleBy_comp`) inside that one cut
(`scaleBy_preserves_cut`), along which `CrossDetSmall` is antitone
(`orbit_free_implies_base_free`) with a unique reduced base (`reduced_scaling_trivial`):
the rung is read at the canonical reduced presentation (`scaling_orbit_structure`).  So
"does this real complete?" is *intensional* — a fact about the cut — while the W-vs-d
readout is an *extensional* probe of a chosen presentation.

### Closure of the finite-coordinate class (`DepthClosure`)

The trajectories of *finite* coordinate form a class closed under the tower's
operations, by the linearity of the difference operator:

  - `diff` is additive on monotone sequences, so every iterated difference distributes
    (`diffN_add`): the finite-difference-depth class is closed under `+`
    (`finDiffDepth_add`, the floor of a sum reached by the deeper summand);
  - a sum of exponents is a **product** of values — `c^{e₁+e₂} = c^{e₁}·c^{e₂}`
    (`expSeq_mul`) — so closure of exponents under `+` is closure of the exponential
    values under `×` (`value_mul_closed`); φ, e, and any finite-coordinate real
    generate a family under multiplication, for free;
  - the **exponent axis** lifts a finite difference depth to a finite ratio depth one
    tier up (`value_finRatio_of_finDiff`, value-height = 1 + exponent-height), and this
    closure **breaks exactly at the exponential** — `twoPow = 2^n` is not of finite
    difference depth (`twoPow_not_finDiff`) and its value `2^{2^n}` has no finite ratio
    depth (`exp_axis_breaks`).

`rate_carrying_tower_closure` bundles the four.  This is holonomic closure made
internal to the resolution tower, with the boundary the same `2^{2^n}` of the overtake
layer.

### The tower is a coordinate system (`DepthCoordGenerator`)

The tower is also a generator: place a coordinate and read off a sequence sitting at
it.  The degree-`d` binomial column `genExp d = (n ↦ binom n d)` realizes
difference-depth `d` for every `d` (`genExp_realizes`, `= binomCol_polyDepth`); its
exponentiation `genValue c d = c^{binom · d}` has finite ratio-depth `d`
(`genValue_floors`); and the `ω^r` tower `expTower c r` realizes every exponential
height, each strictly dominating the whole lower tower (`coord_layer_dominates`) by the
generator recursion `expTower c (r+1) = c^{expTower c r}` (`expTower_succ`).
`tower_is_coordinate_system` bundles these — the `ω^ω` ladder is populated level by
level by explicit sequences.  The finite-coordinate ones are exactly the rate-carrying
class that carries a free modulus (φ, e, the Liouville constant), so each generated
finite coordinate is an actually-completing real.

### The deep tie: the tower has no top (`DepthCeilingResidue`)

Naming "the act of raising the ceiling" is a diagonalisation (`diag_not_in_seq`) — the
same Cantor self-cover (`cantor_general`) that makes the residue of pointing
(`ceiling_reference_leaves_residue`, `ceiling_residue_is_pointing_residue`).  The real-
number tower has no top because pointing has no exterior; its top-lessness **is** the
residue read at the scale of divergence-complexity.  The boundary of constructive
completeness and the surplus of pointing are one object.

### The discriminant trichotomy of the reference forms (`FloorReferenceForm`, `EisensteinSignature`, `ParabolicSignature`)

The cross-determinant's rungs carry a quadratic *reference form*, and the forms split by
the sign of their discriminant — which is the shape of the reference (line / cusp /
curve):

  - **disc `+5`, golden `m²−mk−k²`** — the det-one floor's conserved invariant
    (`ProbeTwistConic.Q_preserved`).  It is *indefinite* (`golden_indefinite`: `Q(2,1)=+1`,
    `Q(1,1)=−1`), so its level sets are unbounded hyperbolae — an infinite convergent
    **line** (`ℤ[φ]`'s units `φⁿ`), the completing bottom (`floor_reference_is_indefinite`);
  - **disc `0`, parabolic `(m−k)²`** — *semi-definite* (`parab_nonneg`) with a non-origin
    zero (`parab_nonorigin_zero`): vanishing on a line, the degenerate **cusp** (the
    rational direction);
  - **disc `−3`, Eisenstein `a²−ab+b²`** — *positive-definite* (`eisForm_nonneg`, via the
    bivariate `Int` reflection prover `PolyInt2`), zero only at the origin: bounded
    elliptic level sets, a **curve** / torus (the `ℤ[ω]` lattice, `|μ| = 6 = NS·NT`, the
    det-one floor = the 6-unit group `eisenstein_det_one_floor`).

`signature_trichotomy` bundles the three.  Indefinite ⟹ line ⟹ completes; definite ⟹
curve; the parabolic cusp is the boundary, the rational direction — the residue in the
geodesic coding (the one cusp of `ℍ/SL₂(ℤ)`), tying the trichotomy back to the
top-lessness above.  The rung floor of a completing real is thus not just a sign but a
**McKay rung**: disc `−3` = `μ₆ = C₆` (the A-family), disc `+5` = the E₈ endpoint below.

### The five-floor unification: the floor is the E₈ endpoint (`FiveFloorUnification`)

The det-one floor's matrix `P = [[2,1],[1,1]]` carries disc `5 = NS+NT`, and that single
`5` is where the completability bottom meets the framework's exceptional ceiling.
`P mod 5` is the order-`10` element of `SL(2,𝔽₅) ≅ 2I`, the binary icosahedral group —
the **E₈** endpoint of the meta-CD-tower's McKay `A–D–E` ladder (`MobiusPIcosian`,
`10 = NT·(NS+NT)`).  `five_floor_unifies` bundles the two readings of the same `P`: the
completability floor (indefinite golden form ⟹ completing line) and the E₈ icosian
endpoint (`P mod 5` order 10).  So the **bottom** of the real-number completability tower
and the **top** of the exceptional-algebra ladder are one atomic object, met at
`5 = NS+NT`.  This is a *convergence*, not a derivation (neither arc reduces to the
other); it is the operational content of "no exterior" (`05_no_exterior` §5.6 — the same
object recurring across unrelated-looking domains).  The completability tower's no-top
loop (the residue) is pinned, at its floor, to the McKay E₈ rung.

### One statement

`tower_native_completeness_program` (`TowerNativeCompleteness`) is the single ∅-axiom
conjunction of the boundary, the Liouville adjudication, the closure, the generator,
and the residue tie.  In one line: **completability reduces to a comparison of two
growth-axes inside the tower, the tower has no top, and its top-lessness is the
residue — so the real line's completability is a stratified, self-generating,
foundation-touching structure, not a yes/no fact about individual reals.**

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `completability_boundary` | `CrossDetOvertake` | over `2^i`: constant `W` free, double-exp `W` breaks |
| `crossdet_small_total_modulus` | `CrossDetOvertake` | `CrossDetSmall` ⟹ total modulus `N=k+2` |
| `liou_cross_det` | `LiouvilleModulus` | the Liouville cross-determinant equals its denominator |
| `liouville_total_modulus` | `LiouvilleModulus` | the Liouville constant carries a free modulus |
| `liouville_W_eq_denom_coordinate` | `LiouvilleModulus` | `W` and `d` share the factorial-tier coordinate, `d` dominates |
| `finDiffDepth_add` / `value_mul_closed` | `DepthClosure` | finite-coordinate class closed under `+` / `×` |
| `value_finRatio_of_finDiff` / `exp_axis_breaks` | `DepthClosure` | exponent-axis closure, breaking at `2^{2^n}` |
| `cf_det_sq` | `ContinuedFractionFloor` | every real's continued-fraction cross-determinant is a unit (`W² = 1`) |
| `cfDet2_even` | `ContinuedFractionFloor` | the even two-step cross-determinant is the partial quotient `a_{2n+2}` |
| `cf_universal_total_modulus` | `ContinuedFractionModulus` | every real `≥ 1` completes through its continued fraction |
| `tower_is_coordinate_system` | `DepthCoordGenerator` | every tower coordinate realized by an explicit sequence |
| `ceiling_residue_is_pointing_residue` | `DepthCeilingResidue` | the tower's top-lessness is the residue of pointing |
| `tower_native_completeness_program` | `TowerNativeCompleteness` | the five, bundled |
| `completability_is_intensional` | `IntensionalCompletability` | the test is presentation-relative, the completion presentation-invariant |
| `scaling_orbit_structure` | `ScalingOrbit` | the rescaling orbit is one cut; the reduced base is canonical |
| `floor_reference_is_indefinite` | `FloorReferenceForm` | the det-one floor's golden form is indefinite (the completing line) |
| `signature_trichotomy` | `ParabolicSignature` | reference forms split line / cusp / curve by disc sign |
| `eisenstein_det_one_floor` | `EisensteinSignature` | the Eisenstein det-one floor is the 6-unit group `= NS·NT` |
| `five_floor_unifies` | `FiveFloorUnification` | the completability floor `P` = the McKay E₈ endpoint mod `5` |

## Open frontier

Internal to the program: closed ∅-axiom — the overtake boundary, the Liouville
adjudication, closure of the finite-coordinate class under `×` and the exponent axis, a
generator surjective onto the tower coordinates, the universal det-one floor with its
continued-fraction completion for every real, the residue tie, the intensional-reduction
split, the discriminant trichotomy, and the five-floor unification.  The binary boundary
itself is refined into a two-axis ordinal engine — `(height, rate)` lex grade plus the
rescaling gauge — in `refined_completability_engine.md`, and the unit-order/divergence-depth
classification in `spiral_coordinate_classification.md`.

The genuinely open questions: whether every completing real admits a *rate-carrying
re-presentation* (the converse of the bridge; π via Wallis is the obstruction, so this
reframes the π frontier as an existential, not a property of π); the **cross-presentation
rung floor** — the rung over *all* presentations of a cut (the rescaling sub-family is
closed in `ScalingOrbit`; the cross-presentation invariant subsumes the re-presentation
question); and the standing **fast-π representation** meeting the rate criterion
(`holonomic_modulus.md` frontier).  Outside the tower-native frame and not claimed: full
num/den closure under `+`/`×` for arbitrary rate-carrying presentations (the classical
holonomic-closure theorem), and a fully generic ordinal-indexed `coord → cut` map for
every `ω^r` position at once.

## How to verify

```bash
cd lean
lake build E213.Lib.Math
cd ..
for M in \
  E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake \
  E213.Lib.Math.NumberSystems.Real213.LiouvilleModulus \
  E213.Lib.Math.NumberSystems.Real213.ContinuedFractionFloor \
  E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus \
  E213.Lib.Math.NumberSystems.Real213.IntensionalCompletability \
  E213.Lib.Math.NumberSystems.Real213.ScalingOrbit \
  E213.Lib.Math.NumberSystems.Real213.FloorReferenceForm \
  E213.Lib.Math.Analysis.Cauchy.DepthClosure \
  E213.Lib.Math.Analysis.Cauchy.DepthCoordGenerator \
  E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSignature \
  E213.Lib.Math.Algebra.CayleyDickson.Integer.ParabolicSignature \
  E213.Lib.Math.FiveFloorUnification \
  E213.Lib.Math.NumberSystems.Real213.TowerNativeCompleteness ; do
    python3 tools/scan_axioms.py $M
done
```
Each module reports `N pure / 0 dirty`.
