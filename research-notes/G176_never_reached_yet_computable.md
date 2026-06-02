# G176 — how a never-reached number yields `3.141592…`: convergence vs equality, computable vs holonomic

**Tier 1 (volatile, conceptual).**  Answers a question (Mingu, 2026-06) at the heart of the
π-non-holonomicity arc: *if π is "never reached" (outside every pointing's image,
`object1_not_surjective`), how do the digits `3.141592…` come out?*  Anchored throughout to
∅-axiom theorems already in the repo.

## The one-line resolution

`3.141592…` is **not π** — it is a **pointing** (the decimal Lens).  Every finite truncation is
a *rational* `≠ π`; the trailing "`…`" is not a possessed object but a **rule** to continue.
"Getting the digits" = running a pointing that emits rationals **converging to** π, the
unreached limit/residue.  No contradiction: the pointing-outputs get arbitrarily *close*
(convergence) but equal π at no step (the residue is in the closure, not the image).

## Two distinctions that dissolve the paradox

### 1. Convergence (pointing-toward) ≠ equality (reaching)

A strictly monotone bounded rational sequence can approach a limit it never equals.  This is a
**theorem in the repo**, for the golden archetype:

  - `Real213/FibCassiniNat.fib_convergent_below_phi` — every Fibonacci convergent lies
    **strictly below** φ (∀ n): no term *equals* φ.
  - `Real213/PhiCauchyLimit.phiCauchy_limit_eq_phiCut` — the same convergents **converge to** φ
    (the cut): arbitrary precision.

So φ is *approached from below by computable rationals, equalling none* — the exact shape of
"never reached, yet its value is produced to any precision."  The continued-fraction analog for
*every* real is the unit cross-determinant `ContinuedFractionFloor.cf_det_sq` (`W² = 1`): the
convergents bracket the real with gap `1/(qₙqₙ₊₁) → 0`, while the real (if irrational) equals no
convergent.  The residue is reached by none, bracketed by all
(`FlatOntologyClosure.object1_not_surjective`).

### 2. Non-holonomic ≠ non-computable

The marathon proved two sequences **non-holonomic** ∅-axiom — yet both are **manifestly
computable**:

  - `Cauchy/NonHolonomicWitness.superFact_nonHolonomic` — `(n!)ⁿ` (any term is computed
    directly).
  - `Cauchy/ZeroRunNonHolonomicWitness.chi_nonHolonomic` — the powers-of-two indicator, with
    `chi_values : ∀ n, χ n = 0 ∨ χ n = 1` (every value a decidable `0`/`1`, produced by
    `isPow2`).

**Non-holonomic = "no finite recurrence generates it", not "uncomputable".**  The same holds for
π: its *continued-fraction pointing* is conjectured to have no finite recurrence
(non-holonomic), but *other* pointings — Wallis (`Cauchy/Wallis`, finite-depth via
`DepthPiQuartic.liftK4_piRatio`), Machin arctan series, the BBP digit formula — compute the
digits fine.  "We get `3.14159`" through a **computable pointing that is not the CF**.  This is
the load-bearing thesis already promoted to `theory/math/analysis/phi_pi_poles.md`:
**holonomicity is a property of the pointing, not of the real**
(`Real213/PresentationDependence.crossDetSmall_is_presentation_dependent`, `rcut_rescale`).

## Why there is no tension with "absolutely never reached"

| "absolutely never reached" | "`3.141592…` comes out" |
|---|---|
| no *finite* pointing-output **equals** π | pointing-outputs get arbitrarily **close** |
| `object1_not_surjective`: π ∉ image of any view | π ∈ *closure*: a computable pointing converges |
| the CF pointing has no finite recurrence | a *different* pointing (BBP/Wallis/arctan) is algorithmic |

The "`…`" is precisely the mark of *approaching without closing* — the residue's signature
inside the decimal Lens.

## The deepest layer

We never manipulate π directly — only **pointings** (digits, CF, series).  Every true statement
about π (`3 < π < 4`, transcendence, `π/4 = Σ…`) is proved *through* pointings; the residue is
what they all converge to / agree on.  **"Having π" = having a coherent family of pointings**,
not possessing the residue.  The residue is *reached by none, pointed to by all* — and that
suffices for all of mathematics, because all of it is done in the pointings.

## What then makes π special, if "pointing, not the number" is generic?

The pointing/residue distinction is **generic** — true of every irrational (and rationals are
pointings too).  So it is *not* π's specialness.  That lives on two axes the marathon measured.

**Axis 1 — structure of the canonical (CF) pointing.**  Order the reals by how structured their
regular continued fraction is: rationals (finite/periodic) ; **quadratic irrationals**
`√2,√3,√5,φ` (eventually *periodic* CF — tier 0, `periodic_quasipoly`, Lagrange — *proven*
ordered) ; **e, tan 1** (*quasi-periodic*/Hurwitzian CF — tier 1, `e_cf_quasipoly` — *proven*
ordered) ; **π** (no known pattern — conjectured non-holonomic, tier 3 — *open*).  So `√2,√3,√5`
are **not like π at all** (their CF is periodic); e is structured too.  π is the disordered one
*among this list*.

  - *Precision:* π's CF-disorder is **not unique** — degree-≥3 algebraics (`∛2`) and almost
    every real share it (Gauss–Kuzmin genericity).  The *special* numbers are the **ordered
    exceptions** (quadratic + e-family, measure zero).  π is the **generic/typical** one; that
    is *why* it is hard — proving genericity is hard, proving structure is comparatively easy
    (which is exactly why the marathon closed `√2,√5,e` and left π open).

**Axis 2 — role/origin (where π is genuinely unique).**  π is the **rotation/period/circle
constant** (`e^{2πi}=1`, every U(1)/Fourier/rotation) — the continuous-symmetry image of the
residue (elliptic face, `phi_pi_poles.md`, `HyperbolicEllipticTrace`).  `√2,√3,√5` are
**quadratic-field units/discriminants** (algebraic axis, hyperbolic face); `e` is the
**exponential self-rate**; `φ` the **self-reference fixed point** (`Mobius213`).  Here π is the
odd one out, uniquely tied to the circle.

**One line:** π is special not for *how it is written* (infinite decimal — generic) nor even for
its *CF-disorder* (shared with `∛2`, in fact *generic*), but for *what it is* — the rotation
constant — and for the paradox that a constant we care about so deeply is statistically
*ordinary* in its CF.  `√2,√3,√5,e` are the *atypically ordered* rarities; π is the *typically
disordered* rotation constant.

## ∅-axiom anchors (all already proven)

  - `Real213/FibCassiniNat.fib_convergent_below_phi`, `Real213/PhiCauchyLimit.phiCauchy_limit_eq_phiCut`
    — approaches (converges) but never equals (strictly below), for φ.
  - `Real213/ContinuedFractionFloor.cf_det_sq` — the det-1 bracket, every real.
  - `Cauchy/NonHolonomicWitness.superFact_nonHolonomic`,
    `Cauchy/ZeroRunNonHolonomicWitness.{chi_nonHolonomic, chi_values}` — non-holonomic yet
    computable (two orthogonal axes).
  - `Real213/PresentationDependence.crossDetSmall_is_presentation_dependent`, `rcut_rescale` —
    holonomicity is a property of the pointing, the real is invariant.
  - `Lens/FlatOntologyClosure.object1_not_surjective` — the residue is outside every view's
    image.
