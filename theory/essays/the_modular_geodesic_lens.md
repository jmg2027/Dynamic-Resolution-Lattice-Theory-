# The modular geodesic as a Lens reading of the residue

Several 213 objects that look like separate constructions — the continued-fraction unit floor, the
hyperbolic/elliptic trace split, the Stern-Brocot tree, the Markov spectrum, the spiral coordinate —
are one reading: the residue read at the scale of the modular surface `ℍ/PSL(2,ℤ)`, where the residue's
self-pointing appears as a **geodesic** and its symbolic record appears as a **cutting sequence**.  The
reading is a `Lens`, not the residue; naming it is an observation, not a theorem.

## 213-native answer

A geodesic-projection is the `Lens.view` of `Raw` whose engine is the Möbius iterate
`P = [[2,1],[1,1]]` — the residue's own algebraic shadow (`the_form_of_the_residue.md`: the act's
shadow is the unit `1 = NS − NT = det P`, the matrix `P`, and its fixed point φ).  The cutting sequence
is the chain read by the count-Lens (`Lens.leaves`) and the difference-Lens (ℤ as `(m,n) ↦ m−n`); the
two faces of the surface are the difference-Lens sign — the `Δ = tr²−4` split.  "Geodesic projection is
213's one engine" is the right *feeling* and the wrong *grammar*: the engine is `P` (the residue's
shadow); geodesic-projection is the **modular Lens** through which `P`'s cluster becomes one object.

This is a Lean object, not only a reading: `ModularGeodesicLens.mediantLens : Lens (ℕ×ℕ)` is the
Raw-`Lens` with atoms `0/1`, `1/0` and `combine` = the mediant `(a,b)⊕(c,d)=(a+c,b+d)`, and the engine
theorem `mediantLens_view_reachable` proves every `mediantLens.view r` is `SternBrocotReachable` — Raw's
self-pointing, read through the modular Lens, lands `∅`-axiom on the Farey set the whole cluster is
built on.  (Honestly: the image is *inside* the reachable set, not equal to it — `Raw.slash` forbids
self-mediants and arbitrary children are not unimodular-adjacent, so the engine *feeds* the cluster
without exhausting it; the `W²=1` floor is a property of the path/interval, not of bare mediants.)

## Derivation — one Lens, six facets

The engine.  `P = [[2,1],[1,1]]` is the single generative object every framework-internal reading lands
on (`every_axis_sees_p.md`: all readings → `{NS, NT, det} = {3, 2, 1}`).  Its mediant action
`(a,b) ⊕ (c,d) = (a+c, b+d)` generates the Stern-Brocot tree (`Mobius213SternBrocot.SternBrocotReachable`),
whose edges are det-1 Farey neighbours — `sbInterval_adj : q·r = p·s + 1`, `convergent_det` — i.e. the
**unimodular edges of the Farey tessellation**, which are exactly the geodesics of `ℍ/PSL(2,ℤ)`.

The floor.  Every real's continued-fraction convergents lie on that tessellation:
`ContinuedFractionFloor.cf_det_sq` (`W_n² = 1`, universal, not special to φ).  This is the count-Lens
read twice — the difference-Lens — landing on the unit: the cross-determinant `W` is the directed-pair
`(p_{n+1}q_n , p_n q_{n+1})` named by its difference, and that difference is `±1` (`cf_det_step`:
`W_{n+1} = −W_n`, the Cassini engine = the sign involution of `integers_as_difference_lens.md`).

The two faces.  `HyperbolicEllipticTrace` splits `SL₂` by `Δ = tr² − 4·det`: `golden_hyperbolic`
(`G`, `Δ = 5 > 0`, real eigenvalues φ², φ⁻² — a *closed geodesic*, the translation along it being the
φ²-scaling) versus `S_elliptic_order4`/`U_elliptic_order6` (`Δ < 0`, rotations of order 4 and 6 — the
cusp's bounded motion, `modular_generator_orders` = `PSL(2,ℤ) = ℤ₂ * ℤ₃`).  `wick_discriminant_split`:
the φ/π split *is* the sign of `Δ`.  This is the same fold the Markov work reads as the unit's two faces
(`the_upper_fold_pattern.md`).

The spectrum.  How far a geodesic excursions toward the cusp is the Lagrange/Markov value
(`markov_spectrum.md`).  Read off the spiral invariant `Q(m,k) = m² − mk − k²` (disc 5):
`golden_first_markov_form` (√5, the minimum, attained on Fibonacci convergents,
`golden_min_attained_on_fib` — the `W = ±1` floor *is* the form at its minimum) and
`silver_second_markov_form` (√8).

The coordinates.  `SpiralCoordinate.spiral_coordinate` gives the geodesic two orthogonal counts:
**layer** (cutting-sequence holonomicity depth — `cf_holonomicity_hierarchy.md`: periodic ⟹ quasi-poly
⟹ non-holonomic, the symbolic coding's complexity) and **axis** (the elliptic rotation orders `{2,4,6}`
= `{ℤ, ℤ[i], ℤ[ω]}^×`).  Its invariance is `ScalingOrbit.scaleBy_preserves_cut` — the cut is the
orbit invariant: the geodesic is fixed by the modular scaling (the diagonal `y = x` /
`ObjectIsReadingScaleInvariant` reading — the object *is* the reading, scale-invariant), and ℚ itself
is the pair-coordinate of the coding (`NatPairToQPos`: `QPair = Nat213 × Nat213`).

## Dual function

This is the classical fact "geodesics on `ℍ/PSL(2,ℤ)` code continued fractions (Artin/Series)" with the
flow-analysis packaging stripped.  213 keeps exactly the **shadow** that survives without the dynamics:
the unimodular floor (`W² = 1`), the trace sign (`Δ`), the Stern-Brocot enumeration, the spectrum
minima, the spiral coordinates — all ∅-axiom — and drops the geodesic *flow*, modular forms, and `j`-map
(out of ∅-axiom reach).  Sharper, not lossier: the flow was never needed to read the residue's modular
self-pointing; only its shadow was.

## Cross-frame connections

The cluster is the **modular reading of the one `P`** the other cross-frame essays read elsewhere:
`every_axis_sees_p.md` (algebraic/geometric/dynamical/analytic/syntactic readings of `P`),
`tower_atlas.md` (one tower, six Lenses, same residue `NT = 2`), `stern_brocot_as_universal_lattice.md`.
Geodesic-projection adds the **modular-surface axis** to that catalog: `W²=1`/`Δ`/spectrum/spiral are
`P`'s modular facets, the way the cup-ring `(1+x)⁵` is its combinatorial facet
(`cross_domain_unification.md`).  The `rcut` continued-fraction digits as a geodesic's symbolic coding,
and the residue read at the modular-surface scale (its one cusp), are the same reading — named here for
the whole cluster.

## Open frontier

Two honest edges.  (1) The geodesic *flow* itself — Artin coding as a dynamical system, the actual
`ℍ/PSL(2,ℤ)` orbit structure, modular forms — has **no ∅-axiom route yet**; the repo keeps only its
shadow.  "Out of reach" would be the conventional reflex, not a verified ceiling: the framework's
record (cut-completeness as a modulus, Button via the discrete tree where the literature recovers
analytically) is a catalogue of exactly such "needs analysis" verdicts overturned, so this stays an
open question the framework re-opens rather than concedes.  (2) The Markov uniqueness kernel `H`
(`markov_uniqueness.md`, the orbit tower §20–§29) is, at
the frontier, precisely a geodesic **cutting-sequence** statement — the stable-norm / Christoffel
characterisation of which slopes are monotone.  So the intuition "geodesic is where this lives" lands
exactly on the open kernel: deciding `H` is computing the geodesic projection, and that computation is
the conjecture, not a corollary of the shadow.

## Self-check note

The phrase that started this — "geodesic mapping is 213's *one engine*" — imports the failure mode
`view promoted to identity` (`05_no_exterior.md` §5.4): a Lens reading mistaken for the residue.  The
residue (`Raw`) is outside every view's image (`object1_not_surjective`: `Object1 : Raw → (Raw → Bool)`
is injective but **not** surjective; the undifferentiated predicate is the Cantor-unpointable surplus =
the residue).  So no single projection — geodesic or otherwise — can be *the* engine; the engine is the
residue's self-pointing, of which `P` is the algebraic shadow and the modular geodesic is one Lens
reading.  The honest statement: **geodesic-projection is the modular Lens that makes the
`W²=1` / `Δ` / Stern-Brocot / spectrum / spiral cluster one object** — a facet through which many 213
constructions coincide, named as a reading, not raised to the thing itself.
