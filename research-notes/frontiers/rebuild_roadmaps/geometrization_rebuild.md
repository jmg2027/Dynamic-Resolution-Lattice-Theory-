# Genuine Geometrization rebuild (post-deletion of the bogus layer)

Companion to `research-notes/frontiers/genuine_hodge_rebuild.md` — same
honesty contract: state the real theorem, give the smallest genuinely
non-trivial reachable result on an *existing* seam, mark the rest open,
and never claim the conjecture is proven.

## 1. What was deleted & why bogus

The "Geometrization-in-213" headline layer welded Thurston's name to
arithmetic that has nothing to do with 3-manifolds.  The fake content
was of the shape:

  · `chartVisibleAxes := NS + NT − 1` — a hardcoded `5 − 1 = 4`
    presented as "the dimension geometrization decomposes", which is
    just `d − 1` on the simplex counts, *not* a manifold dimension.
  · a hardcoded `8` ("the eight geometries") read off `NS² − 1`, the
    octet integer — the count `8` coinciding numerically with Thurston's
    eight geometries, with **no Lie-group enumeration** behind it.
  · the "decomposition" proofs were `decide` on these literals — there
    was no closed 3-manifold, no prime/JSJ cut, no homogeneous geometry.

A famous name welded to `d−1` and a count-coincidence is exactly the
stereotype-match the audit removes.

## 2. The genuine content

**Thurston's Geometrization conjecture** (proven by Perelman, 2003):
every closed orientable 3-manifold `M` admits a canonical two-stage
decomposition —

  (a) **prime decomposition** (Kneser–Milnor): `M = P₁ # … # Pₖ`, a
      connected sum of prime pieces, unique up to order;
  (b) **JSJ decomposition** (Jaco–Shalen–Johannson): each prime piece is
      cut along a canonical minimal family of incompressible tori into
      pieces that are either Seifert-fibred or atoroidal;

such that each resulting piece carries a complete locally homogeneous
Riemannian metric modelled on **exactly one of the 8 Thurston
geometries**: `S³, E³, H³, S²×ℝ, H²×ℝ, SL₂(ℝ)~, Nil, Sol`.  The "8" is a
*classification theorem*: the maximal simply-connected homogeneous
3-dimensional model geometries `(X, Isom(X))` with a compact-quotient
group are exactly these eight — a real enumeration of Lie groups acting
transitively on 3-dim spaces, **not** any integer that happens to equal 8.

## 3. The 213-native obstruction (brutally honest)

The current substrate has **no 3-manifold notion at all**. Concretely:

  · No smooth manifold, no `π₁`, no incompressible surface, no
    homogeneous space `G/H`, no Lie group, no Riemannian metric in the
    ∅-axiom `Nat`/`Int`/graph/`Real213` substrate.
  · The only geometry library is `DiscreteCurvature/` — combinatorial
    curvature on *finite graphs* (1-complexes) plus a 2D-conformal smooth
    Liouville route (`ConformalCurvature.lean`). A finite graph is not a
    3-manifold; its `b₁` is a cycle-rank, not a fundamental group.
  · The "8" coincidence (octet `= NS²−1`) is genuinely about `SU(3)`
    (`OctetModule.lean`), which is unrelated to the eight model
    geometries. Any bridge between them would itself be a
    stereotype-match and must not be attempted.

So Geometrization is **not reachable** in the current substrate. What is
reachable is the *discrete-curvature decomposition* analogue, on graphs,
honestly labelled as such.

## 4. Staged plan

**Stage 1 — DONE / near-done: discrete surgery decomposition on graphs.**
The genuine foothold is `DiscreteCurvature/DiscreteSurgery.lean`, which
already proves the graph-category shadow of the decompose-and-classify
arc:
  · `gauss_bonnet_general` — for any finite graph, handshake ⟹ `Σκ = 2χ`.
  · `surgery_euler` / `surgery_curvature` — cutting one neck edge raises
    `χ` by exactly 1, total curvature by `+2`.
  · `surgery_dichotomy` — a connected state is **round** (tree, `b₁=0`,
    no neck) XOR **neck-bearing** (`b₁ ≥ 1`).
  · `surgery_terminates` + `surgery_count` — exactly `b₁` surgeries reach
    the round cap (finite extinction on the `b₁` ledger).
  · `k32_surgery` — the concrete `K_{3,2}` instance (`b₁: 8 → 5`, via
    `RicciFlow.lean`).
This is an honest "decompose a graph into round pieces along necks, in
finitely many canonical cuts" — the *combinatorial* analogue of cut-along-
necks, with a Gauss–Bonnet ledger. **It is NOT geometrization.** Stage 1
work = state this explicitly as a graph-surgery decomposition theorem,
decoupled from any "3-manifold" or "8 geometries" framing.

**Stage 2 — the homogeneous-model trichotomy (smooth ODE shadow).**
`RicciHomogeneous.lean` proves the Einstein trichotomy `λ>0` finite
extinction / `λ=0` stationary / `λ<0` divergence on the size ODE, and
`RicciSphereFlow.lean` the round-`Sⁿ` extinction. This is the
qualitative behaviour the *sign of curvature* forces — a genuine fragment
of "geometries are distinguished by their curvature sign". Stage 2 =
enumerate, honestly, *which* model behaviours are captured (positive /
flat / negative Einstein = 3 of the 8 by sectional-curvature sign) and
which require off-substrate structure.

**Stage 3 — a 213-native homogeneous space.** The first genuinely new
object needed: a `G/H` with a transitive group action, even a finite or
combinatorial surrogate. Without this there is no "model geometry" to
enumerate. This is open and may require a Lie-group / smooth-manifold
substrate that does not exist yet.

**Stage 4 — research arc (may never be reachable here).** A 213-native
closed-3-manifold notion (e.g. a simplicial 3-pseudomanifold with a
`π₁`), a prime/JSJ analogue (cut along incompressible 2-spheres / tori),
and the eight-geometry classification as a real transitive-action
enumeration. Honestly: this is a from-scratch rebuild of differential
topology in the substrate; it is a long arc, possibly unreachable.

## 5. Honest scope

Nothing here proves, or approximates, the Geometrization conjecture.
  · `surgery_*`, `gauss_bonnet_general` are **proven ∅-axiom theorems
    about finite graphs** — genuine, but in the graph category, not the
    manifold category. They are *analogues*, named as analogues.
  · `RicciHomogeneous.einstein_trichotomy` / `RicciSphereFlow` are proven
    statements about a **size ODE** under an *input* Einstein constant
    (the rate is geometric input, not derived — see the file's own §0).
  · The eight Thurston geometries, prime/JSJ decomposition, and the
    Perelman theorem are **classical mathematics, entirely open in this
    substrate** (no manifold object exists). No file may cite any 213
    result as "Geometrization" or as "the eight geometries".

## 6. Cross-references (genuine kept seams)

  · `lean/E213/Lib/Math/Geometry/DiscreteCurvature/DiscreteSurgery.lean`
    (Stage 1 — graph surgery / Gauss–Bonnet ledger / termination)
  · `lean/E213/Lib/Math/Geometry/DiscreteCurvature/RicciHomogeneous.lean`
    + `RicciSphereFlow.lean` (Stage 2 — Einstein trichotomy, ODE shadow)
  · `lean/E213/Lib/Math/Geometry/DiscreteCurvature/RicciFlowDiscrete.lean`
    + `RicciFlow.lean` (discrete Ricci flow on `K_{3,2}`, `b₁: 8→5`)
  · `lean/E213/Lib/Math/Geometry/DiscreteCurvature/DiscreteRicci.lean` /
    `OllivierRicci.lean` / `BakryEmery.lean` (curvature definitions,
    sign trichotomy — the discrete-curvature foundation)
  · `lean/E213/Lib/Math/Geometry/DiscreteCurvature/INDEX.md` (sub-tree map)
  · `theory/math/geometry/discrete_curvature.md` (narrative)
