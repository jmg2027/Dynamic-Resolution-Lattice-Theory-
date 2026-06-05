# Frontier — the shapeLens single-ℕ fork as an independent route to d = 5

**Status**: open conjecture (Mingu Jeong, 2026-06-05; this is the originator's
insight, sharper than the visual-explosion observation).  Below DRLT Validation
Standard.  Artifact: `research-notes/geometric/shapelens_fork.{py,png}`.

## The observation (originator)

The point/line generation rule is itself a Lens (the `shapeLens`).  In this Lens the
canonical (synchronous, choice-free-per-cycle) process produces point counts
`2, 3, 5, 12, 68, 2280, …` with new-points-per-cycle ("growth axes") `1, 2, 7, 56, …`.
A *single natural-number cycle* can be spoken of only while there is one growth
axis (one new point) — i.e. only the step `2 → 3`.  At 3 the process is forced to
add `+2` (two independent points at once), past which the cycle is not a single ℕ
(the no-global-cycle / foliation finding).  **The threshold is exactly 5.**

## Why it is one event, at d = 5

The canonical sequence `2, 3, 5, 12, 68` **skips 4**.  The `+2` jump `3 → 5` is
simultaneously:
- **single-ℕ ends**: ℕ-successor (`+1`, the count-Lens unit) generates only `2→3`;
  at 3 the lens forces `+2`.  ℕ is the 1-axis (1-D) shadow; the lens is
  intrinsically multi-axis past here.
- **dimension is born**: 1 axis = 1-D = ℕ-orderable line; ≥2 simultaneous axes =
  a poset/lattice, no single ℕ index.
- **planarity ends**: the single-axis regime stays planar (`K_3`); the `+2` jump
  leaps the planar tetrahedron `K_4` and lands on the first non-planar `K_5`.
- **atomicity**: `d = N_S + N_T = 5`.

So `single-ℕ ends = planarity ends (K_4 skipped → K_5) = d = 5`, all the one `3→5`
fork — not a coincidence of small numbers but a single structural event.

## The conjecture

`d = 5` has an independent characterization *internal to the shapeLens*:
> `d` is the count of the first complete graph the canonical generation reaches by
> an irreducibly multi-axis (non-linear, ≥2 simultaneous) step — equivalently the
> first `K_n` it reaches that is non-planar (it skips `K_4`), equivalently the first
> 4-simplex skeleton.

This would be a route to atomicity parallel to `Theory/Atomicity/PairForcing`
(§4.3, arity+atomicity).  It resonates with no-exterior (§5.1): the fork is where
the structure stops being 1-D / flattenable / linearly orderable — where it gains
an irreducible dimensionality with no lower-dimensional ambient frame.

## Deep-research verdict (2026-06-05, `shapelens_functor.md`)

The "are they the same forcing in two readings?" question below is now answered:
**no.**  The arithmetic forcing (`Five`/`PairForcing`/`ArityForcing`) fixes
`(N_S,N_T)=(2,3)` from coprimality + parity + unique-alive-decomposition count,
then *derives* `5 = 2+3`; it never mentions graphs, planarity, or posets.  The
shapeLens fork fixes `5` *directly* as a structural threshold (first width-≥2
antichain / first non-planar `K_n`, skipping `K_4`) **without referencing
`(2,3)`**.  They share no premise — two **independent** routes that **coincide on
the value 5**.  A *proof* that the fork-characterization implies the arithmetic
atomic shape would be a genuine new theorem, not a re-reading; claiming "same
forcing" is unsupported.

Quantitative additions: the canonical orbit grows doubly-exponentially,
`n_{k+1} = C(n_k+1,2) − C(n_{k−1},2)`, `n_k ~ 2·c^(2^k)` with `c ≈ 1.24602083`;
the skip of `K_4` is **forced** (reaching 4 needs a desynchronised one-at-a-time
path = a different Lens).  Genus: `γ(K_n)` jumps `0→1` at exactly `n=5`
(Ringel–Youngs `⌈(n−3)(n−4)/12⌉`).

## Open

- Make "single-ℕ cycle" / "growth axis" precise as a property of the confluent
  generation (the configuration lattice of `ConfigLatticeCount`); show the fork
  (first antichain of width ≥2) is at the `3→5` step.  **No Lean witness yet** —
  the fork antichain is the conjecture's central object and is not formalized
  (only the count `I(V,s)` is).  This is "Target B" of `shapelens_functor.md`
  (medium effort: a small decidable antichain/poset layer + `decide` over the
  first cycles, proving `maxAntichainWidth(P(V,1))=1`, `…(P(V,2))≥2`).
- Bridge the two routes: derive the arithmetic atomic shape *from* the
  fork-characterization (or vice versa).  This is the genuine open theorem — they
  are known to be independent and to agree on 5, not known to imply each other.
- Whether the skip of `K_4` (the canonical process never visits the planar
  tetrahedron) is the crux, and whether other `(N_S,N_T)` would skip differently.
