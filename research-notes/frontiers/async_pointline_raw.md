# The asynchronous point–line system ≅ Raw — staging as foliation Lens, layer scales

**Origin.**  `seed/ORIGIN_RAW.md` (originator: Mingu Jeong) — the Raw
axiom rebuilt from "difference" alone, then read as an asynchronous
event system with two pure event kinds (contrast: Pair → Line;
differentiation: Line → Point).  Closing question (§10 there): *if
strata are assigned above level 2, which number scale (or scales) is
appropriate?*  This note records the analysis and the Lean targets.

## 1. The system is Raw

The limit object of the point–line process is the direction-free,
no-self-pair magma on two atoms — exactly `Raw`
(`lean/E213/Theory/Raw/Core.lean`): points = Raw terms, the line
between `x` and `y` = the pair caught, its resolving point =
`Raw.slash x y (h : x ≠ y)`.  "Unconnected pairs only" = the
no-duplicate + no-self-pair constraints; "no back-and-forth" = the
slash-symmetry canonical subtype.  The two event kinds are **one
constructor** read under a point/line Lens: the line is the
difference noticed, the point is the same difference reified as an
operand for further difference — splitting `slash` into two halves is
itself a Lens choice (anticipated in the origin dialogue: the
"difference-object Lens, `(ab) ↦ c`").

## 2. Where lockstep staging is canonical — the forced segment

- **Through level 1 the run is deterministic**: from `{a, b}` the only
  enabled event is the line `a–b`, then its resolution `a/b`.  One
  possible history.
- **Level 2 is canonical up to swap**: the enabled set is exactly the
  two `a↔b`-symmetric contrasts `(a, a/b)`, `(b, a/b)`; any
  interleaving yields the same snapshot modulo the swap involution
  (`Raw.swap_depth` / `Raw.swap_leaves` invariance,
  `Theory/Raw/Levels.lean`).  The level-≤2 population is a closed
  theorem: **`Raw.level2_total_card = 5`** (`Levels.lean`) — 2 atoms +
  3 composites, the atomicity split `(NS, NT) = (3, 2)` at `d = 5`.
- **From level 3 staging becomes a convention**: every new pair
  involves a branching-born element; sibling-pairing and
  parent-pairing bookkeeping choices appear; asynchronous snapshots
  diverge beyond the swap symmetry (e.g. a depth-3 object can exist
  while a depth-2 object does not).  "Stage number" and "event count"
  decouple; only per-object structure survives interleaving.

Under the strict lockstep foliation, stage = depth at every level —
the Nat staging does not *contradict* anything; it is one linear
extension among many.  What dies above level 2 is its *canonicity*:
no run forces it, so adopting it is importing a global clock
(`seed/AXIOM/05_no_exterior.md` §5.7 — no external time axis).

## 3. The layer-scale answer — three strata

**(a) Per-object stratum: ℕ, but as a fold-Lens.**  An object's level
is a function of the object (its own history tree), not of the run —
interleaving-invariant by construction.  Two canonical folds exist as
theorems (`Theory/Raw/Levels.lean`):
`Raw.fold_eq_depth` — depth = `fold 0 0 (fun a b => 1 + max a b)`
(max-plus reading); `Raw.fold_eq_leaves` — leaves = `fold 1 1 (·+·)`
(additive reading); related by `Raw.depth_lt_leaves`.  "Level" is a
family of fold-Lenses; depth is one member.

**(b) Per-layer width: iterated exponential.**  Population with depth
≤ n, `T(n)`: composites of depth ≤ n+1 = unordered pairs of distinct
elements of depth ≤ n, so

```
T(n+1) = 2 + C(T(n), 2)
T:  2, 3, 5, 12, 68, 2280, 2598062, …    (T(n+1) ≈ T(n)²/2)
```

`log T` doubles per level — the same `d^(d^n)` shape as the parametric
`configCountD` (`Lib/Math/Cohomology/Fractal/ConfigCount.lean`).  New-
at-level counts: 2, 1, 2, 7, 56, 2212, ….

**(c) Global stratum: not a number — the causal partial order.**  The
interleaving-invariant grading is the ancestor poset itself; a numeric
staging = a linear extension = a **foliation Lens**.  Events are
monotone and non-conflicting (a line, once drawn, stays; resolution
only adds), so the system is confluent: every fair run converges to
all of Raw; only finite snapshots are foliation-dependent.

**Guard (the N_U lesson, `RERESEARCH_n_u_removal.md`).**  The level-2
boundary is where *forcing ends*, a structural property of the runs —
not a privileged truncation depth, and its population `5` is not a
universe constant.  No level is privileged in (b); the boundary lives
in (c).

## 4. Open items (Lean targets)

- **O1 — the event system, formally.**  A Lean structure for states
  (points = a downset of the ancestor order, lines = pending distinct
  pairs) + the two event steps; theorem: the reachable limit is all of
  `Raw` (confluence / fairness), interleaving-independent.
- **O2 — the forced-segment theorem.**  Deterministic prefix =
  level ≤ 1; level-2 canonicity up to `Raw.swap`; from level 3 two
  runs reach swap-inequivalent snapshots.  This makes "numeric strata
  end at level 2" (origin §9) a theorem rather than an observation.
- **O3 — the width recursion.**  `T : Nat → Nat`,
  `T (n+1) = 2 + choose (T n) 2`, with `T 2 = 5` agreeing with
  `Raw.level2_total_card`, and a double-exponential lower bound
  (`2^(2^n) ≤ …` shape) connecting to `configCountD`.
- **O4 — the two 5s.**  Atomicity forces `(NS, NT, d) = (3, 2, 5)`
  (`Theory/Atomicity/`); the forcing boundary here has population
  5 = 2 + 3 with the same split.  One theorem identifying the two
  (or an honest separation if they differ) — touches
  `G121_dim4_self_pointing_axis` knot M2 (the chart-Lens omitting the
  self-pointing axis: 5 → 4 readout).

## Cross-references

`seed/ORIGIN_RAW.md` (the origin dialogue, verbatim);
`lean/E213/Theory/Raw/{Core,Levels}.lean` (Raw, level-≤2 enumeration,
fold bridges); `seed/AXIOM/05_no_exterior.md` §5.7 (no external time
axis); `Lib/Math/Cohomology/Fractal/ConfigCount.lean` (parametric
double-exponential count); `G121_dim4_self_pointing_axis.md` (the
5 → 4 chart readout, knot M2).
