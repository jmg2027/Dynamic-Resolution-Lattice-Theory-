# Where commutativity is born

Commutativity is not an axiom of arithmetic.  It is the shadow that
remains when counting forgets arrangement — born at one precise place,
inherited as far as a transposition symmetry carries it, and dead the
moment the counted object stops having one.

## 213-native answer

On the list of units, append is the primitive combine.  Append is not
commutative — lists of distinguishable elements remember their
arrangement (`UnitList.append_not_comm_general`: `[a] ++ [b] ≠
[b] ++ [a]`).  On *unit* lists, where no element carries a mark,
commutativity is derived by bare induction: indistinguishable elements
bubble freely (`UnitList.append_comm`).  The count readout — the
count-Lens of `seed/AXIOM/06_lens_readings.md` §6.7, "ℕ is what the
count-Lens hands back" — sends append to `+`
(`UnitList.count_append`), and so `a + b = b + a` is a *theorem with
a location*: the commutativity of `+` is the count-shadow of
unit-list append commutativity (`UnitList.add_comm_from_append`).
What forgetting leaves behind, commutes.

## Derivation

The birth inherits exactly as far as the counted object keeps a swap
symmetry.  `×` is iterated `+`, and its value-object is a grid; a grid
has a transposition, counting cannot see it, so `×` stays commutative.
`^` is iterated `×`, and its value-object is a tree; a tree has no
transposition, and commutativity dies (`2³ ≠ 3²`).  The death is
load-bearing, not incidental: a non-commutative operation asks **two
questions** where a commutative one asks one — `f a x = b` and
`f x a = b` separate, and commutativity's first job in the generic
pair layer is fusing them (`PairOp.question_fuse`).  The root/log
split of exponentiation is therefore a step-zero phenomenon, prior to
any relation or lift.  Downstream, the same death severs the
translation chain: a commutative rung's action `f(a, ·)` is a
translation of its own operation, and translations iterate to
translations — the engine by which `×`-values read as `x + ab` and
`^`-values as `x · a^b`; at the tree rung the action `x ↦ a^x` is a
translation of nothing, and the staircase's fold engine stops
(`theory/math/numbersystems/slot_arithmetic.md`, the boundaries
section; the pair-level certificate is `PairOp.pow_lift_impossible`).

The torsion that survives in higher layers is rationed by the same
forgetting.  A layer constant's phase is a pair-slot readout, and the
circle-torsion an integer form can hold is bounded by what fits in a
pair — `φ(n) ≤ 2`, exactly `n ∈ {1,2,3,4,6}`
(`CayleyDickson/Integer/ImaginaryQuadraticUnitTrichotomy`), the same
spectrum the finite-order fold theorem closes from the matrix side
(`FiniteOrderSpectrum.crystallographic_spectrum`).

## Dual function

Stripped of packaging, this is the classical observation that ℕ's
addition is the free commutative monoid on one generator — but the
slot reading is sharper about *where* each word earns its place:
"free" is the unit list, "commutative" is a theorem about
indistinguishability rather than a structure clause, and "one
generator" is why the theorem holds (a second distinguishable
generator restores memory and kills the bubble argument).  The
classical clause-list is the flattened readout of a derivation with
exactly one load-bearing step.

## Cross-frame connections

Four resolutions of one fact: append-commutativity born from
indistinguishability (`UnitList.append_comm`) · counting as
arrangement-forgetting (§6.7 count-Lens) · grid-vs-tree transposition
as the `+,×`/`^` divider (`slot_arithmetic.md`) · question-fusion as
commutativity's pair-layer job (`PairOp.question_fuse`).  The same
forgetting that creates commutativity at the floor rations the phase
budget at the top (`{1,2,3,4,6}`, both modules).

## Open frontier

The grid leg is narrated but not yet ∅-axiom: `×`-commutativity
derived from the grid transposition at the append/count level (the
double-count of a rectangle), parallel to `add_comm_from_append`.
The staircase's translation property (iterates of self-translations
are self-translations, failing at `x ↦ a^x`) is stated as the
fold-engine criterion but awaits its generic formalization.
