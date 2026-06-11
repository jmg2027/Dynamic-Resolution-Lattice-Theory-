# Growth without a clock — the stage, the foliation, and the grading that never dies

Time, in a system with no exterior, is not one thing.  It separates
into three readings of growth — the **run** (a chosen linearization
of events), the **foliation** (a simultaneity convention), and the
**grading** (a fold of the object) — and only the last is
run-invariant.  None of the three is a clock.

## 213-native answer

The asynchronous growth system
(`theory/math/foundations/async_growth.md`; origin
`seed/ORIGIN_RAW.md` §6–§10) fires one event kind: contrast two
present points, adjoin their pair.  "What time is it?" then has
exactly three well-posed forms.  *Which events have happened* — the
run — is underdetermined from inside: determinism ends at the first
composite (`Theory/Raw/Async.step1_forced`), one further firing is
swap-canonical (`level2_canonical`), and the next is not
(`level3_diverges`): two runs reach snapshots that disagree even
after a global swap, the witness being one concrete point, `b/(a/b)`,
present in one snapshot and absent from the other.  *Which events are
simultaneous* — the foliation — is a Lens choice: the lockstep
narration "stage n completes, then stage n+1" (the tension named in
`seed/ORIGIN_RAW.md` §6) imports a convention, not a fact, exactly
as `seed/AXIOM/05_no_exterior.md` §5.7 reads frozen/dynamic as two
Lens readings with no external axis to arbitrate.  *How deep is this
object* — the grading — survives everything: depth and leaves are
catamorphisms of the term itself (`Theory/Raw/Levels.fold_eq_depth`,
`fold_eq_leaves`), and the event cost is the DAG fold
(`UniverseChain/RawDagSize.dagSize`).  The object is its own
history, so "when" collapses into "what".

## Derivation

Two theorems make the separation sharp.  First, divergence is real
but harmless: any two reachable snapshots embed in a common
reachable snapshot with no fairness assumption
(`Theory/Raw/AsyncReach.reach_joinable`) — asynchronous presents are
incomparable, never in conflict, and re-converge in finitely many
steps.  A system whose disagreements always join needs no clock to
stay one system.  Second, the census is not a moment: no run is
forced through the 5-element depth-≤2 population; what distinguishes
it is **past-completeness**, a property of the ancestor order
(`UniverseChain/RawPastCompleteness.depth3_boundary` — at depth 3
exactly the full join survives).  The boundary that looks like "the
time when forcing ends" is, stated honestly, a place in the order,
not a date in a run.

## Dual function

This is relativity of simultaneity with the packaging stripped: no
metric, no observers, no signal speed — just the fact that a partial
order has many linear extensions, and that anything worth calling an
observable must not depend on the choice.  The refinement 213 adds is
that the run-invariant remainder is *computable on the object*: the
"proper time" of a term is not a coordinate but a fold, and the
honest event-cost fold is `dagSize`, not `leaves` — the tree-Lens
overcounts shared history, and the two first split at depth 3
(`RawDagSize.sharing_starts_at_depth3`: `dagSize = 4` against
`leaves − 1 = 5` at the full join).

## Cross-frame connections

The arc's slogan — *the stage is of the run, not of the object* — is
the temporal instance of a fact the corpus already holds in two other
frames: finite-state-ness is of the pointing, not the value
(`theory/essays/synthesis/finite_state_is_of_the_pointing.md`), and
completability is of the presentation, not the real
(`theory/math/numbersystems/completeness_relocated.md` arc).  Three
scales, one non-surjection: properties that vary across covers of
the same residue belong to the cover.  The foliation is simply the
temporal cover.

## Open frontier

Whether the growth order forces a count of "independent directions"
(the axes seed, `research-notes/frontiers/` board) is open; the
constraint proven so far is negative — the bare ordering fraction
diverges, so no finite dimension readout lives on a depth scale.
The orbit-LTE reading of the census tower's 5-adic cycle is likewise
recorded but not yet a theorem.
