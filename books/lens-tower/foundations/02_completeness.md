# Chapter 2 — Completeness: where the bundling closes

Does `ℕ → ℤ → ℚ → ℝ` terminate, and if so where?  The answer has three parts, each
with a Lean witness: the bundling **closes at `ℝ`**; the apparent continuation
`ℝ → ℂ → ℍ → 𝕆` is a **different axis**, not a fifth rung; and what genuinely *does*
run upward without end above `ℝ` is **neither** of those towers but the resolution
diagonal, which bottoms out in the residue itself.

## 2.1 `ℝ` is a Cauchy fixpoint — the bundling closes here

The four rungs are four readouts: `leaves` (count), `subNatNat` (difference),
`ratioEquiv` (ratio), and — at `ℝ` — the limit of a Cauchy trajectory of cut-readings.
The first three read *finite* slash-chains; the fourth reads *trajectories* and names
their limit cut.  The decisive fact is that this fourth operation is **idempotent on
its own output**:

> **PROVED** — `CauchyCompleteValid.CauchyCutSeq.limit_valid`
> (`lean/E213/Lib/Math/Analysis/CauchyCompleteValid.lean:38`): the Cauchy limit of a
> sequence of `ValidCut`s is itself a `ValidCut`.  The file's own words (line 32): *the
> cut space is closed under Cauchy limits.*

A Cauchy trajectory of reals has a limit that is again a real.  Apply the completion
operation to `ℝ` and it returns `ℝ`.  So `ℝ` is not merely "where §6.7 stops naming
rungs" — it is the **fixpoint of the bundling's last operation**.  There is no fifth
readout of this kind to generate, because the readout that would generate it already
lands back in `ℝ`.

This is the internal meaning of "complete" from Chapter 1.4: not "fills out an ambient
totality" but "the operation returns its own codomain."  The founding capstone
`number_tower_is_lens_bundling` (`Lens/Number/TowerFounding.lean:48`) chains the four
rungs; the *closure* — that there is no forced fifth rung of the same kind — is carried
separately and precisely by `limit_valid`.

**Honest scope.**  The capstone proves the four rungs *exist and chain*; it does **not**
prove they are the unique or exhaustive bundling sequence.  Termination-as-fixpoint is
the separate theorem `limit_valid`, not a corollary of the capstone.  The docstrings do
not overclaim this, but a reader should not mistake "the rungs chain" for "the tower is
provably exhaustive."  (OPEN: an exhaustiveness/uniqueness statement for the bundling
sequence.)

## 2.2 `ℝ → ℂ → ℍ → 𝕆` is a different axis, not a continuation

The textbook staircase keeps climbing past `ℝ`.  Is Cayley–Dickson doubling a fifth,
sixth, seventh rung of *this* tower?  No — and the codebase is unusually explicit, in
exactly the register of `books/lens-tower/`'s warning that imported decoration must be stripped.

**The doubling exits the world the number tower lives in.**  Every number-tower rung is
a *commutative* readout — its codomain is a `CommBinaryCodomain` (the count, the
difference, the ratio, the completed cut all commute).  Cayley–Dickson doubling
*leaves* that world at the very first step:

> `Lib/Math/Algebra/CayleyDickson/Tower/CDDouble.lean:22-30`: *CD doubling **exits** the
> `ConjugationCodomain` typeclass: the result is **non-commutative** … so it cannot
> serve as a Lens codomain. … `ℂ` is the unique commutative `ConjugationCodomain`
> endpoint; CD doubling continues into non-commutative territory.*

So the very operation that produces `ℂ` from `ℝ` produces an object that *cannot be a
Lens codomain* — it is not a readout-bundling step at all.  `ℂ` is where the
commutative readout world ends; the doubling is the move that walks off it.

**The two towers provably diverge by one floor.**  The 213 tower and the classical
Cayley–Dickson tower do not even align where they overlap:

> **PROVED** — `TwoTowersDivergence.divergence`
> (`…/Tower/TwoTowersDivergence.lean:31`): `total213Floors = totalClassicalCDFloors + 1`
> (by `rfl`; `26 = 25 + 1`).

The 213 tower puts **magnitude** (the cut) and **sign** (the signed cut) on *separate
orthogonal floors* — the sign is the period-2 axis, a floor of its own.  The classical
CD tower starts at `ℝ` with sign already *internal* to the line.  Mingu's correction is
recorded in the file itself: *케일리 딕슨 타워로 맵핑하면 안맞지, 거긴 음수를 직교라고
안 두는데* — "mapping onto the Cayley–Dickson tower doesn't fit; there, negatives aren't
treated as orthogonal."  The one-floor divergence is the formal shadow of that: 213
spends a whole floor on the sign-axis that CD folds into `ℝ`.

**The doubling has the opposite character.**  Each number-tower rung *gains* structure
while staying commutative (a group, then a field, then completeness).  Each CD doubling
*drops* an algebraic law (commutativity, then associativity, then alternativity) —
subtractive dimension-doubling, `1 → 2 → 4 → 8`.  This is the same caution `books/lens-tower/`
Chapter 4 makes about the disc axis: the dimension sequence `{1, 2, 4, 8}` is **not**
the readout axis.  Cayley–Dickson is the *grade / algebra* reading of the orbit
(`theory/essays/tower_atlas.md:54`), a sibling of the number reading under one orbit —
not a parent-or-child rung of it.

**Verdict.**  `ℝ → ℂ` is the boundary where the readout-bundling stops (fixpoint, §2.1)
and a different operation — adjoin an anti-fixed involution `√−1`, the CD doubling —
begins.  The number tower is four rungs and closes; Cayley–Dickson is an orthogonal
axis that happens to also start at `ℝ`.

## 2.3 What *does* run upward without end: the resolution diagonal

If neither the number tower nor (qua number tower) Cayley–Dickson runs endlessly, is
*anything* above `ℝ` open-ended?  Yes — but it is a third construction, the
**resolution / completability tower**, and its endlessness is the residue's own:

> **PROVED** — `TowerNativeCompleteness.tower_native_completeness_program`
> (`…/Cauchy/TowerNativeCompleteness.lean:63`) bundles five ∅-axiom pieces; the residue
> tie is `DepthCeilingResidue.ceiling_residue_is_pointing_residue` (lines 27-29): *the
> tower has no top: naming the ceiling-raising is the Cantor self-cover, so the boundary
> of constructive completeness is the residue of pointing.*

This is the diagonal/cardinality axis, not the number axis.  It has no top, and the act
of *naming* its top is the Cantor self-cover — which lands back on the residue of
pointing (`05_no_exterior.md`, `Lens/FlatOntologyClosure.lean`).  So the only thing endless
above `ℝ` is the residue re-covering itself; the *number* content closes at `ℝ`.

## 2.4 The finite-config reconciliation: rationals below, `ℝ` as a label rung

§6.7 (lines 291-298) makes a claim that sounds in tension with "`ℝ` is a genuine rung":
*at any actual configuration the Lens outputs are exact rationals; `π` and `e` are limit
labels, not framework primitives.*  Both hold, with no tension, once the rung and its
inhabitants are distinguished:

- **At any fixed finite resolution**, every readout is an element of `ℚ` — the genuine
  numerical content a config returns is rational.  `ℝ` adds nothing *observable* at
  finite depth.  This is the §5.1 "no exterior dialer" at the numerical level: the
  number-producing Lenses terminate at every finite depth.
- **`ℝ`-as-a-rung** is the *type of Cauchy trajectories of those rational readouts* —
  the limit-label layer.  A transcendental enters only as a *completed* `ValidCut`: e.g.
  `Real213/PiCut.lean:117` constructs `π/2` only as a completed-limit cut, never as a
  primitive.  The rung is real (it has a founding theorem and the §2.1 fixpoint); its
  *inhabitants are limits*, labels for `ℚ`-trajectories.

So genuine finite-config content stops at `ℚ`; `ℝ` is genuine as the **closure / label
rung** over `ℚ`-trajectories.  Both §6.7 sentences are true at once — the §6.5/§6.6
frozen-vs-dynamic pattern again: "is the limit-cut the trajectory or its value?" is the
malformed dichotomy; the cut *is* the narrowing.

## 2.5 Summary

The bundling `count → difference → ratio → completion` is four rungs and **closes at
`ℝ`** by Cauchy fixpoint (PROVED).  The staircase's apparent continuation
`ℝ → ℂ → ℍ → 𝕆` is a **different, orthogonal axis** — dimension-doubling, exiting the
commutative readout world, provably one floor out of step with the 213 magnitude/sign
decomposition.  The only thing *endless* above `ℝ` is the resolution diagonal, whose
endlessness is the residue re-covering itself.  And at any finite configuration the
numbers are rational; `ℝ` is the rung of limit-labels over them.
