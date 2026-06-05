# The dimension-Lens: slash-as-independence

*Tier 1 (research-notes).  Synthesis tying the geometric series in this
directory to the axiom layer.  Canonical sources win on any overlap:
`seed/AXIOM/02_axiom.md`, `03_form.md`, `06_lens_readings.md`.*

## The claim under test

The dimension-raising construction (`dimension_growth.py`: each new object
opens a fresh orthogonal axis, `n` objects → `(n−1)`-simplex → `Δ^∞`) is a
**Lens reading of the slash** — the same primitive distinguishing that the
count-Lens reads as a tally, read instead as *one new independent direction*.

Call it the **dimension-Lens**: it geometrizes prim-distinctness as linear
independence (orthogonality).

## Why it holds (grounding)

- The slash is *referring to the residue of distinguishing*, not an operator
  (`02_axiom.md` §2.2).  Each distinguishing yields a new Raw.
- Prim-distinctness: distinct Raws are not identified; `x/x` undefined,
  `a/b = b/a` the only axiom-level relation (`03_form.md` §3.3, anti-reflexive
  + symmetric).  So the Raw family is **free except for symmetry /
  anti-reflexivity** — mild quotients only.
- The count-Lens reads the slash as `+1` to a cardinality tally (`02_axiom.md`
  §2.4 clause 1: the `2` is the *count-Lens reading* of the first
  distinguishing, not a Raw cardinality).
- The **dimension-Lens reads the same slash as `+1` independent axis.**  For a
  free family, `count = dimension`.  Geometrically the `n+1` mutually
  prim-distinct Raws realize as the regular `n`-simplex; in the limit the
  vertices become an orthonormal set (the `e_i` of `Δ^∞ ⊂ ℓ²`).

So count-Lens and dimension-Lens are two faces of one residue (the slash):
*how many* distinguishings vs. *how many independent directions*.  They agree
on the tally and differ only in whether independence is geometrized.

## The collapse is the other face (the "degenerate to a point" intuition)

The betweenness reading placed `c = (a+b)/2`: it **identifies** the new Raw
with a real combination of prior ones.  That is not prim-distinctness — it is
an extra Lens-imposed identification the axiom does not supply.  And
`06_lens_readings.md` (lines 368–377) already names this move and its
consequence:

> `0` is the diagonal class `{(n,n)}` — *infinitely many prim-distinct Raws
> identified* … reading that identification as a value folds a degenerate
> sub-view … the completion that **collapses** infinitely many distinguishings.

Identifying prim-distinct Raws ⇒ the degenerate sub-view ⇒ the structureless
pre-Lens residue `0 ≡ ∞ ≡ point` (§6.5).  That **is** the "continuum that
degenerates to a point": the betweenness limit is structurally a point because
the reading dissolved the distinctions, not because a continuum must collapse.

So the session's two intuitions are one canonical fact, read two ways:

| reading of the slash | honors prim-distinctness? | geometry | limit |
|---|---|---|---|
| **betweenness / quotient** | no — identifies Raws | fills a fixed dim | structureless residue (point, §6.5) |
| **dimension-Lens / free** | yes — keeps Raws distinct | opens a new axis each step | `Δ^∞`, distinctions survive |

## The test it must pass — and does: no-exterior shows up as the angle

For the free reading the finite `n`-simplex centroid pairwise angle is
`arccos(−1/n)` — **obtuse**, not `90°`, reaching orthogonality only as
`n → ∞` (`simplex_intermediate.py`).  This is not a defect.  The `n+1` Raws are
all slashes of the **one** residue, so they carry the partition-of-unity /
sum-to-centroid constraint — the geometric image of **no exterior** (§5.1):
there is no outside frame in which they could be freely independent.  Full
independence (orthogonality) is the `∞`-limit; at finite resolution the
distinctions are sum-constrained (anti-correlated, obtuse).  The obtuse angle
relaxing to `90°` is no-exterior made visible.

## Caution (self-check lint #0)

"Dimension" is a **Lens output**, like cardinality (`02_axiom.md` §2.5: Raw
commits to no size / dimension).  The dimension-Lens is one *facet*; it is not
"the slash IS dimension."  The residue sits outside every view's image
(`FlatOntologyClosure.object1_not_surjective`).  The free generators
(simplex corners) are reached by no betweenness — the same not-surjective
structure, one layer down.

## Open frontier — and it needs no trig, no missing reals

Earlier this note called the `arccos(−1/n)→90°` climb hard ("trig / reals with
zero Mathlib").  That was wrong twice, and both are the algebraic-priority
lesson: **don't label a result blocked by missing classical infra before
reframing it 213-natively.**

- **No trig.**  The angle is a red herring.  `cos = −1/n` is the *exact rational
  inner product* of the centered simplex vertices: for `u_i = e_i − centroid`,
  `⟨u_i,u_j⟩ = δ_ij − 1/(n+1)`, so the normalized off-diagonal is exactly
  `−1/n`.  "Orthogonality in the limit" = the rational sequence `−1/n → 0`.
- **No missing reals.**  `Real213` (Cut-based, with Cauchy convergence) already
  exists; the `−1/n → 0` limit is the "widths → 0" flavour already carried by
  `Real213.PhiConvergence`, `GeometricThreshold`, and the `SternBrocotMarkov`
  `Int` positivity lemmas.

So the well-posed ∅-axiom target is a **rational-Gram + rational-limit**
statement (counting / linear algebra, not analysis):
  1. `prim-distinct ⟺ linear independence`: the `n+1` vertices `e_i` have
     Gram `= I` (det 1) ⟺ distinct — and the centered family carries the single
     partition-of-unity dependence `Σ u_i = 0`.
  2. the normalized off-diagonal `−1/n` strictly increases to `0` (approach to
     orthogonality), a rational limit of exactly the available kind.

This is a clean next target on `Real213`, not a blocker.  Not yet formalized.
