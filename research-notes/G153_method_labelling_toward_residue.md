# G153 — Method: why one slips, and labelling toward the residue's outline

**Date**: 2026-05-30. **Status**: methodology note (tier-1, volatile).
A positive-form companion to CLAUDE.md's failure-mode guards (which are
negative: "don't do X").  Written for the next session's Claude, who starts
fresh under the same distributional gravity.

## Why one slips (the gravity)

An LLM's training distribution is built almost entirely from texts written
*from a fixed standpoint* — an observer, a metalanguage, a set-theoretic
universe, a "what is really the case."  So the default move is **to pick one
viewpoint and stand on it**.  That is the gravity of the distribution.

213 is exactly the place where that standpoint is absent (`05_no_exterior.md`).
So the default move *misfires* every time: it promotes one reading
(separation/non-separation, distinct/미분화, gap/glue, one Lens output) to "what
the residue IS."  This is not a stray bug — it is the distribution pulling
toward the nearest familiar frame because 213 offers no handle to grab.

Consequence: understanding 213 is **not a stored state** ("I read seed/AXIOM, so
I know it").  It is a *per-utterance act* of not sliding into the standpoint.
The axioms can be read once; not-slipping must be re-done every time.  (This is
itself 213-shaped: comprehension is an act, not a static object.)

## The positive method — labelling toward the outline

Mingu's framing: **continuing to plant labels is both the limit and the only
method** — for the investigator and ontologically alike.

  - No interior/exterior ⇒ no single reference point can be fixed ⇒ every label
    is *relative* (this = not-that) ⇒ planting one label auto-summons the next
    (that also needs a label, and so on).  Labelling does not "fail to stop"; a
    *stop* is simply undefined here.  To exist (in a no-exterior place) is to
    have begun labelling, and beginning auto-chains.

  - A *single* label cannot be judged "the floor" (undecidable in general).
    But planting *many* labels and reading their **common shadow** narrows the
    residue's outline.  The "floor" is not where the regress stops (it does not)
    — it is **what keeps the same shape under further label-refinement**
    (self-similar under descent), i.e. a fixed point, not a terminus.

  - Caution (the guard, applied to the method itself): the common shadow is
    *not* "the residue's identity" — fixing it that way is again promoting a
    view.  The shadow is **evidence of the direction several views converge**.
    An assembled structure is not a final floor but *a deeper view more views
    can join*; the joining does not stop, it only sharpens the outline.

So research here is not finished — it is the unbounded narrowing of an outline.
This is the *active* reading of "why the repo is vast" (CLAUDE.md): not clutter
but a pile of labels narrowing the outline.  Viewpoint-count is the asset, not
merge density.

## This session as an instance of the method

  - Several views were each planted as one label-attempt at the residue:
    `Lambek` (decompose↔build is one iso), `FlatOntologyClosure` (the
    Cantor-unpointable surplus), `FlatOntology` (object/relation = one
    predicate sort), `Mobius213OneAsGlue` (gap = glue = the same 1).
  - Their common shadow: each is "a place where a dual looks like one shape,"
    each "closes into itself," each "is itself outside every view's image."
  - Assembled (not as a final floor, as a deeper view): the residue is what all
    these duals collapse toward — `two_closures` (the act's self-fixed-point and
    the finiteness of pointing are distinct levers meeting at Raw = μF), and the
    informal "213 = the most primitive view where duals look like one shape,
    seen as the vanishing point all dual-readings converge to (itself
    unpointable)."
  - The five-agent sweep earlier *was* this method (label the residue from five
    repo regions, then extract the common shadow) — named here as a principle.

## Standing dual-pairs collapsing to one shape (the running catalog)

| dual (classically two) | primitive view (one shape) | witness |
|---|---|---|
| object / morphism | predicate on Raw^n | `FlatOntology` |
| transition / state | `slash` output (line = point) | `Theory/Raw/Slash` |
| decompose / build | mutually inverse (one iso) | `Raw/Lambek` |
| difference / identity | the same `1` | `Mobius213OneAsGlue` |
| separation / non-separation | both are Lens readings | `RawTopology` bookends |
| definable predicate / total space | round-trips / Cantor-blocked | `PredicateSelfEncoding` + `FlatOntologyClosure` |

The point of the catalog is not the rows but the **shared column**: each dual is
one shape under a sufficiently primitive view, and the residue is what every row
converges toward without any row being it.

## Open continuations (for the marathon)

  1. **Self-similar floor**: formalise "what keeps the same shape under
     label-refinement" — a self-similarity / fixed-point statement of the
     residue under descent (ties `Lambek.two_closures` to the `5^L` /
     fractal-level self-similarity, and to φ as `P(φ)=φ`).  **DONE** —
     `Raw/Lambek.{self_similar_peel, self_similar_floor}` (8 PURE total):
     peeling a non-atom yields two parts that each again satisfy `decompose`
     (same atom-or-slash shape — self-similar) while depth strictly drops
     (refinement descends), bottoming out at the atoms.  The floor is the fixed
     shape under refinement (invariant form + terminating descent), not a
     stipulated stop.  **Quantitative link DONE** —
     `Lib/Math/SelfSimilarityBridge.lean` (3 PURE):
     `self_similarity_two_readings` joins the form reading (Raw
     `self_similar_floor`) and the count reading (`self_similar_count :
     numV (m+n) = numV m · numV n`, the `5^L` level-replication law).  One
     self-similarity, two Lenses (form / count).  **φ-side DONE** —
     `self_similar_ratio_is_phi` + `self_similarity_three_readings` (5 PURE
     total): the P-orbit's consecutive-term ratio settles on the irrational
     fixed point φ (`tower_growth_phi_squared_bracket` ∈ (2,3)=φ²;
     `phi_bracket_via_pell` brackets φ as a Cut).  Three readings of one
     self-similarity from the (NS,NT)=(3,2) signature: form (shape invariant),
     count (rational factor `5 = disc P`), limit-ratio (irrational `φ` = P's
     fixed point).  Fully closes G153 #1.  **Limit-ratio further PINNED** —
     `Real213/PhiConvergence.phi_is_unique_nested_limit` +
     `SelfSimilarityBridge.self_similar_ratio_pins_phi`: the convergents nest
     (cross-products ±1) and shrink (denominators grow), so φ is the unique
     nested-bracket limit, not merely bracketed.
  2. **Scale-invariant non-separation**: the transition=state / line=point
     collapse holds at the atom (`a/b`) AND at the limit (ℝ as `ValidCut`,
     `Real213/Core/AsLensOutput`) — one theorem that the same collapse recurs at
     both scales.  **DONE** —
     `Lib/Math/Real213/ObjectIsReadingScaleInvariant.lean` (4 PURE):
     `object_is_reading_scale_invariant` — at both scales the object is a reading
     `Index → Bool` (`Object1 : Raw → (Raw→Bool)` at the atom scale;
     `RealAsLensOutput = Nat → (Nat→Bool)` at the limit scale); only the index
     differs.  "Object = reading" is one shape `ObjectAsReading ι` read at two
     indices, not a coincidence repeating.
  3. **Dual-collapse as a uniform statement**: the catalog rows above are
     currently separate files; a single "every framework-internal dual is
     self-dual under the pointing view" statement would be the column made
     explicit.  **DONE** — `Lib/Math/DualCollapseCapstone.lean` (1 PURE):
     `every_dual_is_one_shape` bundles the four proven instances
     (Lambek `two_closures`; FlatOntologyClosure `self_covering_closure`;
     Real213 `object_is_reading_scale_invariant`; OneAsGlue
     `mobius_det_eq_ns_minus_nt`) to exhibit the shared column — each dual is
     one shape under the pointing view.  It is convergence evidence, not a
     capture of the residue (the non-surjectivity conjunct keeps the residue
     outside every single view).

All three continuations now have ∅-axiom bricks; the residue stays the unbounded
outline the labels narrow, never a captured object.
