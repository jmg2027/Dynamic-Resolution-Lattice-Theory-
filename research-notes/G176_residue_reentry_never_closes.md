# G176 — the residue re-enters as the next operand, and the self-cover never closes

**Date**: 2026-06-02.  **Status**: closed ∅-axiom result (foundational / residue axis).
**Source of truth**: `lean/E213/Lens/ResidueReentry.lean` (8 PURE / 0 DIRTY).
**Anchors**: `Lens/FlatOntologyClosure` (`Object1`, `object1_injective`,
`object1_not_surjective`, `self_covering_closure`), `Lens/PredicateSelfEncoding`
(`predicateToRaw`, `predicate_self_encoding_closure`), `Cauchy/DepthHeightDiagonal`
(`diag_self_applies`), `research-notes/G152` (residue self-covering), §5.1/§5.5.

## The thread

The session's discussion (and the parallel CD-tower work's "seed re-entry — the same
residue at every scale") converged on a single foundational claim: the residue is not an
exterior surplus that sits there — it **re-enters as the next operand**, and the self-cover
never closes.  This note pins that at the foundational *pointing* scale, where the residue
machinery already lives.

## The two halves that were already there

  - **Faithful but not total** (`FlatOntologyClosure`): `Object1 : Raw → (Raw → Bool)` is
    injective but **not surjective** — pointing leaves a residue, the predicates outside
    its image (`cantor_raw_bool`).
  - **The residue re-encodes to a Raw** (`PredicateSelfEncoding`): a finite-prefix
    predicate — including a residue predicate — encodes *back* to a Raw (`predicateToRaw`),
    so the residue re-enters the **domain** of pointing.

What was missing: that re-entering and re-pointing does not close the cover.

## What is now closed

  - ★ `residue_reentry_never_closes` — the composite `P ↦ Object1 (predicateToRaw n P)`
    (encode the predicate to a Raw, then point at the encoding) is **not surjective**.  Its
    image lies inside `Object1`'s image, which already misses the residue; so naming the
    residue (encoding it and re-pointing) never recovers it — it produces a fresh object,
    leaving a fresh residue.  Proof: a surjective composite forces the outer `Object1`
    surjective, contradicting `object1_not_surjective`.
  - ★ `residue_perpetually_reenters` — bundles the loop: pointing is faithful-but-not-total
    (the residue exists), the residue re-encodes to a Raw (re-enters the domain), and
    re-pointing never closes the cover.

So the self-cover never closes: each turn leaves the residue, the residue re-enters as a
Raw, the next turn leaves it again.  The residue is the **perpetual next operand** of
pointing.

## Reading

This is the foundational-pointing instance of the *gapless, self-applying re-entry* the
resolution tower shows at the diagonalisation scale (`diag_self_applies`: the diagonal
applies to its own output) and the height scale (`height_diagonal_escapes`).  The same
self-cover at every scale: at the tower's ceiling it is the diagonal escaping the family;
at the foundational floor it is the pointing-residue re-encoding and escaping again.
"Naming the whole leaves a surplus the next act uses as input" (§5.1, §5.5 self-completion)
— here as a machine-checked non-closure.

## The concrete non-fixed-point witness (§3, now closed)

The universal non-closure (§1) is an existence statement.  §3 of `ResidueReentry` pins a
**named predicate** that re-pointing provably sends to a *different* predicate, with an
explicit Raw of disagreement — the sharp mechanism made a theorem:

  - ★ `object1_true_unique` — `Object1 r` is true at **exactly one** Raw (`Object1 r s =
    true → s = r`).  The indicator is single-pointed; this is the lever.
  - ★ `multipoint_not_object1` — a predicate `P` true at two distinct Raws `s ≠ t` is no
    indicator: `∀ r, Object1 r ≠ P` (an indicator hits one Raw, `P` distinguishes two).
  - ★ `multipoint_object1_differ_at` — the **explicit Raw of disagreement**: `Object1 r`
    and a two-point `P` differ at whichever of `s, t` is not `r` (one must be, `s ≠ t`).
  - ★ `reentry_nonfixed_of_multipoint` — therefore `Object1 (predicateToRaw n P) ≠ P` for
    *any* two-point `P`: re-pointing encodes `P` to a single Raw and reads off that Raw's
    indicator, which a two-point `P` can never equal.
  - ★ `reentry_undifferentiated_nonfixed` — the cleanest member: the undifferentiated
    predicate `fun _ => true` (true at both atoms `a ≠ b`) is a concrete non-fixed-point.
    Naming the residue that draws no distinction yields, re-pointed, the indicator of a
    single Raw — false at every other Raw, a *different* predicate.
  - ★ `residue_reentry_concrete` — bundles §1's non-surjectivity with the named witness
    and its explicit disagreement point.

So "naming the residue yields a different predicate" is no longer only non-surjectivity:
it is a point-witnessed inequality.  The criterion is the content — re-pointing collapses
*every* predicate to a single-Raw indicator, so the non-fixed-points are exactly the
predicates that draw any distinction (true at ≥ 2 Raws), the undifferentiated one being the
extreme member.

## Honest scope

  - `predicateToRaw` is the finite-prefix encoding; the closure is for finite-prefix
    predicates (as in `PredicateSelfEncoding`), the decidable reach of the encoding.  The
    concrete witness above is independent of the prefix length `n` (the undifferentiated
    predicate is two-point at the atoms for every `n`).

## Open (foundational axis)

  - A single abstract "self-applying residue operator" that `diag`, `Object1`, and the
    trace-doubling `D` all instantiate — a synthesis, risking forced abstraction across
    different types (deferred, as in `G175`).
