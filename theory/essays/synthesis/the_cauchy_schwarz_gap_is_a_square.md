# The Cauchy–Schwarz gap is a square

Cauchy–Schwarz is not an estimate.  It is the **READ of a gap that is
exhibited as a square**: the deficit between the two sides is an
intrinsically nonnegative fold, so the bound is forced with no analysis
(`Lib/Math/Foundations/Positivity.positivity_of_sq`, archetype A7 of
`Lib/Math/Foundations/ProofISALifts.lean`).

## 213-native answer

Take the two-vector form `⟨u,v⟩² ≤ ⟨u,u⟩⟨v,v⟩` over `Int`.  The gap
`⟨u,u⟩⟨v,v⟩ − ⟨u,v⟩²` *is* the square `(u₀v₁ − u₁v₀)²` — the Lagrange
identity (`Positivity.cauchy_schwarz_2d`).  Nothing is estimated; an
algebraic identity rewrites the deficit as a square, and a square is a
nonnegative readout.  The entire content of the inequality is the
identity; the "≤" is one application of `positivity_of_sq`.

## Derivation: what the gap counts

The power-mean form `(Σa)² ≤ n·Σa²` makes visible *what* the square
measures.  `(Σa)²` reads the family by pointing at it twice
independently — every pair `(i,j)` once.  `n·Σa²` reads `n` copies of
the diagonal pairs `(i,i)`.  The gap between the two readings is the
total pairwise distinguishing:

```
n·Σa² − (Σa)²  =  Σ_{i<j} (a_i − a_j)²
```

So Cauchy–Schwarz reads **how much a family distinguishes its members**,
and it is saturated exactly on the diagonal — a family with no
distinguishing left.  The repo carries the saturation witness in the
curvature setting: `BakryEmery.sosGap_eq_zero_of_const` (the SOS gap
vanishes precisely for the constant function).

## One instruction, two certificate depths

The Lean corpus proves the power-mean form without ever writing the
pair-indexed sum.  `BakryEmeryBipartite.cauchy_schwarz_gridZ` runs an
induction along the `gridSumZ` spine, and **every rung's step-gap is
itself an SOS**: rung `m` contributes `Σ_{j<m} (a_j − a_m)²`
(via `kab_inner`) — the new-versus-old pairs, a triangular enumeration
of `{(i,j) : i < j}` carried on a one-dimensional pointing.

The bound is presentation-invariant; the **certificate is a property of
the pointing**: depth-0 (the pair-sum identity, one rewrite) or folded
(per-rung squares along the induction).  This is the certificate-level
face of the fact that depth belongs to the approximant sequence, not to
the value (`Real213/PresentationDependence`).

A consumer exhibits the depth as mathematics, not bookkeeping: the
bipartite curvature bound splits into a wide regime closed by one
completed square (`kab_cd_wide`) and a narrow regime where the
`X²`-coefficient changes sign and only the folded certificate trades
`X²` against the carré du champ (`kab_cd_narrow`) — the regime boundary
of a curvature theorem *is* the depth of its positivity certificate
(`theory/math/geometry/discrete_curvature.md`).

## Dual function

This is the classical Cauchy–Schwarz with its packaging stripped: no
inner-product space, no norm, no completeness — an `Int` identity plus
"a square is nonnegative".  The stripping is itself the refinement: once
the inequality is an identity-plus-READ, it acquires a parameter the
classical statement hides — certificate depth — and classical corollaries
(Jensen-type convexity bounds, `lazyHeatStep_l2_jensen`) line up as the
same instruction applied to other folds.

## Cross-frame

A5 COUNT and A7 POSITIVITY are the two faces of one deficit-forcing
move (`ProofISALifts`): COUNT forces existence because a *cardinality*
gap is positive; POSITIVITY forces a bound because a *norm* gap is a
square.  The folded Cauchy–Schwarz shows POSITIVITY composing with the
induction instruction exactly as COUNT composes with union
bound / double counting — evidence that the two are one GAP primitive
read through two Lenses (count / square), with depth as the composition
parameter.

## Open frontier

The pair-sum identity `n·Σa² − (Σa)² = Σ_{i<j}(a_i−a_j)²` is stated
here, not yet a Lean theorem (the buildable brick: prove it next to
`cauchy_schwarz_gridZ` and identify the two certificates).  The
two-sequence n-dimensional form, the equality case as a theorem
(`gap = 0 ⟺` diagonal), and the "every classical inequality =
POSITIVITY ∘ fold" compilation claim are open, tracked on the
`research-notes/frontiers/` board (inequalities-as-positivity-folds).
