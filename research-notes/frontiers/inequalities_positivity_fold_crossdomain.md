# Inequalities as POSITIVITY folds — curvature arc × proof-ISA arc

**Cross-domain note** (organization-branch `/process` pass, after promoting
`theory/math/geometry/discrete_curvature.md`).  Two already-closed sub-trees
name the same object at different depths:

- **Proof-ISA arc** (`Lib/Math/Foundations/ProofISALifts.lean` A7):
  POSITIVITY = "a bound is forced because its gap is a square"
  (`positivity_of_sq`).  Its conquest exhibit is **2-D Cauchy–Schwarz**
  (`cauchy_schwarz_2d`): gap = the single square `(u₀v₁ − u₁v₀)²`
  (Lagrange identity) — a **depth-0** certificate, one algebraic identity.
- **Curvature arc** (`GeometrizationConjecture/BakryEmeryBipartite.lean`):
  the **n-dimensional power-mean Cauchy–Schwarz** `cauchy_schwarz_gridZ`
  (`(Σa)² ≤ n·Σa²`) is proven by induction whose **every rung's gap is
  itself an SOS**: `Σ_j (a_j − a_m)²` (via `kab_inner`).  The certificate
  is *distributed along the inductive spine* — POSITIVITY composed with
  the induction/LOOP instruction.

## The observation: one SOS, two presentations

The n-dim gap has a closed pair-indexed SOS form,
`n·Σa² − (Σa)² = Σ_{i<j} (a_i − a_j)²`.  The Lean proof does not state it;
it *compiles* it onto the 1-D inductive spine of `gridSumZ` — rung `m`
contributes exactly the new-vs-old pairs `Σ_{j<m} (a_j − a_m)²`, a
triangular enumeration of `{(i,j) : i<j}`.  So:

> The **bound** is presentation-invariant; the **certificate** is
> presentation-dependent — depth-0 (pair-sum Lagrange form) vs folded
> (per-rung SOS along the pointing).  Same residue, two pointings; the
> instruction is one (A7 POSITIVITY).

This is the certificate-level instance of
`Real213/PresentationDependence` (holonomicity/depth is a property of the
pointing, not the real).

## Consumer evidence: the regime split is certificate depth

`kab_cd_narrow` vs `kab_cd_wide` (the `K_{a,b}` curvature): the **wide**
regime `b ≥ 2a−2` closes by shell SOS alone (depth-0); at the boundary
the `X²`-coefficient `2b−4a+4` changes sign and the **narrow** regime
needs `cauchy_schwarz_gridZ` (the folded certificate) to trade `X²`
against `b·Γ`.  The wide/narrow split of a curvature theorem is literally
the depth of its positivity certificate.

Further repo instance: `lazyHeatStep_l2_jensen` (marathon P3, "L²-Jensen
via POSITIVITY") — convexity bounds as the same instruction.

## Open

1. **Per-rung-SOS normal form**: is every classical n-dim inequality the
   repo carries (full two-sequence Cauchy–Schwarz, AM-GM, Jensen,
   power-mean family) an A7 fold with an explicit per-rung SOS — i.e. does
   "inequality" = "POSITIVITY ∘ LOOP" hold as a compilation theorem, the
   way A5 COUNT composes with union-bound/double-counting?  **First brick
   CLOSED** (`BakryEmeryBipartite` §5.5, ∅-axiom): the pair-sum Lagrange
   identity `n·Σa² − (Σa)² = Σ_{i<j}(a_i−a_j)²`
   (`lagrange_pair_identity`, with `lagrangePairSumZ` the triangular
   double-sum) stated next to `cauchy_schwarz_gridZ`, and the two
   certificates proved equal — rung `m` of the closed sum is literally the
   per-rung SOS the fold folds in (same `kab_inner`), and Cauchy–Schwarz
   re-derives from the depth-0 form (`cauchy_schwarz_via_lagrange`).  The
   2-D collapse to the single square `(a₀−a₁)²` (`lagrange_pair_two`) ties
   it to `Foundations.Positivity.cauchy_schwarz_2d` (A7's conquest).  *Still
   open*: the **general** "inequality = POSITIVITY ∘ LOOP" compilation
   theorem over the rest of the family (AM-GM, Jensen, power-mean).
2. **Bearing on G205's open question** (POSITIVITY = GAP sub-mode or own
   primitive): the fold-depth axis is evidence for the sub-mode reading —
   POSITIVITY composes with LOOP exactly as COUNT does, suggesting one
   GAP primitive with two faces (cardinality / norm) and a depth
   parameter, not two primitives.
