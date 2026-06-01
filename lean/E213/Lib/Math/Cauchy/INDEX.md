# `Lib/Math/Cauchy/` — Cauchy / Euler / Wallis / Pell sequences + the depth arc

213-native sequence machinery and the real-number / completeness arc: monotone-
bounded, Archimedean, profinite sequences, the classical families (Euler, Wallis,
Pell), and the divergence-depth / resolution-axis tower.

Narrative: `theory/math/completeness_without_completeness.md`.

## Foundations + properties

  - `GenericFamily.lean`     — generic Cauchy-family combinator
  - `MonotonicBounded.lean`  — monotone-bounded ⇒ Cauchy
  - `Archimedean.lean`       — Archimedean property
  - `ProfiniteSeq.lean`      — profinite sequence type

## Specific sequences

  - `Euler.lean`             — Euler-formula sequence + Cauchy (e ∈ (2,3))
  - `Wallis.lean`            — Wallis product (π/2 ∈ (1,2))
  - `PellSeq.lean`           — Pell sequence as Cauchy seq

## Divergence form + depth (the resolution-axis tower)

  - `EulerDivergenceForm.lean`     — cross-determinant `W_n` (discrete Wronskian):
                                      φ `±1`, e `−n!`, π Wallis
  - `DivergenceLadder.lean`,
    `DivergenceDepth.lean`         — finite-difference depth (φ 1, e 3, π 6,
                                      Liouville ∞); = P-recursive rank
  - `DepthFloorDetOne.lean`        — the depth-0 floor IS det P = 1 (P-orbit invariant)
  - `DepthPRecursive.lean`         — finite depth ⟺ P-recursive (structural)
  - `DepthPRecursiveInstances.lean`— witnesses: `newton_polyDepth` (every degree-`d`
                                      discrete polynomial has depth `d`, via exact
                                      Pascal differences); e (order-1 recurrence +
                                      `polyDepth 1`); π (Wallis recurrences +
                                      `polyDepth 2` step coefficient)
  - `DepthPiQuartic.lean`          — π's full degree-4 cross-det ratio has
                                      `polyDepth 4` (depth 6 ∅-axiom), nonlinear
                                      expansion via `Meta/Nat/PolyNat` reflection
  - `DepthTower.lean`              — the ratio-lift axis (= diff on the exponent);
                                      `(h,d)` coordinate
  - `DepthOrdinal.lean`            — `(h,d)` is an ordinal `< ω²` (`lex_wf`)
  - `DepthExponentRecursion.lean`,
    `DepthDoubleExp.lean`          — third axis = recursion into the exponent;
                                      `ratioN` cannot cross one exponential layer
  - `DepthOmegaTower.lean`         — the depth-`r` tower coordinate is an ordinal
                                      `< ω^r` (`coord_wf`); the `ω^ω` ladder, each
                                      layer ×`ω` (`coord_layer_dominates`)
  - `DepthLiouvilleCoord.lean`     — `k!` (Liouville exponent, diff-∞) gets a finite
                                      recursion coordinate: `ratioLift fact = n+1`,
                                      one diff floors it
  - `DepthCeilingResidue.lean`     — naming the ceiling-raising is a diagonalisation
                                      = the residue (`cantor_general`)
  - `DepthOverflowDuality.lean`    — the diagonalisation residue and the
                                      completeness-break are one operation: a value
                                      overflowing the closing bound by the unit `1`
                                      escapes the family (`overflow_escapes`) or breaks
                                      domination (`overflow_breaks`) — same surplus,
                                      two scales (`overflow_dual_reading`)
  - `DepthClosure.lean`            — the finite-coordinate class is closed under `×`
                                      and the exponent axis (`diff` linear), breaking
                                      at the exponential `2^{2^n}`
  - `DepthCoordGenerator.lean`     — the tower as a coordinate system: `binom·d` /
                                      `expTower` realize every coordinate, top-down

## Companion clusters

  - `Real213/Cauchy/ChainToCut`   — Cauchy chain → cut bridge
  - `Real213/ExpLog/*Cauchy*`     — exp/log series convergence
  - `DyadicFSM/Pell/`             — Pell FSM encoding
  - `Math/Analysis/<...>Cauchy*`  — analysis-level Cauchy

## Where to add new files

  - New sequence family   → `<Sequence>.lean` (consolidate evolution-of-the-same-
                            topic per CLAUDE.md rule 7)
  - New depth/axis result → `Depth<Topic>.lean` in the depth cluster
  - New property          → `Monotone*` / `Archimedean*` / `Profinite*`
