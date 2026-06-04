# `Real213/Lattice/` — Real213 lattice operations

Lattice structure on Real213 cuts: max, min, midpoint, scale, equiv.

## Files (5)

  - `CutMaxMin.lean`        — `cutMax` / `cutMin` operators
  - `CutMidSelf.lean`       — midpoint base lemmas
  - `CutMidMono.lean`       — midpoint monotonicity
  - `CutLatticeEq.lean`     — lattice-equiv lemmas
  - `CutScaleLattice.lean`  — scale ⊗ lattice interaction

## Where to add new files

  - New lattice op           → `Cut<op>.lean` (e.g. CutSup, CutInf)
  - Monotonicity / equiv     → `Cut<op>Mono.lean` / `Cut<op>Eq.lean`
  - Scale interaction        → `CutScale<...>`

## Companion sub-clusters (in `Real213/`)

  - `Core/`      — type + equiv + poset
  - `Sum/`       — addition
  - `Mul/`       — multiplication
  - `Bisection/` — bisection / continuity
  - `ExpLog/`    — exp / log
