# Graph connectivity → δ⁰-closed colourings are constant

**Status**: Closed.

## Overview

A minimal, reusable graph-connectedness induction.  Over an abstract
adjacency `Adj : V → V → Prop`, the single load-bearing fact:

> if a `Bool` colouring is constant across every edge (`IsClosed`) and
> every vertex is reachable from a root (`IsConnectedFrom`), then the
> colouring is globally constant — so the δ⁰-kernel collapses to the two
> global constants, `b₀ = 1`.

This is the graph-connectedness induction infrastructure the parametric
bipartite cohomology needs to lift `ker δ⁰ = constants` off the
complete-bipartite special case onto any connected graph.

## Form

Reachability is an **inductive predicate** `Reach Adj root`, so the
propagation argument is plain structural induction — no well-founded
recursion, no `propext`, no `funext` (every statement is pointwise).
The whole file is ∅-axiom.

  - `closed_eq_root` — a δ⁰-closed colouring equals the root colour at
    every reachable vertex (structural induction on `Reach`).
  - `closed_const` — connectivity ⟹ global constancy.
  - `closed_false_or_true` — kernel = exactly the two constants (b₀ = 1).
  - `closed_root_determines` — the root colour is the single free
    parameter (`dim ker = 1`).
  - `reach_one`, `reach_two` — one- and two-edge reachability helpers.

## Bipartite instantiation

`Cohomology/Bipartite/Parametric/Betti/KernelConstancyUniversal.lean`
instantiates the framework on K_{NS,NT}^{(c)}:

  - `bipAdj` — the S–T adjacency (S-side index `< NS`, T-side `≥ NS`).
  - `bipAdj_connected` — K_{NS,NT}^{(c)} is connected for NS ≥ 1, NT ≥ 1:
    T-vertices reached from the root S-vertex in one step, the other
    S-vertices in two (`S0 → T0 → Sᵢ`).
  - `isConstOnEdges_isClosed` — edge-constancy = δ⁰-closedness for
    `bipAdj`.
  - `isKer_const_via_framework` — the δ⁰-kernel = constants conclusion,
    re-derived through the abstract `closed_const`.

The only graph fact special to the bipartite deployment is
`bipAdj_connected`; everything else is the domain-agnostic framework.

## Lean source

- `lean/E213/Lib/Math/Combinatorics/GraphConnectivity.lean` — the
  abstract framework
- `lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/Betti/KernelConstancyUniversal.lean`
  — bipartite instantiation + the direct (division-free) kernel close

## Connection

- `theory/math/cohomology/bipartite.md` — the universal δ⁰-kernel =
  constants result this framework underwrites
- `theory/math/geometry/geometrization_conjecture.md` — the
  `d_M = d_213 − 1` chart-axis reading consuming the 1-dimensional
  self-pointing kernel
