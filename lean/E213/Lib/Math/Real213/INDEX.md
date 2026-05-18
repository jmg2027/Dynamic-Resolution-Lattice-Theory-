# Real213 — Module Index (sub-organized 2026-05-13)

213-native real-number type via Dedekind cut.  57 files in 7 sub-clusters.

## Sub-clusters

| Dir | Files | Topic |
|---|---|---|
| `Core/` | 11 | type + Equiv + ValidCut + Dyadic + Functions + Poset |
| `Sum/` | 11 | cutSum + signedSum family |
| `Mul/` | 15 | cutMul/Inv/Pow/Poly + ConstCutScale + CutBinary/Double/Distance |
| `Lattice/` | 5 | cutMax/Min/Mid + LatticeEq + ScaleLattice |
| `Bisection/` | 3 | bisection + continuity (CutBisection{,Algo}, CutContinuity) |
| `ExpLog/` | 11 | CutExp/Log series + ODE + Geom* (Cauchy convergence) |
| `Cauchy/` | 1 | ChainToCut (Method A Nat213 chain → cut bridge, via `Lens.Number.Nat213.Bridge.value_toRaw*`) |

## Top-level

`Real213.lean` — umbrella aggregator.

## Architecture notes

- Real = (sequence + modulus) pair — PAPER1 §6, §7 type-level form.
- Cut = `Nat → Nat → Bool` (m, k ↦ "value ≤ m/k").
- Real213 marathon: ~90% PURE — most CutSum/CutMul/Lattice
  paths propext-free via pointwise eq + ChainToCut bridge.

PURE 진행: see STRICT_ZERO_AXIOM.md.
