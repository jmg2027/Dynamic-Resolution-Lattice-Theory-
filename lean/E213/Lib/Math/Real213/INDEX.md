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
| `ExpLog/` | 13 | CutExp/Log series + ODE + Geom* (Cauchy convergence) + EulerCut (e) / PiCut (π) |
| `Cauchy/` | 1 | ChainToCut (Method A Nat213 chain → cut bridge, via `Lens.Number.Nat213.Bridge.value_toRaw*`) |

## Top-level

`Real213.lean` — umbrella aggregator.

**Named-constant cuts via `AbCutSeq`**:
  - `AbCutSeq.lean` — ★ every monotone-bounded ab-sequence is a `Real213` cut
    (the shared carrier: valid/ratio/nesting/eventual-const/completion/
    `limit_brackets`).  Instances: `ExpLog/EulerCut` (e), `ExpLog/PiCut` (π),
    `PhiAbCut` (φ).
  - `PhiAbCut.lean` — φ as an `AbCutSeq`; the algebraic/transcendental split as a
    theorem (φ completes with closed-form modulus `N=2k`, e/π take it as a
    hypothesis — algebraicity *is* the closed-form modulus).
  - `MobiusProbeTwist.lean` — the cut-probe lattice `(m,k)` is twisted by the
    Möbius `P = [[2,1],[1,1]]` (`Pstep (m,k) = (2m+k, m+k)`); P preserves rational
    order (det `= NS−NT = 1`), so the twist sends cuts to cuts
    (`cutThroughP_ratio`).  The two probe axes are braided by the `(NS,NT)=(3,2)`
    matrix.
  - `PhiProbeFixed.lean` — ★ **φ is the fixed cut of the probe-twist**:
    `cutThroughP phiCut = phiCut` (∀, PURE).  The cut-level shadow of "φ is the
    eigenvector of P".  Both sides reduce to the subtraction-free master invariant
    `masterCut m k = decide(k ≤ 2m ∧ mk+k² ≤ m²)` (the φ-norm `m² ≥ mk+k²`).
  - `ProbeTwistFixedPoint.lean` — the dichotomy: φ's cut is twist-fixed, a
    transcendental's is not (`e_not_fixed`: `cutThroughP (eulerCut 4) 3 1 ≠
    eulerCut 4 3 1`, witnessed by the probe `3/1 ↦ 7/4`).  φ is the twist's
    eigen-direction; e/π are moved by the two-axis braid.
  - `ProbeTwistDynamics.lean` — ★ *how* a non-φ cut wobbles: `twist_undoes_step`
    proves `cutThroughP (constCut (2p+q)(p+q)) = constCut p q`, i.e. the probe-twist
    runs the Pell recurrence **backwards** on the value (`f⁻¹`, expanding away from
    φ), the exact inverse of advancing the convergents (`f`, contracting toward φ).
    φ is the lone common fixed point `f(φ)=f⁻¹(φ)=φ`.

## Architecture notes

- Real = (sequence + modulus) pair — type-level form of Cauchy completeness.
- Cut = `Nat → Nat → Bool` (m, k ↦ "value ≤ m/k").
- Real213 marathon: ~90% PURE — most CutSum/CutMul/Lattice
  paths propext-free via pointwise eq + ChainToCut bridge.

PURE 진행: see STRICT_ZERO_AXIOM.md.
