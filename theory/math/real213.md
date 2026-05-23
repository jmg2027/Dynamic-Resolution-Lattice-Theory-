# Real213 — Dedekind-Cut Real Numbers (213-native)

**Status**: Closed (57 files in 7 sub-clusters).

## Overview

**Real213** is the 213-native real-number type, built as a
**Dedekind cut on dyadic rationals** with finite precision at every
operation.  No completion-at-infinity: every Real213 value is a
sequence of dyadic brackets at progressively finer levels, with
the value's identity = the limit predicate on the bracket sequence.

Standard `ℝ`-theorems (Cauchy completeness, IVT, MVT, ε-δ
continuity) all hold in Real213 with **explicit modulus
functions** instead of existential ε-δ quantifiers.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Real213/` (57 files, 7 sub-clusters)
- **Umbrella**: `Real213.lean`
- **∅-axiom status**: PURE on production critical path

### Sub-cluster organization

| Sub-cluster | Files | Topic |
|---|---|---|
| `Core/` | 11 | type + Equiv + ValidCut + Dyadic + Functions + Poset |
| `Sum/` | 11 | cutSum + signedSum family |
| `Mul/` | ~8 | cutMul algebra (commutativity, associativity, distributivity) |
| `Inv/` | ~6 | multiplicative inverse via reciprocal-cut |
| `Order/` | ~5 | total order on Real213 cuts |
| `Bridge/` | ~10 | bridges to Cauchy, DyadicFSM, SignedCut |
| `Misc/` | ~6 | absolute value, signum, miscellaneous |

## The narrative

### Why classical ℝ doesn't fit 213

Classical ℝ is the completion of ℚ at infinity — every Cauchy
sequence of rationals **converges** to a real, where "converges"
is an existential.  In 213's substrate, there is no "at infinity"
— every operation must produce a finite output at finite depth.

The naive workaround (use only ℚ, lose continuity) is wrong:
DRLT physics needs continuity-style reasoning (precision brackets
that tighten, MVT for the strong coupling, ...).  The right
solution: keep the **Dedekind cut** primitive (which works in 213)
but replace "the cut **is** the real" with "the cut **encodes** the
real as a typed protocol".

### Real213 type

```
Real213 := { lower : Set ℚ // ValidCut lower }
```

where `ValidCut` enforces:
1. Lower set is downward-closed
2. Lower set has no maximum (open above)
3. Lower set is bounded (cut is finite)

All three are **decidable** in 213's substrate.  Real213 equality
is `cutEq`: same lower set.

### Operations

- **`cutSum`** (Sum/, 11 files):
  addition by elementwise sum on representative dyadic brackets.
  Closure-form: bracket(a + b, n) ⊂ bracket(a, n) + bracket(b, n)
  with explicit modulus.  BoolOrLadder is a generic ladder template
  for bool-or sums (REAL-2 per marathon deferred-items log).
- **`cutMul`** (Mul/,):
  multiplication via 4-quadrant case decomposition (sign of a, sign
  of b).  CutMulOuterReduce is the outer-reduce refactor enabling
  FluxMVT-side reuse (FLUX-1 upstream per FluxMVT deep dive).
- **`cutInv`** (Inv/): reciprocal via bracket-reflection.
- **`cutOrder`** (Order/): total order via lower-set inclusion.

Each operation has an **explicit precision bound**: the output's
modulus is a computable function of the input's modulus.

### Connection to other chapters

- `theory/math/analysis/minimal_root.md` — IVT via Real213 cuts
- `theory/math/modulus.md` — modulus combinators used here
- `theory/math/cauchy.md` (separate chapter) — sequence machinery
- `theory/math/signed_cut.md` (separate chapter) — sign extension

## Oracle-based continuity — closed (OracleContinuity.lean, 10 PURE)

`Lib/Math/Real213/OracleContinuity.lean` recasts the
`IsContinuousModulus` framework into the **typed-protocol** style
parallel to `ConsistentOracle`:

  `IsOracleContinuous f` carries:
    · `threshold : Nat → Nat` — input precision lower bound
    · `threshold_pos : ∀ k, threshold k ≥ k` — monotonicity

The data is identical to `IsContinuousModulus`'s `(modulus,
modulus_pos)`; the renaming "modulus → threshold" aligns continuity
with the trajectory-witness paradigm.

Bridge functions `ofModulus` / `toModulus` witness bidirectional
equivalence; round-trip equalities hold pointwise (`rfl`); identity,
constant, and composition are oracle-continuous.  Capstone
`oracle_continuity_capstone` packages forward + backward bridge +
round-trip + composition.

Reading: the "ε-δ residue" in `IsContinuousModulus` is **purely
terminological** — the underlying data (Nat → Nat refinement +
monotonicity) is the same.  Oracle framing makes the trajectory the
witness without changing the structural content.

## Open frontier

- ~~Continuity-without-ε via consistent oracles~~ — CLOSED via
  `OracleContinuity.lean` (10 PURE) above.
- **Differentiation** via `DiffCut` + modulus tracking — partially
  in `Modulus/Translation.lean`, full deferred
- **Measure-theoretic extension** — `Lib/Math/Measure/` provides
  the start; integration over Real213 cuts is open

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Real213
python3 tools/scan_axioms.py Lib/Math/Real213
```
