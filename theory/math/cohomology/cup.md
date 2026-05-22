# Cohomology — Cup

**Status**: Closed.
**Promoted from research-notes**: 2026-05-22.

Pattern 2 (narrative-from-scratch).

## Overview

The **lex-projection cup product** on Bool-valued cochains over the
canonical (n-1)-simplex.  For α : C^k, β : C^l, and a sorted
(k+l)-subset τ of {0..n−1}:

```
(α ⌣ β)(τ) = α(τ.take k) · β(τ.drop k)
```

where `·` is Bool AND.  This is **not** the standard Alexander–Whitney
cup (which uses (k+1)+(l+1)-vertex inputs with a shared vertex at
position k) nor the antisymmetric wedge (which XOR-sums over all
k-l partitions).  The lex-projection cup picks the *single* sorted
partition and admits its own natural coboundary law.

## Lean source

- `lean/E213/Lib/Math/Cohomology/Cup/`
- ∅-axiom PURE on production critical path

## Twisted Leibniz — the structural identity

The coboundary δ does *not* obey the standard simplicial Leibniz on
this cup.  There is a single un-cancelled face — position `k` —
whose contribution is **the cup itself, evaluated at the
middle-removed face**:

```
δ(α ⌣ β)(τ) = (δα ⌣ β)(τ) ⊕ (α ⌣ δβ)(τ) ⊕ (α ⌣ β)(τ \ {τ[k]})
```

The correction term `(α ⌣ β)(τ \ {τ[k]})` is **self-referential**:
δ of α ⌣ β at τ involves the cup α ⌣ β itself at a face of τ.  No
external term enters; the operation closes within its own value-set.

This identity holds **for all (n, k, l)** with `k + l + 1 ≤ n`.  The
Fin-indexed Lean statement is `fin_level_leibniz_general` in
`Cup/LeibnizFinGeneral.lean`; its pure-Fin-index restatement
`fin_level_leibniz_pure_form` lives in `Cup/LeibnizFinPureForm.lean`.

### Proof architecture

The full ∀(n, k, l) closure is composed from six PURE sub-layers:

| Sub-layer | Content |
|---|---|
| `Cup/LeibnizLexListLevel.lean` | List-level algebraic ∀(k, l) form via the 3-way `xorRange` partition (take/drop boundary lemmas) |
| `Cup/KSubsetEraseIdx.lean` | `eraseIdx` of a kSubset is a kSubset (third sibling to take/drop structural lemmas) |
| `Cup/FaceIdxGeneral.lean` | Well-defined Fin-typed face map `Fin (binom n m) → Fin (binom n (m-1))` |
| `Cup/CupOnList.lean` | Bridge Fin-cup ↔ list-cup via `subsetIdx ↔ kSubset` round-trip |
| `Cup/RangeFoldXor.lean` | PURE replacement for propext-tainted `List.range_succ`, plus foldl-xor ↔ xorRange conversion |
| `Cup/DeltaUnfoldGeneral.lean` | Fin-δ as xorRange over the face-index function |

The capstone Leibniz statement is obtained by:

1. unfolding Fin-δ as an xorRange over `cupOnList` at eraseIdx faces;
2. converting `cupOnList` to the list-level `cupList` via the
   asListCochain wrap;
3. invoking the list-level algebraic identity;
4. converting the side terms back to Fin form via the
   take/drop colex-index bridges.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `cup` | `Cup/Core.lean` | lex-projection cup definition |
| `cup_unfold_general` | `Cup/FinBridgeGeneral.lean` | Fin-cup unfolds to α(frontIdx) ∧ β(backIdx) |
| `list_level_leibniz_general` | `Cup/LeibnizLexListLevel.lean` | algebraic twisted Leibniz at the List level, ∀(k, l) |
| `kSubset_eraseIdx_eq` | `Cup/KSubsetEraseIdx.lean` | eraseIdx of a kSubset is a kSubset |
| `faceIdx` | `Cup/FaceIdxGeneral.lean` | Fin-typed face-index map |
| `delta_via_faceIdx_xorRange` | `Cup/DeltaUnfoldGeneral.lean` | δ as xorRange over faceIdx values |
| **`fin_level_leibniz_general`** | `Cup/LeibnizFinGeneral.lean` | Fin-level twisted Leibniz, ∀(n, k, l) |
| `fin_level_leibniz_self_referential` | `Cup/LeibnizFinGeneral.lean` | self-referential restatement of the capstone |
| **`fin_level_leibniz_pure_form`** | `Cup/LeibnizFinPureForm.lean` | pure Fin-index form (no list-level wrappers in conclusion) |

## Connection

- `theory/math/cohomology/hodge_conjecture.md` — HodgeConjecture sub-tree (parent)
- `theory/math/cohomology/delta.md` — coboundary δ
- `theory/math/cohomology/cochain.md` — Cochain definition
- Other cohomology sub-clusters cite this layer

## 213-native reading

Every operation that *appears* to require external structure actually
closes within the residue (`seed/AXIOM/05_no_exterior.md` §5).  The
lex-projection cup's Leibniz is an explicit cochain-level instance:
δ of α ⌣ β refers back to α ⌣ β's own face values, not to any term
introduced from outside the cup operation.

## Self-reference depth signature and the cup-channel catalog

Iterating the boundary-self correction traces a path through the
face poset.  The output is a **face-iteration depth signature** —
a `List Bool` recording the cup value at each iterated middle-
removed face:

```
step 0: cupList k l α β τ                    (τ of length L)
step 1: cupList k l α β (τ.eraseIdx k)       (length L - 1)
step 2: cupList k l α β ((τ.eraseIdx k).eraseIdx k)
...
step d: cupList k l α β (... d iterations ...)
```

Implemented as `selfRefIter (k l α β) (depth : Nat) (τ : List Nat)`
with the output length always equal to the fuel parameter.

### Codim correspondence

At `d = 5` (the DRLT count-Lens dimension), each admissible
bidegree `(k, l)` with `k, l ≥ 1` and `k + l ≤ 4` has a
**unique** firing configuration — the **boundary-endpoint pair**
`(α_e_front-k, β_e_back-l)` — that fires at depth bit
position `d - k - l`:

| Bidegree | Endpoint pair          | Codim = 5 - k - l | Firing bit |
|---|---|---|---|
| (1, 1)   | `(α_e 0, α_e 4)`       | 3 | 3 |
| (1, 2)   | `(α_e 0, β_e2 3 4)`    | 2 | 2 |
| (2, 1)   | `(α_e2 0 1, α_e 4)`    | 2 | 2 |
| (1, 3)   | `(α_e 0, β_e3 2 3 4)`  | 1 | 1 |
| (2, 2)   | `(α_e2 0 1, β_e2 3 4)` | 1 | 1 |
| (3, 1)   | `(α_e3 0 1 2, α_e 4)`  | 1 | 1 |

The firing depth bit equals the **codimension of the cup support
in Δ⁴**.  This is a count-Lens output: the firing depth IS a
finite-resolution Lens-label entirely determined by the
support codimension.

### Channel count — universal closed form

```
totalCupChannels d = binom (d - 1) 2
```

Concrete values:

| d | Channel count |
|---|---|
| 3 | 1  |
| 4 | 3  |
| 5 | 6  ← DRLT |
| 6 | 10 |

Proof by Nat induction + Pascal at column 2:
`binom (n+1) 2 = n + binom n 2`, combined with
`bidegreeCount d = d - 1`.

### Codim stratification at d = 5

```
6 = 3 + 2 + 1 = NS + NT + 1
```

where:
- Codim 1 (shallow, `k + l = 4`): **3 channels** = `NS`
- Codim 2 (middle, `k + l = 3`): **2 channels** = `NT`
- Codim 3 (deepest, `k + l = 2`): **1 channel** (saturation)

### Physical bridge to weak inverse-coupling

The codim-1 cup-self-reference channel count `NS = 3` matches
the `α_GUT` coefficient in

```
1/α_2 = 30 - 1/2 + 3·α_GUT
```

(per `lean/E213/Lib/Physics/Couplings/TripleCoupling.lean`).  The
3 codim-1 channels `{(1,3), (2,2), (3,1)}` ARE the structural
origin of the `3·α_GUT` correction.  This is a zero-parameter
structural derivation of the `α_GUT` coefficient.

The leading integer `30 = 6 · d = (cup-channels) · d = NS·NT·d`
factorises the cup-channel count out of `1/α_2`.

### Falsifiability contract

For each of the six bidegrees, the boundary-endpoint pair is
verified to be the **unique** firing configuration in the
indicator basis:

| Bidegree | Search space | Theorem |
|---|---|---|
| (1, 1) |  25 pairs | `basisDepth4Sig_unique_survivor` |
| (1, 2) |  50 pairs | `depth4Sig_1_2_unique_endpoint` |
| (2, 1) |  50 pairs | `depth4Sig_2_1_unique_endpoint` |
| (1, 3) |  50 pairs | `depth4Sig_1_3_unique_endpoint` |
| (2, 2) | 100 pairs | `depth4Sig_2_2_unique_endpoint` |
| (3, 1) |  50 pairs | `depth4Sig_3_1_unique_endpoint` |

Total: `325` decide-verified indicator basis pair signatures.
Any additional firing pair outside the boundary-endpoint
configurations would contradict the catalog.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Cohomology.Cup.LeibnizFinPureForm
cd lean && lake build E213.Lib.Math.Cohomology.Cup.SelfRefDepth
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Cup.LeibnizFinPureForm
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Cup.SelfRefDepth
```
