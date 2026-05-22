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

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Cohomology.Cup.LeibnizFinPureForm
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Cup.LeibnizFinPureForm
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Cup.LeibnizFinGeneral
```
