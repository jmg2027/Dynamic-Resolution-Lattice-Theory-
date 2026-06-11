# SignedCut — Module Index

213-native signed Cut layer via `SignedCut := Cut × Cut` pair.
35 files: 6 sub-clusters + top-level `DichotomyLadder.lean`
(Cayley-Dickson dichotomy ladder strict ordering).

## Sub-clusters

| Dir | Files | Topic |
|---|---|---|
| `Core/` | 10 | Core/Algebra/Inv/UnifiedGenericInv/Equivalence/Capstones (incl. MathClosureCapstone, MulRuleCapstone) |
| `CD/` | 6 | CD-doubling (Conjugation/LevelOps/MulRule/Norm/Tower{Capstone,Level}) |
| `Hurwitz/` | 4 | HurwitzDichotomy/ExactL1/Failure/NormProduct |
| `Level/` | 2 | G38/G39 CD-tower capstones |
| `Bridge/` | 5 | Bridge/Capstone + FanoK32Bridge/FanoPlane + GenericGeomBridge |
| `Octonion/` | 7 | Octonion + Quaternion mul rules + tables + NonAssociativity |

## 213-native paradigm

- **Sign extension via pair**: structurally mirrors `ComplexCut :=
  (re, im)` from `Lib/Math/NumberSystems/Complex`.  Cayley-Dickson level-0 sign
  extension.
- **No new substrate primitive**: sign tracking is purely
  *structural* via the pair representation.  All operations reduce
  to `cutSum` + `cutMul` on the components.
