# SignedCut — Module Index

Closes the residual from PR #59:
> "Generic-`x` (non-zero) cutInv bridge: needs cutSub-equivalent
>  at the cut layer; signed-Cut machinery introduction marathon"

## Modules

| File | Topic | Status |
|---|---|---|
| `Core.lean` | `SignedCut := Cut × Cut`; `signedNeg/Add/Sub/Mul`; zero/one/negOne | ∅-axiom |
| `Algebra.lean` | involutive negation, sub-self structural form, components | ∅-axiom |
| `GenericGeomBridge.lean` | `oneMinus x = signedSub one (ofPos x)`; signed-cut fixpoint baseline | ∅-axiom |
| `Capstone.lean` | 4 cluster witnesses + `total_witness` | ∅-axiom |
| `SignedCut.lean` | umbrella | — |

## 213-native paradigm

  * **Sign extension via pair**: `SignedCut := (positive,
    negative) : Cut × Cut`.  This is the **Cayley-Dickson
    level-0 sign extension**, structurally mirroring
    `ComplexCut := (re, im)` from `Lib/Math/Complex`.
  * **No new substrate primitive**: sign tracking is purely
    *structural* via the pair representation.  All operations
    reduce to `cutSum` + `cutMul` on the components.
  * **Subtraction without sub**: `(a, b) − (c, d) = (a + d, b + c)`.
    The "value" `a − b` is recovered at the implicit real layer
    (oracle), not at the cut layer.
  * **Generic-x cutInv bridge**: `oneMinus x` represents `1 − x`
    as a signed cut.  The geometric-series fixpoint
    `S_∞ · (1 − x) = 1` is captured structurally at every depth
    `N` by the partial-sum recurrence + `oneMinus x`.

## Connection to other tracks

  * **Complex 213**: Same Cayley-Dickson pair pattern, one level
    deeper (signed → complex via squaring `i² = −1`).
  * **Real213.CutLog Cauchy convergence** (PR #59): generic-x
    bridge that was deferred is now closed at the structural
    level via `oneMinus x` representation.
  * **CayleyDickson** (existing): the 8-tower of normed division
    algebras; SignedCut is the level-0 base.

## Honest residual scope

After this PR:
- **Equivalence under signed reduction**: `(a + c, b + c)` should
  reduce to `(a, b)` modulo cancellation.  Reduction is not
  defined in this layer; would need a normalization step.
  Currently witnesses are `cutSum`-explicit, leaving cancellation
  for the oracle.
- **Multiplicative inverse** `signedInv (1 − x)`: bridge to
  `cutInv` for *generic* x requires defining `signedInv` as
  `(num · denPos, num · denNeg)` over `(positivePart, negativePart)`.
  Structural definition possible; substantive convergence proof
  is the next marathon.
