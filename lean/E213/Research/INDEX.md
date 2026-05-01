# lean/E213/Research/ — exploratory + Real213 marathon

Research-tier work: Bishop-style real-analysis marathon, lens
metatheory exploration, kernel cardinality investigations, and
exploratory observations that fed into capstones.

## Layout (post-2026-05-01 reorg)

```
Research/
├── Real213/         ★ 181 files — Bishop analysis marathon (already organized)
├── CayleyDickson/   29 files — Cayley-Dickson construction tower
├── Lens/            32 files — lens algebra (joins, meets, factoring,
│                                Lattice, on-lens tower, leaf, etc.)
├── Cauchy/          14 files — Cauchy seqs (Wallis, Euler, Profinite,
│                                MonotonicBounded, GenericFamily, ...)
├── ModArith/        10 files — mod arithmetic + CRT (Bezout, GCD,
│                                Euclidean, lens-CRT, PureNatMod{3,5})
├── Kernel/          8  files — kernel space (cardinality LB,
│                                congruence, FourDistinct, IdLensEq,
│                                SwapInvariant, FreeAudit)
├── Instance/        8  files — type instances (Pair, Subtype, Sum,
│                                FunctionSpace, Reach)
├── Morphism/        7  files — Bool/Dist morphism (NotFold series,
│                                FoldStructured, BoolSqClassification)
├── Irrational/      6  files — Sqrt{2,3,5} irrationality proofs
├── Universal/       5  files — UniversalLens claim + factoring +
│                                QuotLens + Reflection
├── Leaves/          5  files — leaves analysis (depth, mod, parity)
├── Modulus/         4  files — HasModulus + StrongModulus + extras
├── Choice/          4  files — canonical choice + bootstrap
├── Diagonal/        3  files — diagonal classification + modulus
├── Raw/             3  files — Raw DecEq, Initiality, SwapSlash
├── Hyper/           3  files — Hyper213 + Tower + Padic
├── Refines/         2  files — refines chain + preorder
└── (flat root, 13 files):
    AxiomMinimality, AxiomMinimalityCapstone, CmpIndependence,
    ComplexityClass, IdempotentConstancy, IntHelpers,
    ParityXorIncomparable, ParityXorJoin, PrimeDescentObservations,
    Prism, ProdBelowId, PureNat, SemanticAtom
```

## Naming convention (post-reorg)

When a sub-cluster name appears as a prefix in a file name, the
prefix is dropped (e.g., `LensFactoring.lean` → `Lens/Factoring.lean`,
`ModJoinBezout.lean` → `ModArith/JoinBezout.lean`,
`Sqrt2IrrationalPure.lean` → `Irrational/Sqrt2Pure.lean`).

The `Real213/` and `CayleyDickson/` sub-trees were organized
earlier (Phase 3) and use their own internal naming.

## When to add a new file

Use the existing sub-cluster if the new file fits.  If it doesn't,
add at the flat root and revisit later when a cluster of related
files emerges.

## See also

  - `lean/E213/INDEX.md` — full library map
  - `Math/Cohomology/INDEX.md` — Math/Cohomology sub-cluster index
  - `research-notes/INDEX.md` — narrative research notes (not Lean)
