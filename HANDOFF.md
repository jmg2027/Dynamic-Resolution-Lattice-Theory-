# Session Handoff — 2026-05-18

## Branch
`claude/review-lens-emergence-path-ZtS3A` — pushed, 44+ commits.
Latest: `e05d34b9 Lens/Number umbrella — add Int213`.

## This session — sprawl cleanup + size compression + orphan surfacing

### Pass 1–3: singleton sub-cluster dissolution
  - `Lib/Math/Atomicity/` (1 file) hoisted to top level.
  - Polynomial213 restructure (parent-as-Core + proper 3-file
    sub-cluster); Geometry filename normalisation
    (`Nat213AlgebraicGeometry` → `AlgebraicGeometry`, etc).
  - `DyadicFSM/Legendre/Legendre.lean` singleton dissolved
    (16 consumers updated); `Real213/Cauchy/ChainToCut.lean` →
    `Real213/ChainToCut.lean`; `Analysis/ChainCauchy.lean` KO →
    English docstrings.

### Size compression
  - 4 `Z*Instance.lean` singletons → one `ConjugationInstances.lean`
  - 3 `ZOmega{X}OrderDist` pairs merged into their `X.lean`
  - `HasModulusBoundsExtra` folded into `HasModulus`
  - `Meta/Int213/Instance.lean` folded into `Meta/Int213.lean`
  - `Theory/CDDouble/{UniversalOrder4,GenericLiftDemo}` → one file
  - `DyadicFSM/Archive/{EdgeSignature,SubwordComplexity}` → one file
  - `Theory/Raw/{Signed,Hom}` → `FoldSwap.lean`
  - 3 ZSqrtMinus2 finding files → `ZSqrtMinus2Findings.lean`

### Cleanup
  - Dead `Cohomology/CupAW/BilinearFunc.lean` (empty placeholder)
    deleted; 5 dead imports stripped.
  - 3 mis-researched capstones deleted: `Extras/ResidualPass2Capstone`,
    `Extras/ResidualPass3Capstone`, `Extras/SkeletonCleanup` — all
    imported non-existent `Multivariable.Stokes{2D,3D,4D}` modules
    and never built clean.

### Umbrella orphan surfacing
  Many umbrellas had orphan sub-files (reachable transitively but
  invisible to umbrella readers).  Now surfaced explicitly:
  - `Modulus`         + 3 files (incl. `G40Capstone` chain)
  - `Extras`          + 3 files (`HoeffdingFiniteN`,
                                  `AggregatorCapstone`, `RealLogCapstone`)
  - `Linalg213`       + `PhaseChiralBridge`, `Gap` sub-cluster
  - `Topology`        + `ContinuityArith`
  - `Logic`           + `CutElimination`
  - `DyadicFSM/Pell`  + `ProperMod` (per-prime bundle)
  - `Lens/Number`     + `Int213` (was listed as 'Future')

Net file count reduction: ~22 files removed.  All theorems remain
∅-axiom; default `lake build E213` (framework rings) clean
throughout.

## What this branch delivered

A full traversal of the lens-emergence-path roadmap
(`research-notes/2026-05-18_lens_emergence_path.md` §5), plus the
related §9.4 syntactic-internalisation programme.

  - **Option C — Raw-side arithmetic deleted**: ℕ₊ is the
    projection of `Lens.leaves.view : Raw → Nat`, not a quotient
    of `Raw`.  `Raw.lean` is slim (chart structure only);
    `Chain.lean` is a Raw-subtype carrier whose operations route
    through `Nat`; `Bridge.lean` exposes the value-level
    homomorphism via Peano arithmetic.  Downstream
    `Lib/Math/Real213/Cauchy/ChainToCut.lean` migrated.  ~600 net
    lines deleted.
  - **Option D — chart-explicit framework**: `ChartGeneral.lean`
    parameterises Method A over any `(r₀, r')` with `r₀ ≠ r'`;
    full chart-invariance theorem `value (chartChain ...) = value
    r₀ + n * value r'`.
  - **Option E — internal congruence (generic)**:
    `Theory.Raw.Congruence` + `Lens.Congruence` give the
    `Eqv (gens) ↔ L.equiv` biconditional for any lens.  The §2.6
    quotient-style ℕ₊ candidates are abandoned — different
    parenthesisations are *structurally distinct* Raws (witnessed
    by `Theory.Raw.ParenthesizationDistinct`), so forcing
    associativity erases content.
  - **§9.4 syntactic internalisation L2 + L3**:
    `Lens.SyntacticInternalization` realises a 7-glyph alphabet
    (each glyph → distinct Raw) plus a Polish-prefix parser /
    printer with a fully-proved universal round-trip
    `∀ t, parseTree (printTree t) = some t`.

## Verification state

```
lake build (full tree)                       ✔ clean
```

All new symbols PURE.  No `propext` / `Quot.sound` /
`Classical.choice` / `omega` / `Mathlib` introduced.  Standard
`List.{append_assoc, append_nil, length_append}` carry `propext`;
`E213.Tactic.List213.{append_nil, append_assoc, length_append}`
provides the propext-free replacements as a reusable utility.
`simp [...] at h` in impossible branches replaced with
`Option.noConfusion h`.  `Nat.sub_add_cancel` replaced with
`Nat.succ_pred_eq_of_pos`.

Key axiom-audit counts (post-code-development):
  - `Lens/Number/Nat213/Chain.lean`             13 PURE (+ 3 parent)
  - `Lens/Number/Nat213/ChartGeneral.lean`       6 PURE
  - `Lens/Number/Nat213/ChainCoreBridge.lean`    5 PURE (+ `Chain.ext_val`)
  - `Lens/Number/Nat213/Bridge.lean`             7 PURE
  - `Lens/Number/Nat213/Raw.lean`               13 PURE (+1 `numeral_injective`)
  - `Theory/Raw/Slash.lean`                      hosts `Raw.slash_ne_right` (PURE)
  - `Theory/Raw/Congruence.lean`                 2 PURE
  - `Theory/Raw/ParenthesizationDistinct.lean`   2 PURE
  - `Term/Internal/Tree/Levels.lean`             hosts `Tree.leaves_pos` (PURE)
  - `Meta/Tactic/List213.lean`                   3 PURE
  - `Lens/Congruence.lean`                       4 PURE
  - `Lens/SyntacticInternalization.lean`        21 PURE

## Open work (genuinely remaining)

### 1. KO docstring backlog
`Peano.lean`, `Bridge.lean` (now English), `Raw.lean`, `Chain.lean`,
`NumberingSystem.lean`, `RawCut.lean` — already English.
Remaining KO content in `Lens/Number/Nat213/`: `Lenses.lean` (2 lines —
verbatim user quote, rule-compliant), `AtomicityCorrespondence.lean`
(2 lines — verbatim quote, compliant).  No further translation
needed in this directory.

Out-of-scope checks worth doing in a future pass: `Lens/Bool213/`,
`Lib/Math/Real213/`, `Lib/Math/Analysis/` may still have KO
docstrings.

### 2. Tower / downstream audit
`Lens/Number/Nat213/Tower/*` (NatPairToInt, NatPairToQPos,
NatTripleToZ2) — build clean indicates no breakage from the Option
C refactor, but a confirmation pass examining whether any rely on
the deleted `Bridge.toRaw_add` / `value_add` / `leavesCountRaw_*`
would be reassuring.  No active failures.

### 3. Bool213 architectural review
`Lens/Bool213/Raw.lean` keeps a Raw-internal `booleanProj`
(legitimately — Bool213's `{T, F}` canonical form *is* the Raw
image).  Comment references to the deleted Nat213
`leavesCountRaw` have been cleaned (commit `b99fb3eb`).  No further
work currently planned.

## Anchor docs (next session start)

- `CLAUDE.md` (top) — boot sequence
- `seed/AXIOM/07_self_reference.md` §8.4 — dichotomy guide
- `seed/AXIOM/09_chart_relativity.md` — chart-relativity chapter
- `research-notes/2026-05-18_lens_emergence_path.md` — long-form
  exposition of the lens-emergence reasoning
- `lean/E213/Lens/Number/Nat213/INDEX.md` — current Nat213 layout
- `lean/E213/Lens/SyntacticInternalization.lean` — §9.4 realisation
