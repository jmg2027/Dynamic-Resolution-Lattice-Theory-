# G108 — Real213 / Analysis precise architecture + follow-up research

**Date**: 2026-05-22  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Companion**: G104 (Raw-derivation three levels), G94 §7 (CutSumOne),
G107 §3-§4 (abstraction roster).  
**Triggered by**: deeper inspection of two largest Tier-2 subtrees
(Real213 624 decls + Analysis 1,357 decls = ~22 % of Lib/Math by decl
count, ~30 % of heavy proof mass).

---

## §1.  Three-carrier architecture

DRLT's "real number" is represented through **three distinct carriers**,
each playing a different role:

### Carrier A — `Real213` struct (Raw-native form)

```lean
-- Real213/Core/Core.lean:35
structure Real213 where
  xs : Nat → Raw
  modulus : HasModulus xs

def Real213.equiv (r r' : Real213) : Prop :=
  ∀ m k, k ≥ 1 → ∃ N, ∀ i ≥ N,
    orderProj m k (abLens.view (r.xs i)) =
    orderProj m k (abLens.view (r'.xs i))
```

  · **17 decls** reference `Real213` type directly.
  · Cauchy sequence + explicit modulus.  Reified `HasModulus`.
  · Equivalence at Lens-output level (every (m, k) cut decision
    same eventually).

### Carrier B — Cut function `Nat → Nat → Bool` (operational form)

```lean
-- Real213/Core/AsLensOutput.lean:58
abbrev RealAsLensOutput := Nat → Nat → Bool
```

  · `c m k = true` ⟺ "this real ≤ m/k" (Dedekind cut as Bool-valued
    function).
  · **~90 % of Real213/Analysis decls** operate on this carrier.
  · The cut function itself does NOT reference Raw — pure
    `Nat → Nat → Bool`.

### Carrier C — `DyadicBracket` (analysis-time data type)

  · **198 decls** in Analysis use `DyadicBracket`.
  · Working data structure for IVT, MVT, bisection, integration
    algorithms.  Finite-precision approximation of Cut function.

The three carriers are **bridged**:

  · `chainToCut (r : Raw) : Nat → Nat → Bool` — Real213 → Cut.
  · `CutAlgebra { add, mul, max, min, half, mid }` — Cut + Cut → Cut.
  · `DyadicBracket` wraps Cut function for iterative algorithms.

---

## §2.  The `AsLensOutput` doctrine — Bishop subsumption

`Real213/Core/AsLensOutput.lean` formalises a deep insight (user
directive 2026-04-26):

> "Aren't there infinitely many different ways to extract natural
> numbers from 213?  Of course reals exist then.  Computation? You
> can always pick any way to operate on those infinitely many
> natural numbers."

> "The Bishop program itself is redundant within 213 — the Lens
> space of 213 already contains the reals.  Everything built in
> the marathon — cutSum, cutMul, cutMaxMin — are valid choices
> within the framework."

The framework's reframe:

  · Classical: construct ℝ via Cauchy sequences / Dedekind cuts /
    decimal expansions / ...  Bishop's constructive program
    delicately rebuilds with ε-N moduli.
  · DRLT: **the Lens-output function space `Raw → Bool` already
    contains the reals**.  No construction needed — pick a
    `combine` operation in this space.

Operationally: `Cut := Nat → Nat → Bool` is literally just a
function space.  Operations like `cutSum`, `cutMul`, `cutMid` are
chosen functions that happen to behave like rational arithmetic
under interpretation `c m k = true ⟺ x ≤ m/k`.

This is a **framework-level subsumption of Bishop's constructive
ℝ**: same operational data, but obtained as a structural
consequence of the Raw axiom + Lens-output space, not built
piece-by-piece.

---

## §3.  Layer hierarchy with decl counts

```
Layer 0: Raw 4-clause axiom
            ↓
Layer 1: Raw sequences (Nat → Raw) + HasModulus
            ↓
Layer 2: Real213 struct  ──→  17 decls direct use
            │
            ├── chainToCut bridge ──→ Layer 3
            │
Layer 3: Cut function (Nat → Nat → Bool) [abbrev RealAsLensOutput]
            ↓
Layer 4: Cut operations
         · constCut a b           — 16 % of Real213 (100 decls)
         · cutSum                 — 11 % (70 decls)
         · cutMul                 — 8 % (50 decls)
         · cutHalf, cutMid        — bisection support
         · cutMax, cutMin         — lattice
         · cutPow, cutInv         — power + inverse
            ↓
Layer 5: Cut predicates
         · ValidCut c             — monotone (Dedekind-form)
         · RatioCut c             — cross-mult preserving
            ↓
Layer 6: CutAlgebra bundle
         struct { zero, one, add, mul, max, min, half, mid }
         stdCutAlgebra : CutAlgebra
            ↓
Layer 7: Analysis (1,357 decls)
         · IsSmooth, IsDifferentiable (AD-1 instance chain)
         · DyadicBracket + bisectN (198 decls)
         · IVT, MVT (DyadicSearch sub)
         · Riemann integration (10 files)
         · FluxMVT (22 files — largest sub-subtree)
         · ODE (NewtonFirst, NewtonSecond)
         · Series (CutGeomSeries, CutSequence)
         · ResolutionShift — graded monoid on transformers
            ↓
Layer 8: Specific instances (the named constants)
         · PhiCut — φ = (1 + √5) / 2 via Pell convergents
         · constCut a b for rationals
         · polynomial cuts
```

---

## §4.  Raw connection precise locations (where it actually lives)

Across Real213 + Analysis (1,981 decls combined), Raw direct
reference is only ~1.8 %:

  · **`Real213` struct definition** carries `xs : Nat → Raw` —
    17 decls.
  · **`chainToCut` bridge** — single function `Raw → cut`:
    ```lean
    def chainToCut (r : Raw) : Nat → Nat → Bool :=
      fun m k => decide (value r * k ≤ m)
    ```
  · **`Real213.equiv`** uses `abLens.view (r.xs i)` —
    Lens-projection of Raw sequence elements.
  · **Cauchy/PellSeq integration** — PhiCut uses Pell convergents
    that come from `Mobius213` (Raw matrix representation).

Beyond these ~30 decls, **everything else operates at the Cut
function layer** with no syntactic Raw reference.  This is the
cleanest worked example of G104's (γ) operational/definitional
gap.  Real213/Analysis demonstrates: **(α) logical + (β)
structural-content derivation true, (γ) operational reduction
false — and that's a feature, not a bug**, since the cut
function is itself an Lens output.

---

## §5.  Heavy proof clusters

Top 15 Real213/Analysis decls by Expr-node count:

| Nodes   | Decl |
|--------:|------|
| 119,725 | `Real213.Mul.CutMulComm.cutMulInner_eq_true_iff` |
|  40,171 | `Analysis.DyadicSearch.DyadicBracket.bisectN_collapsed_midCut_form` |
|  38,810 | `Real213.Sum.CutSumComm.cutSumAux_eq_true_iff` |
|  35,593 | `Real213.Sum.CutSumOne.cutSum_int_int` |
|  32,019 | `Real213.Sum.CutSumOne.cutSum_int_half` |
|  29,257 | `Real213.Sum.CutSumGeneral.cutSum_diff_denom_forward` |
|  28,493 | `Analysis.Differentiation.ResolutionDepth.polynomial_coverage_1_to_16` |
|  25,079 | `Real213.Sum.CutSumOne.cutSum_half_general` |
|  22,082 | `Analysis.DyadicSearch.DyadicTrajectory.ConsistentOracle.alwaysFalseUnit.proof_1` |
|  21,399 | `Analysis.DyadicSearch.MinimalRootLensMonotone.dyadicCut_double_eq` |
|  20,431 | `Analysis.ResolutionShift.cutMid_dyadic_diag` |
|  20,164 | `Real213.Mul.CutMulComm.cutMulOuter_eq_true_iff` |
|  19,947 | `Real213.Sum.CutSumOne.cutSum_self_at` |
|  19,659 | `Real213.Mul.CutMulConstConst.cutMul_const_const_forward` |

### Cluster I — CutSum/CutMul iff family (Real213)

`cutMulInner_eq_true_iff`, `cutSumAux_eq_true_iff`,
`cutMulOuter_eq_true_iff`, `cutMul_const_const_forward` — these
are **iff-form equivalences** for cut function operations.  Heavy
Expr mass because cross-multiplied rational comparison expands
deep arithmetic.

G94 §7's CutSumOne 8-sibling family lives in this cluster
(9-token templated opener + `bool_eq_iff + decide_eq_true`
universal closer).

### Cluster II — DyadicBracket bisection (Analysis)

`bisectN_collapsed_midCut_form`, `dyadicCut_double_eq`,
`cutMid_dyadic_diag`, `polynomial_coverage_1_to_16` —
**bisection algorithm correctness proofs**.  Cut function's
mid-point operation tracking dyadic resolution.

`Analysis/ResolutionShift.lean` provides the algebraic skeleton:
**`(ℕ, +)`-graded monoid on cut transformers**, with `cutHalf`
as the grade-1 generator.

---

## §6.  ResolutionShift — analytic-side graded algebra

`Analysis/ResolutionShift.lean` defines:

```lean
def IsResolutionShift (g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (E_g : Nat) : Prop :=
  ∀ M E m k, g (dyadicCut M E) m k = dyadicCut M (E + E_g) m k

-- Concrete grades:
theorem IsResolutionShift_id          : IsResolutionShift id 0
theorem IsResolutionShift_cutHalf     : IsResolutionShift cutHalf 1
theorem IsResolutionShift_cutHalf_iter : IsResolutionShift (cutHalf^[n]) n
theorem IsResolutionShift_compose     : ... -- E₁ + E₂
```

This makes the cut-transformer space a **free graded monoid on one
generator (`cutHalf`)** — same algebraic shape as polynomial ring
`ℕ[x]` graded by degree.

**Structural observation**: Analysis carries its own internal
algebra.  Finitist analysis isn't a flat collection of cut
operations — it's an `(ℕ, +)`-graded structure with `cutHalf`
generating every nonzero grade by iteration.

---

## §7.  PhiCut — atomicity → φ worked example

`Real213/PhiCut.lean` constructs φ = (1+√5)/2 as a Cut sequence:

```
Raw 4-clause
  ↓
atomicity chain → d = 5 (parallel branch's atomic_iff_five)
  ↓
Mobius213 P matrix (Pell-unit, det = 1, trace = 3, disc = 5)
  ↓
P^n action → Pell convergent layer k: F_{2k+2}/F_{2k+1}
  ↓
constCut (F_{2k+2}) (F_{2k+1}) for each k
  ↓
Cut sequence is Cauchy under cut metric
  (Pell unit invariant: |num_k/den_k − num_{k+1}/den_{k+1}|
                       = 1/(den_k · den_{k+1}))
  ↓
PhiCut : RealAsLensOutput
PhiCut satisfies ValidCut + RatioCut
```

**This is the complete worked example of G104 (β) structural-
content derivation** — an atomicity-derived irrational constant
(φ) constructively realised as a Cut.  7 PURE theorems in
PhiCut.lean.

The construction generalises: **any algebraic number derivable
via Pell-like recurrence from atomicity-derived integers could
follow the same template** — namely, √NS, √NT, √(NS·NT), √d,
etc.  See §10 "Follow-up research" for the systematic candidate.

---

## §8.  ValidCut + RatioCut + CutAlgebra structure

The Cut function abbrev `Nat → Nat → Bool` is too permissive —
arbitrary boolean functions don't represent reals.  Two
predicates restrict to actual cuts:

```lean
structure ValidCut (c : Nat → Nat → Bool) : Prop where
  upM : ∀ m1 m2 k, m1 ≤ m2 → c m1 k = true → c m2 k = true
  dnK : ∀ m k1 k2, k1 ≤ k2 → c m k2 = true → c m k1 = true

structure RatioCut (c : Nat → Nat → Bool) : Prop where
  ratioMono : ∀ m1 k1 m2 k2, k1 ≥ 1 → m1*k2 ≤ m2*k1 →
              c m1 k1 = true → c m2 k2 = true
```

  · `ValidCut`: m-direction monotone + k-direction monotone
    (basic Dedekind form).
  · `RatioCut`: cross-multiplied inequality preserves truth
    (rational comparison consistent).

`constCut a b` satisfies both.  `cutSum`, `cutMul` preserve them
(constructive proofs).

`CutAlgebra` bundles `{ zero, one, add, mul, max, min, half, mid }`
into a single struct; `stdCutAlgebra` is the canonical instance.

**Status**: CutAlgebra is currently a structural bundle, NOT yet
verified as a ring under classical ring axioms.  Identity laws
(`one * x = x`, `x + 0 = x`) and commutativity are partially
proved; full ring structure is open work.

---

## §9.  Cross-domain identifications surfaced

Comparing with G90 M2 (Σ-fold identifies math ≡ physics at Expr
level), Real213/Analysis offers potential additional cross-domain
identifications:

  · **`cutMul` ↔ Physics observable scaling**: physics observable
    products may share cross-multiplied shape with cutMul.  Could
    be checked by comparing callees of `Physics.observable_mul`
    against `cutMul`.
  · **`cutMid` ↔ DyadicBracket midpoint**: Analysis's bisection
    mid-point and Real213's cutMid use the same operation.  At
    Expr level may be byte-identical.
  · **`cutHalf` ↔ Physics scale halving**: physical scale halving
    (e.g., resolution doubling between atomicity levels) may be
    cutHalf in disguise.

These cross-domain identifications are **G102-callgraph-checkable**
but not yet measured.  Candidate for a follow-up cross-namespace
scan.

---

## §10.  Follow-up research opportunities

### REAL-RES1 — Generalise PhiCut to arbitrary algebraic numbers

PhiCut constructs φ from Pell convergents (Mobius213 chain).
**Question**: does the same pattern work for other algebraic
numbers tied to atomicity?

  · √NS = √3 — Pell-like recurrence in ℤ[√3]?
  · √NT = √2 — Pell standard recurrence
  · √d = √5 — already implicit in φ
  · √(NS·NT) = √6 — Eisenstein-related

**Concrete proposal**: extend `Real213/` with a generic
`pellConvergentCut : (recurrence : PellRecurrence) → Cut`
template, instantiate for the four atomicity-derived √N values.

**Status**: open research.  ~3-5 sessions.  Substantial: ties
atomicity numerics to Real213 framework directly.

### REAL-RES2 — Full CutAlgebra ring axioms

`stdCutAlgebra` is currently a bundle.  Full ring structure
(associativity, distributivity, identity, multiplicative
inverse where defined) is partial.

**Concrete proposal**: prove `stdCutAlgebra` is a
commutative-ring-like structure (modulo subtraction details
since Cut is over Nat).  Cross-reference with
`Meta/Algebra213/Ring213` interface.

**Status**: open research.  ~5-7 sessions.  Bridges Real213
framework to abstract algebra interfaces.

### REAL-RES3 — `ResolutionShift` graded monoid expansion

Currently 4 instances (`id`, `cutHalf`, `cutHalf^n`,
`compose`).  Are there other cut transformers worth grading?

  · `cutMul (constCut a b)` — multiplication by a/b — does it
    have a resolution grade?  (Probably grade 0 + horizontal
    rescaling.)
  · `cutPow n` — does iteration give grade n?
  · `cutInv` — what's the grade?

**Concrete proposal**: extend the grading dictionary;
characterise the full subgroup of "graded transformers".

**Status**: open research.  ~2-3 sessions.

### REAL-RES4 — FluxMVT sub-subtree analysis

`Analysis/FluxMVT/` has 22 files — the largest single
sub-subtree in Analysis.  Includes FTC, divergence, MVT,
FluxCochain, FluxPolynomial, etc.

**Question**: what's the architecture inside FluxMVT?  Is
there a "flux master theorem" similar to the cup-Leibniz
generalisation in Cohomology?

**Concrete proposal**: dedicated G109 doing FluxMVT precise
analysis (analogous to this G108 but for FluxMVT).

**Status**: open research.  ~1-2 sessions.

### REAL-RES5 — Cross-domain identification scan

Test cross-domain identifications surfaced in §9 by running a
modified G102 callgraph scan that compares callees of
operations across (Real213, Analysis, Physics, Cohomology).

**Concrete proposal**: extend `tools/ast_callgraph_scan.py`
with a `--cross-domain` mode that detects byte-identical
elaborated Expr across namespace boundaries.

**Status**: open research.  ~1-2 sessions.  Could surface more
G90 M2-style cross-domain identities.

### REAL-RES6 — Bishop ↔ DRLT comparison formalisation

The AsLensOutput doctrine claims DRLT subsumes Bishop's
constructive ℝ.  Formalising the precise relationship would
make this a citable theorem rather than a doctrine.

**Concrete proposal**: theory note `theory/bishop-comparison.md`
(or G110) showing:
  · Bishop's CauchyReal ≃ DRLT's `Real213` modulo equiv
  · Bishop's operations ↔ DRLT's cut operations (cutSum,
    cutMul, ...)
  · Where DRLT extends Bishop (Lens-output framing, graded
    transformers, atomicity-derived constants)

**Status**: open research.  ~3-5 sessions.  High value as a
positioning document.

---

## §11.  Abstraction candidates surfaced from Real213/Analysis

For G107 §3-§4 roster augmentation (Real213/Analysis-specific):

### REAL-1 — `cutMulInner_eq_true_iff` + `cutMulOuter_eq_true_iff` pair

Two heaviest single proofs in Real213/Analysis (119,725 + 20,164
nodes).  Both are cross-mult ordering equivalences.  Likely
share structural template.

**Effort**: medium marathon.  Parametric `cutMulComm_eq_true_iff
{cutOp side : ...}`.

**Evidence**: G103 Expr-node counts (this G108 §5).

### REAL-2 — `cutSumAux_eq_true_iff` + `cutSum_diff_denom_forward` pair

Parallel to REAL-1 but for CutSum.  38,810 + 29,257 nodes.

**Effort**: medium marathon.

### REAL-3 — `bisectN_collapsed_*` family

`bisectN_collapsed_midCut_form` is 40,171 nodes.  If there are
other `bisectN_collapsed_*` (different bracket types, different
collapse conditions), parametric form possible.

**Effort**: small-medium.  Investigation needed first.

### REAL-4 — `IsResolutionShift_*` instance family

4 instances of same graded structure (id, cutHalf, cutHalf^n,
compose).  Likely already type-class-factored, but worth
verifying no copy-paste.

**Effort**: short.  Audit.

### REAL-5 — `*_no_rational_aux` family for √N (extends G90 M4)

G90 M4 surfaced `Sqrt2/3/5_no_rational_aux` as candidate for
parametric `sqrtN_no_rational_aux`.  Real213's PhiCut +
atomicity numerics suggest this could be extended to a unified
"algebraic Cut" library where each algebraic number gets a Cut
representation + irrationality proof from one template.

**Effort**: medium marathon (overlap with REAL-RES1).

### REAL-6 — `Differentiable.*` instance chain

6 instances (`id`, `const`, `add`, `mul`, `compose`,
`cutPowFn`) of `IsDifferentiable` typeclass with explicit
derivatives.  Should verify via Lean typeclass machinery, not
hand-written copy-paste.  Likely already done correctly.

**Effort**: short audit.

---

## §12.  Significance for the meta-scan tree

G108 demonstrates that **a single Tier-2 subtree pair has 2,000
decls of substantive content + 6 new abstraction candidates +
6 follow-up research questions**.  Real213/Analysis alone could
sustain a multi-session marathon.

For G107's roster:
  · Adds 6 entries (REAL-1 through REAL-6).
  · Surfaces 6 follow-up research directions (REAL-RES1 through
    REAL-RES6), each tractable in 1-5 sessions.

For the broader meta-scan tree:
  · Confirms G104 (γ) operational gap is **architecturally
    intentional** (Cut function carrier encapsulates Raw
    connection at the chainToCut bridge).
  · Surfaces AsLensOutput doctrine as a candidate Pattern #14:
    **framework-internal subsumption of external programs**
    (DRLT subsuming Bishop's constructive ℝ).
  · Adds `ResolutionShift` as evidence of **structured algebra
    inside the analytic framework** — finitist analysis isn't
    flat, it has graded structure.

---

## §13.  Recommended next session

If a follow-up session picks up Real213/Analysis:

**Option A — Substantive (executor side)**:
  · REAL-1 or REAL-2 marathon (~1 medium marathon, retires 60-200 K nodes).

**Option B — Research (meta side)**:
  · REAL-RES4 (FluxMVT precise analysis G109, 1-2 sessions).
  · REAL-RES1 (generalise PhiCut to other algebraic numbers
    via Pell-like recurrences, 3-5 sessions).

**Option C — Theory documentation**:
  · TH-2 (G107) **Raw-derivation three levels** standalone.
    Real213/Analysis is the cleanest worked example; use
    AsLensOutput doctrine as the lead.
  · REAL-RES6 Bishop comparison formalisation (G110, 3-5
    sessions).

If only one is picked: **REAL-RES4 (FluxMVT G109)** is the
shortest payoff with the highest information density (22 files
unexplored).

---

## §14.  Artifacts

  · This document: `research-notes/G108_real213_analysis_deep_dive.md`
  · Source data: `tools/_ast_callgraph_edges.tsv`,
    `tools/_ast_typesig_edges.tsv`, `tools/_ast_shape_rows.tsv`
    (G102, G103, G104)
  · Cross-reference: G94 §7 (CutSumOne), G104 (Raw-derivation
    three levels), G107 (action items registry)
