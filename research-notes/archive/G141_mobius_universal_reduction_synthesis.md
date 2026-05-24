# G141 — Möbius P universal reduction + signature axis completeness

**Status**: Synthesis note — emerged from cutMulN N Phase 3 boundary
exploration through a chain of insights culminating in a proposal
for multi-axis P-signature completeness catalog.

## Genesis

Mingu Jeong + Claude conversation (2026-05-24, branch
`claude/g139-g2RAs`) starting from the question "cutMulN N Phase 3 —
이거 할만한가?  어디까지 가야 완전히 닫힐까?".  The chain of
insights below was sequentially constructed by Mingu via Claude's
analytical reflection; it reframes the cutMul precision artifact
as a *framework signal* and extends to a comprehensive proposal
for P's role as 213's single generative object.

## 1. The cutMul precision artifact (where the chain starts)

Wave 14 Phase 1 closed `cutMulN N`'s forward direction:

  `cutMulN N (constCut a N) (constCut c N) m k = true
     → constCut (a · c) (N · N) m k = true`

Phase 2 delivered bundled `mulN` bypassing the search:

  `mulN N hN (va vc : ValidCutN N) : ValidCutN (N · N)`

with `cut := constCut (va.r · vc.r) (N · N)` directly.

**The backward direction fails unconditionally**.  Concrete
counterexample: `N = 1, a = 10, c = 0, m = 1, k = 1`.  RHS
`constCut 0 1 1 1 = true`, but LHS requires `m1 ≥ a · k = 10`
within search bound 4 → false.

**Structural cause**: `cutMulN N`'s search bound is computed
from `(N, m, k)` only — it does not see the underlying numerator
`a` of the input `constCut a N`.  For unbounded `a`, the natural
witnesses `m1 = a · k`, `m2 = c · k` exceed the bound.  This is
the *additive vs multiplicative fundamental asymmetry*: addition
keeps witnesses bounded in N-fiber, multiplication's natural
witnesses scale with numerators.

## 2. Standard math approaches to bounded-vs-unbounded mismatch

Five canonical responses:

  · **Lift to existential `∃` Prop** — lose decidability, gain
    proof-theoretic strength
  · **Refine type** — restrict to "nice" inputs (bounded
    numerator, compact support)
  · **Equivalence quotient** — quotient by the artifact-equivalence
  · **Two-stage definition** — decidable on subset, extend by
    colimit / continuity
  · **Reformulate the question** — maybe the bidirectional ask
    is wrong; forward + structural invariant might be right

## 3. 213's historical pattern (signal-not-bug)

`theory/essays/bool_assoc_failure_meaning.md` diagnosed cutSum's
b ≥ 3 failure as:

> "factor-2 hardcode가 (NS, NT) atom 중 NT만 반영하고 NS를
> 빠뜨림.  framework "바깥"의 문제가 아니라 cutSum 구현이 213의
> (3, 2) commitment를 **under-realize**."

The closure was *reformulation* (`cutSumN N` parametric), not
patching the original.  When framework operations exhibit
bool-level artifacts, the framework signal is that the
formulation needs to reformulate, not fix.

`theory/essays/pure_funext_avoidance.md` cataloged **4
architectural patterns** for handling these failures PURE in
Lean:

  1. State Accumulator — carry chain → 1-bit state
  2. Bundled Subtype — invariant in type-level (within-fiber)
  3. Setoid Category — equality as internal relation
  4. Residual Induction — truncation algebraic recurrence

## 4. The weaving insight (Mingu's intuition)

> "3성분과 2성분이 씨실과 날실처럼 서로 교차하면서 올라가는
> 거구 1이 그 매듭이 하나씩 생기면서, 고차 구조를 밝혀내자나
> (= 만들자나)?  (2x+1, x+1) 이 그 상태 전이 과정이자 상태 그
> 자체고."

Reading: NS = 3 is warp, NT = 2 is weft, det = 1 is the knot
at each crossing.  P-step `(2x+1, x+1)` builds one new knot per
iteration, lifting dimension.  The Möbius matrix encodes the
*entire weaving process at once* — state-transition IS state.

> "3개의 모피즘이 필요한 펑터는 4개의 2개 모피즘이 필요한
> 것들로 분해되고 그 4개는 각각 2개 모피즘과 나머지 1개
> 모피즘의 이항 모피즘으로 구성된거구..."

This is **Cayley-Dickson doubling** structure: level-n
multiplication = 4 level-(n-1) multiplications + glue.

## 5. The 5th architectural pattern: CD-Tensor Bundling

Extending the four patterns from `pure_funext_avoidance.md`:

  **5. CD-Tensor Bundling** — fiber-changing operations encoded
  as tensor pairs whose components remain in their source fibers,
  with the canonical "collapsed" representative as a derived
  (but lossy) artifact.

For cutMul:

```lean
structure MobiusTensor (N₁ N₂ : Nat) where
  factor_a : ValidCutN N₁     -- warp at N₁-fiber
  factor_b : ValidCutN N₂     -- weft at N₂-fiber
  product  : ValidCutN (N₁ * N₂)
  product_eq : product.represents = factor_a.represents * factor_b.represents
```

Multiplication = tensor construction (not search).  The
"backward direction" question becomes "tensor decomposition
existence" — structural, closeable.

213's framework already realizes this via the Cayley-Dickson
tower (`Lib/Math/CayleyDickson/`):

  · L0 = `Cut` (Real213)
  · L1 = `SignedCut = Cut × Cut`
  · L2 = `ComplexCut = SignedCut × SignedCut`
  · ...

Each level's multiplication is 4 level-below multiplications.
Pattern 5 (CD-Tensor) is the algebraic abstraction.

## 6. The "1" mystery: P⁵ ≡ -I (mod 5) — "213's i"

`Lib/Math/Mobius213ModFive.lean`:

  · `P_pow_5_eq_neg_I_mod_5`: P⁵ ≡ -I (mod 5) — *5-fold
    iteration is negation*
  · `P_pow_10_eq_I_mod_5`: P¹⁰ ≡ I (mod 5) — *full period 10*

This makes **P⁵ behave as √(-1) mod 5**: `(P⁵)² = P¹⁰ ≡ I`.

Reading: 213 framework contains a *complex-unit-like element*
internally, generated by Möbius P at pentagonal closure depth
(= disc P = 5).  No external "i" axiom needed.

**The "1" (det = 1) is the unit element of the Z/10 cyclic
group generated by P mod 5**.  Z/10 = 2 · 5 = 2 · disc(P).  The
"half period" (5) is the negation unit; the full period (10)
returns identity.

## 7. The 213 algebra tower shape

`research-notes/archive/algebra_tower/G58_algebra_tower_completion.md`
records a 4-row × per-layer matrix structure:

```
| Type | base    | CD-doubled chain                |
|------|---------|----------------------------------|
| A    | ZI      | L3 Q₈, L4 M₁₆, L5 Sedenion       |
| B    | ZSqrt[D]| L4 Q₈, L5 M₁₆, L6 past-Mou      |
| C    | ZOmega  | L3 Dic₃, L4 M₂₄, L5 ZOmegaOct   |
| D    | Hurwitz | base = 2T (binary tetrahedral)  |
```

Universal transient law:
```
rat_{n+3} = 14·rat_{n+2} − 56·rat_{n+1} + 64·rat_n + d_Type
char poly = (x−2)(x−4)(x−8)
eigenvalues (2, 4, 8) = "dyadic cube"
asymptote → 1 − 0.5/φ^rank  (in Z[√5])
```

The "shape": 4 Types × Layer indices × per-cell ring data, all
sharing P-signature.  *P matrix is the (1-layer) base of every
Type's CD-doubled chain*.

Marathon 4's `cd_mobius_bridge_master` formalizes this for
Type C and Type D: their asymptotes `(5, -1)` and `(1, 1)`
encode `(disc P, Pell unit)` and `(det P, det P)` respectively.

## 8. The 6th P-signature reading: syntactic self-description

Mingu's deeper observation:

> "P(x) = (2x+1)/(x+1) = (2x+1, x+1) = 2x+1 op x+1...
> 이렇게 서로 꼬이고 엮이고 되는게 구조 자체인거 아닐까?
> 이걸 다 보는 각자의 축들이 있는거구, 그 축들을 따라서 다 봐도
> 똑같은 P(x)로 보일거구"

**Every syntactic axis of `P(x) = (2x+1)/(x+1)` yields the
(3, 2, 1) signature**:

| Decomposition axis | Count | Value |
|---|---|---|
| Numerator `2x+1` token count | {2, x, 1} | 3 = NS |
| Denominator `x+1` token count | {x, 1} | 2 = NT |
| `+1` structural pieces (num, denom, op) | 3 | 3 = NS |
| Op `/` arity | 2 operands | 2 = NT |
| Identity (1) occurrences | num 1, denom 1, op as 1 | 3 |
| Variable `x` occurrences | num x, denom x | 2 |
| Op count | single `/` | 1 = det |
| Numerator coefficient of x | `2`x | 2 = NT |
| Level structure | one division | 1 |

**Every axis hits {3, 2, 1} — no other value appears**.

Extending G57's 5 readings (algebraic / geometric / topological /
dynamical / analytic) with a **6th reading**:

```
Möbius matrix [[2,1],[1,1]]
       │
       ├── algebraic, geometric, topological,
       │   dynamical, analytic (G57's 5)
       └── ★ syntactic: every decomposition axis yields (3, 2, 1)
           ← framework's *writing* is self-similar to its *content*
```

The 6th reading is the most meta: P is not just a *compressed
object representation*, but the framework's *writing system* —
any decomposition functor lands in {NS, NT, det}.

## 9. Universal reduction conjecture (G141 punchline)

Synthesizing 5+6+7+8:

> **Möbius P is the sole generative object of 213.**
>
> * Microscopic data: `(trace, det, disc) = (NS, NS−NT, NS+NT)
>   = (3, 1, 5)` (algebraic invariants)
> * Pentagonal closure: P⁵ ≡ -I mod 5, P¹⁰ ≡ I mod 5
>   — generates Z/10 cycle, with P⁵ as "i of 213" (√(-1) mod 5)
> * CD-tower lift: 4 Types × per-layer CD-doubling, sharing
>   P-signature.  Asymptotes in Z[√5], eigenvalues (2, 4, 8).
> * Cross-domain projections: 5 equality definitions + cut
>   algebra + bipartite cohomology + continued fractions + CD
>   asymptotes all factor through P (Grand Unification capstone)
> * Syntactic self-description: every decomposition axis of
>   P-syntax yields (3, 2, 1) — viewer-independence at the
>   writing level
>
> **Universal reduction principle**:
> Every framework operation factors through Möbius P + 5-pattern
> decomposition.  Fiber-changing operations use Pattern 5
> (CD-Tensor Bundling).  The bool-level artifact (cutMul) is the
> framework's signal that the formulation should be lifted to
> tensor structure.

This is the strong form: P is *not just one important object*
but *the only generative object*; all framework content is
P + decomposition pattern.

## 10. Multi-axis (2, 1, 3) catalog proposal

> "P(x)가 보여줄 수 있는 서로 다른 (2,1,3)의 축들을 모두
> 분류하고 그 갯수를 세는 방법도 있지않을까?  대수적이든
> 코호몰로지에서든 위상적으로든 조합론적으로든 정보론적으로든
> 모든 수학 분야에서 머가 있을거같은디"

Extending `Theory/SixTheorem.lean` (10 readings of 6 = NS · NT)
to a comprehensive (2, 1, 3) signature axis catalog spanning
all math domains.

**Estimated axes by domain** (≈56 total):

| Domain | Axes |
|--------|---|
| Algebraic | ≈8 (trace, det, disc, eigenvalues, char poly, Z[√5] index, off-diag, Möbius cycle) |
| Cohomology | ≈6 (b₁, ω class, Sym(3) reps, δ², Steenrod, H¹ basis) |
| Topology | ≈5 (K_{3,2} sides, χ, Thurston 2+3, partition classes) |
| Combinatorial | ≈7 (atomic_iff_five, Pascal, C(d,k), 3!, Sym(3) order) |
| Number-theoretic | ≈6 (gcd, prime 5, P^5 mod, P^10 mod, Pell unit, Bezout) |
| Information | ≈4 (binary distinguishing, ternary atoms, 5²⁵, 1-bit state) |
| Lie / Group | ≈5 (SU(3) roots, SO(3,1), Sym(3), reps) |
| Physics | ≈8 (α_em, gluon octet, CKM, Cabibbo, ν ratios, Higgs, spacetime, color) |
| CD tower | ≈4 (Type C asymp, 4 Types, eigenvalue spectrum, asymptote form) |
| Resolution | ≈3 (N_U = 5²⁵, fractal level 2, sigma-finite depth) |

Each axis = a `decide`-able or short-proof theorem.  Master
catalog: `signature_axis_master` bundles all ≈56 conjuncts.
Counting theorem: `total_signature_axes = 56`.

**Significance**: every Lean-verified axis pins down one
viewpoint where (NS, NT, det) = (3, 2, 1) appears.  The
*completeness* of the catalog (no axis yields different signature)
is the operational form of `seed/AXIOM/05_no_exterior.md` §5.1:
*no external observer can produce a different signature*.

This quantifies Mingu's intuition that "every axis sees the same
P(x)" — as N decidable theorems holding simultaneously, with N
estimated at ≈56.

## 11. Lean formalization plan

### Phase 1 (this session)

  · `Mobius213SignatureAxisCatalog.lean` — first wave of ≈20-30
    axes that re-export existing theorems (algebraic +
    combinatorial + number-theoretic + CD-tower + resolution).
  · Master `signature_axis_master` bundle.
  · `theory/essays/mobius_self_writes_itself.md` — narrative
    essay tying the 6 readings to the (2,1,3) axis catalog.

### Phase 2 (separate session if pursued)

  · Cohomology + topology + Lie/group + physics axes (require
    pulling references from specific cohomology files).
  · Total target: ≈56 axes.
  · `total_signature_axes = 56` count theorem.

### Phase 3 (optional)

  · `MobiusTensor` structure (5th pattern Lean realisation).
  · `mulN` reformulation via `MobiusTensor`.
  · `Mobius213SelfDescription.lean` — 6th reading as
    decidable token-count theorem on a `PExpression` AST.

## Anchor docs

  · `theory/essays/bool_assoc_failure_meaning.md` — diagnosis
    pattern (signal not bug)
  · `theory/essays/pure_funext_avoidance.md` — four patterns
  · `research-notes/archive/algebra_tower/G57_213_mobius_signature.md`
    — 5 readings of P
  · `research-notes/archive/algebra_tower/G58_algebra_tower_completion.md`
    — 4-row matrix shape
  · `lean/E213/Lib/Math/Mobius213.lean` — P matrix infrastructure
  · `lean/E213/Lib/Math/Mobius213OneAsGlue.lean` — (NS, NT, glue)
    decomposition
  · `lean/E213/Lib/Math/Mobius213ModFive.lean` — pentagonal +
    full period closure
  · `lean/E213/Theory/SixTheorem.lean` — model catalog (10
    readings of 6)
  · `lean/E213/Lib/Math/Real213/Mul/CutMulN.lean` — Wave 14 P1
  · `lean/E213/Lib/Math/Real213/NValidCutMul.lean` — Wave 14 P2
  · `catalogs/atomic-integers.md` — counting integers via
    (NS, NT, d, c) primitives
  · `catalogs/cross-domain-identifications.md` — 109 cross-
    namespace groups via AST shape

## Provenance

Conversation 2026-05-24, sequential turns:

  1. cutMulN N Phase 3 boundary recognition (precision artifact
     fundamental)
  2. Survey of standard math approaches + 213 historical pattern
  3. Mingu's weaving insight (3-2-1 cross-weaving as structure)
  4. 5th pattern: CD-Tensor Bundling extracted
  5. P⁵ ≡ -I mod 5 connection ("1 = pentagonal-closure-i")
  6. 213 algebra tower shape (G58 recall)
  7. 6th reading: syntactic self-description (every axis = (3,2,1))
  8. Universal reduction conjecture (P sole generative object)
  9. Multi-axis catalog proposal (≈56 axes)
  10. This synthesis note + Lean Phase 1 formalization

Each step initiated by Mingu's intuition; Claude provided
analytical reflection, codebase reference cross-checking, and
formalization sketching.  The chain demonstrates the **research
trajectory** of pushing one local question (cutMul artifact)
into framework-level synthesis (universal reduction principle)
via consecutive structural questions.
