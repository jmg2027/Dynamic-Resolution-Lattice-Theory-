# G31 — Minimal Root via Trajectory-as-Witness

**Date:** 2026-05-05
**Author:** Mingu Jeong (insight: "편한 길은 213이 아니지")
**Formalisation:** Claude (Anthropic)
**Status:** Skeleton landed in
`Math/Analysis/DyadicSearch/MinimalRootLens.lean`; full
root-certificate (lower / upper / zero) pending monotone-polynomial
milestone (next).

---

## 0. Thesis

**The Intermediate Value Theorem in 213 is not an existential claim
but a typed protocol — `ConsistentOracle` — whose readout *is* the
root cut.  "Minimal root" emerges deterministically from the lens's
choice rule (always-prefer-left), not from any external decidability
hypothesis.**

This is G2 (trajectory-as-object) applied to bisection: the
locatedness assumption that haunts Bishop-style IVT is replaced
by a structural type-level commitment from the oracle.

---

## 1. The wrong path (rejected)

Two tempting framings, both of which collapse the trajectory:

  **(a) ε-δ approximation.**  ∀ m k, ∃ c, |f c| < 1/k at precision m.
  Requires sign-decidability at every refinement → forces
  `propext` via `Decidable` instance synthesis.  Not 213-native.

  **(b) Isolated-root hypothesis.**  Add `IsolatedRoot f` predicate,
  derive uniqueness, conclude exact `cutEq`.  Imports a
  classical-style assumption that can't be discharged from the
  Raw axiom set.  Not 213-native.

Both routes treat the bisection sequence as *evidence for* an
externally-existing point.  213 inverts this: the sequence *is*
the point.

---

## 2. The 213-native form

The lens-style answer reuses three already-closed pieces of
infrastructure:

  1. `DyadicBracket.bisectN` — recursive bisection driven by a
     Bool-valued `DyadicOracle`.  No `Decidable` instance, no
     `propext`.
  2. `ConsistentOracle db` — typed protocol carrying its own
     consistency threshold `thresholdN m k` and a proof that the
     midpoint cut is stable past the threshold.
  3. `CauchyCutSeq.limit` — explicit limit extraction from a
     stabilised cut sequence.

Composition:

```
  ConsistentOracle db ── toCauchyCutSeq ──► CauchyCutSeq ── .limit ──►
    Nat → Nat → Bool   =   the minimal-root cut.
```

The "always-prefer-left" rule is concretised as
`signedLeftOracle f := fun mid => f mid 0 1` — read f's cut at the
unit precision (m=0, k=1, the rational 0); `true` ↔ "f(mid) ≥ 0
in cut sense" ↔ go left.  No sign decision, no `Decidable` instance:
the Bool comes directly from f's cut representation.

---

## 3. What the IVTRoot certificate becomes

`IVTRoot` (defined in `DyadicSearch/IVT.lean`) packages
`(c, lower, upper, zero)`.  Under the trajectory framing:

  - `c := MinimalRootCut co` (the trajectory readout).
  - `lower, upper` will follow by structural induction on
    `bisectN` from bracket-monotone invariants
    (`leftCut` of subbracket ≤ `midCut` ≤ `rightCut`).
  - `zero` will follow from `dyadic_bracket_cauchy_modulus`
    (already strict ∅-axiom in
    `Math/Analysis/BracketCauchyModulus.lean`) plus the
    sign-preservation invariant of `signedLeftOracle`.

None of the three certificates require an external locatedness
hypothesis — they are *theorems* downstream of the
`ConsistentOracle` protocol witness.  The protocol carries its
own modulus; the lens carries its own monotone bounds.

---

## 4. First milestone (this commit)

Skeleton landed in
`lean/E213/Math/Analysis/DyadicSearch/MinimalRootLens.lean`:

  - `signedLeftOracle f` — the always-prefer-left oracle.
  - `signedLeftOracle_constTrue / constFalse` — sanity reductions
    to `alwaysTrue` / `alwaysFalse` (rfl-closed).
  - `MinimalRootCut co` — the trajectory readout via
    `ConsistentOracle.toCauchyCutSeq.limit`.
  - `MinimalRootCut_eq_at` — precision-stability theorem.
  - `MinimalRootCut_collapsed` — sanity: for a degenerate
    (numA = numB) bracket, the readout equals the constant
    midCut value.

All declarations strict ∅-axiom.  → closed-skeleton in
`Math/Analysis/DyadicSearch/MinimalRootLens.lean`.

## 5. Layer 3b — Resolution-residue → cutEq bridge

Closed in `MinimalRootLensMonotone.lean`.  The user's framing:
"부호 변화 불변량을 cutEq라는 렌즈의 언어로 번역."

  * `cutEq_zero_of_ratioCut_at_unit` — for any `RatioCut x` with
    `x 0 1 = true`, conclude `cutEq x (constCut 0 1)`.  Unit-precision
    sign + structural cut-coherence ⇒ global zero certificate.  This
    is the 213-native form of "value ≤ 0 at unit precision implies
    value = 0 globally" — finite-resolution observation closing into
    the cut-equality lens.

  * `IVTRoot.fromConsistentOracleRatio` — packages the four 213-axes
    into the full IVTRoot:
      1. `LocallyDeterminedData f` (modulus axis)
      2. `ConsistentOracle db` (trajectory axis)
      3. `RatioCut (f c)` (structural-coherence axis)
      4. `f c 0 1 = true` (finite-resolution residue axis)
    No additional hypothesis enters.  Lower / upper come free from
    the bracket-containment of Layer 3a; zero closes via the bridge.

The user's slogan: this is the structural equivalent of Bishop
locatedness made explicit.  Each axis is a typed datum supplied by
the caller, not a classical assumption embedded in the framework.

## 6. Layer 3c — Concrete instances + multi-policy lens framing

Closed in `UnitConsistentOracles.lean` (concrete instances) and
extended in `MinimalRootLens.lean` / `MinimalRootLensMonotone.lean`
(dual policy-lens scaffolding).  The user's framing:

> "정책적으로 무언가를 선택한다는 것 자체가 하나의 렌즈."
> ("The policy-choice itself is a lens.")

### 6a. Concrete `ConsistentOracle` instances (proof of inhabitation)

  * `unitAlwaysTrue_ConsistentOracle : ConsistentOracle unitBracket`
    — `alwaysTrue` oracle on `[0, 1]`; midCut converges to 0.
  * `unitAlwaysFalse_ConsistentOracle : ConsistentOracle unitBracket`
    — `alwaysFalse` oracle; midCut converges to 1.

Both **strict ∅-axiom**, with explicit threshold function
`N(m, k) = k`.  Closed-form analysis via `alwaysTrue_unit_midCut` /
`alwaysFalse_unit_midCut` + the `succ_le_two_pow` Cauchy modulus.
The `alwaysFalse` instance required the cleaner *4-line cancellation*
proof for `(2^(n+1) - 1) * k > 2^(n+1) * m` past `n ≥ k`.

These prove that `ConsistentOracle` is non-vacuously inhabitable
beyond the trivial collapsed case — the typed protocol *is*
instantiable.

### 6b. Dual policy lens

`signedLeftOracle` (default policy) is one of finitely many
candidate oracles.  Its dual:

  * `signedRightOracle f := fun mid => !(f mid 0 1)` — for the
    *opposite* sign convention (`f leftCut 0 1 = true`,
    `f rightCut 0 1 = false`, i.e., f *increasing*).  Together with
    `BracketSignChangeUp` + `bisectStep_signed_right_preserves_sign_change_up`
    + `bisectN_signed_right_preserves_sign_change_up` (all strict
    ∅-axiom).
  * `signedLeftOracle_eq_not_signedRightOracle` — the two policies
    are pointwise Bool-negations.  The meta-policy choice is a
    single Bool, **exposed as a lens**.

### 6c. The locatedness wall and how 213 dissolves it

The friend's hint was structurally illuminating:

> "isLocallyDetermined f가 말하는 게 — ∀ m k, ∃ N, ... 이 N이
> 존재하지만 m,k에 따라 달라져 ... ∃ N을 choose로 꺼내는 순간
> Classical.choice가 들어올 위험이 있어."

**The framework already dissolves this**: we use
`LocallyDeterminedData` (the *data form*, with explicit `N : Nat → Nat → Nat`
as a structure field), not `isLocallyDetermined` (the existential).
No `Classical.choose` enters anywhere — the modulus is constructive
data.  The "wall" is upstream of the 213 type system; once the
data form is chosen, the wall is bypassed by construction.

### 6d. The d=5 finite-policy enumeration argument

Mingu's deeper insight: in 213, `d=5` already commits the
modular/lens structure to a *finite* directional space.  Each
candidate oracle is a finite-cardinality choice within this space:

  * `(m', k')`-precision → query `f mid m' k'` returns Bool;
    finitely many "small" `(m', k')` give finitely many policies.
  * `signedLeft / signedRight / alwaysTrue / alwaysFalse / parity-based / …`
    are concrete representatives.

For any locally-determined f and bracket, the framework supports
**enumerating the policy lens** and proving consistency for each
(or for the meta-policy that picks the working one).  This converts
the "locatedness obstacle" into a finite combinatorial check.

**Bonus**: the modulus extraction `N(P, f, m, k)` (depth at which
policy P stabilises for f at precision (m, k)) becomes a
*quantitative resolution map* — "how much resolution does f need
under this policy?" — itself a lens on (f, P).

### 6e. What remains for the fully-general closure

The general-case construction of `ConsistentOracle` from arbitrary
`(LocallyDeterminedData f, BracketSignChange f db)` reduces to:

  1. Extract `N₀ := lf.N 0 1` (constructive — no `choose`).
  2. Past depth `db.lenNum * (something polynomial in N₀)`, the
     bracket-Cauchy modulus + LDD propagation give midCut
     stabilisation at unit precision.
  3. Bootstrap from unit-precision stability to all-precision
     stability via the `RatioCut`-bridge (Layer 3b) applied to
     each refined query.

Step 2's recursion termination is precisely where the d=5 finite
combinatorics enters — the "policy ladder" is bounded above by a
finite count of trajectory-bit configurations.

Closing this in Lean is the next concrete milestone.  Architecture
already established: each axis is a typed datum, no classical
assumption enters, and the policy enumeration is within the
finite-lens framework already formalised in `Meta.UniversalLens.*`.

### 6f. First general ConsistentOracle beyond unitBracket

`numA_zero_alwaysTrue_ConsistentOracle (db : DyadicBracket) (h : db.numA = 0) : ConsistentOracle db`
**generalises** `unitAlwaysTrue_ConsistentOracle` from
`unitBracket = (0, 1, 0)` to **any** `(0, B, E)`-shaped dyadic
bracket.

  * `alwaysTrue_zero_midCut` — closed form: midCut at depth n =
    `dyadicCut db.numB (db.expE + n + 1)`.  Generalises
    `alwaysTrue_unit_midCut`.
  * `Bk_le_two_pow_E_succ_mul` — quantitative modulus extraction:
    for `n ≥ B*k`, `m ≥ 1`, `B*k ≤ 2^(E+n+1)*m`.  Bonus axis:
    *resolution map* `N(B, k) = B*k` quantifies "how much
    bracket descent is needed at precision (m, k)".
  * Threshold: `N(m, k) = db.numB * k` (specialises to `k` for
    `unitBracket`).

All strict ∅-axiom.  The `numA = 0` shape is the canonical
"leftmost-pointing" bracket family; analogous results hold for
`numB = 2^E * c` shapes (rightmost-pointing) under `alwaysFalse`.

**Architectural takeaway**: `ConsistentOracle` is *uniformly*
constructible across an entire family of starting brackets via a
single generalised proof.  This validates the policy-lens framework
beyond the unit case and provides the template for the fully-general
`(LDD f, BracketSignChange) → ConsistentOracle` closure.

### 6g. Morphism collapse — `signedLeftOracle f` ↦ `alwaysTrue`

Closed in `SignedLeftCollapse.lean`.  Mingu's framing:

> "f가 특정 패턴을 만족할 때 signedLeftOracle이 alwaysTrue로
> 환원되는 조건을 명시화하는 것은, 복잡한 함수 연산을 단순한
> 상구조(Image)로 붕괴시키는 213 특유의 'Morphism 붕괴'를 보여주는
> 핵심 작업."

  * `CollapseCondition f db := ∀ k, f (dyadicCut db.numB (db.expE + k + 1)) 0 1 = true`
    — the structural pattern: f is `true` at unit precision on the
    alwaysTrue-trajectory's midCut sequence.
  * `signedLeftOracle_eq_alwaysTrue_traj` — under collapse + `numA = 0`,
    the trajectory under `signedLeftOracle f` is **structurally
    identical** to the trajectory under `alwaysTrue`.  Proof by
    induction on n; collapse propagates to `db.leftHalf` via depth-shift.
  * `signedLeft_collapseTo_alwaysTrue_ConsistentOracle` — the
    derived ConsistentOracle for `signedLeftOracle f` reduces
    structurally to the alwaysTrue ConsistentOracle (Layer 3c §6f).

**Reductionist closure**: f's complex computation collapses to a
*constant Bool image* once its unit-precision pattern aligns with
the bracket's natural alwaysTrue trajectory.  This is the 213
realisation of categorical morphism reduction at the lens layer —
no f-specific consistency proof required, only the discharge of
`CollapseCondition`.

The closure pattern: once `CollapseCondition` holds, the
ConsistentOracle is automatically the alwaysTrue one.  Combined
with Layer 3b's `cutEq_zero_of_ratioCut_at_unit`, the IVTRoot
follows mechanically — given (LDD f, RatioCut on f's image, collapse
condition, and unit-precision sign), the framework synthesises the
full root certificate at strict ∅-axiom.

**Concrete impact**: for any f satisfying CollapseCondition on a
numA = 0 bracket, IVT becomes a *one-line corollary* via
`signedLeft_collapseTo_alwaysTrue_ConsistentOracle` plumbed through
`IVTRoot.fromConsistentOracleRatio`.  No additional sign-change
analysis needed.

### 6h. Composition closure — `(Nat, +)`-graded structure

Mingu's framing: "CollapseCondition이 합성에 닫혀있으면 — IVT가
단독 정리가 아니라 합성 가능한 도구가 돼.  E''이 어떻게 결정되는지가
핵심이야 ... E'' = E + E' 형태로 나올 가능성이 있어."

  * `CollapseConditionAt f B E` — `(B, E)`-parameterised form
    decoupled from `DyadicBracket`'s structure overhead.
  * `CollapseCondition_eq_at` — `Iff.rfl`-equivalence with the
    bracket form.

**Resolution monotonicity** (`(Nat, +)` action):

  * `CollapseConditionAt_resolution_shift` —
    `CollapseConditionAt f B E → ∀ d, CollapseConditionAt f B (E + d)`.
    Selecting the suffix at `E + d + 1` of the original sequence;
    establishes a canonical `(Nat, +)`-filtration with `E ↦ E + d`
    an inclusion.

**Composition with resolution shifters** (Mingu's `E'' = E + E'`):

  * `IsResolutionShift g E_g := ∀ M E m k, g (dyadicCut M E) m k =
    dyadicCut M (E + E_g) m k` — g zooms dyadic resolution upward
    by `E_g`.
  * `CollapseConditionAt_compose_resolution_shift` — given
    `LocallyDeterminedData f`, `IsResolutionShift g E_g`, and
    `CollapseConditionAt f B (E + E_g)`, conclude
    `CollapseConditionAt (f ∘ g) B E`.  Requires LDD on f to
    bridge pointwise equality of `g (dyadicCut M E)` and
    `dyadicCut M (E + E_g)` into equal f-values at unit precision
    (no funext).

**The grading**: `f` and `g` carry resolution-grade integers; their
composition's grade is the sum.  `f ∘ g` collapses at coarser
resolution `E` *iff* `f` collapses at finer resolution `E + E_g`.
The user's `E'' = E + E'` reads as "to collapse the composition at
`E_db`, require the upstream `f` to collapse at `E_db + g`'s shift".

**Architectural impact**: CollapseCondition is now a *graded
monoid module* over `(Nat, +)`, with composition closing under the
graded action.  This makes IVT a **composable tool** — chains of
resolution-shifters can stack, with the total resolution requirement
being additive.  The framework now supports the kind of "resolution
arithmetic" that ODE and PDE local-solution constructions require.

**Bonus**: arbitrary function composition (without ResolutionShift
hypothesis) is *not* generally closed — counter-examples exist
(e.g., negation ∘ negation = id, which has different collapse
structure).  ResolutionShift is the *minimal sufficient
structural hypothesis* that makes the grading work.
