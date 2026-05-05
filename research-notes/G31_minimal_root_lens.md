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

## 6. Layer 3c (next)

Discharge axes (3) and (4) under stronger hypotheses on f:
  * `RatioCutPreserving f` ⇒ axis (3) for `f c` whenever `c` is
    `RatioCut` (the trajectory readout's RatioCut closure is
    itself a Layer 3c subgoal — depends on consistency uniformity
    across precisions).
  * Combined with `BracketSignChange` n-step preservation
    (Layer 2) + LDD-stability at unit precision ⇒ axis (4).

The remaining work is the construction of `ConsistentOracle` from
(LDD + BracketSignChange) — the existence of the typed protocol
witness for any sign-changing locally-determined f.  This requires
showing the trajectory's midCut sequence is Cauchy, which composes
the `dyadic_bracket_cauchy_modulus` (already strict ∅-axiom) with
LDD-stability at every (m, k).
