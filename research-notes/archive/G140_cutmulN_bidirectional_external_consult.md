# G140 — cutMulN N bidirectional closure: external architectural consultation

## Context

This is a problem statement for external LLM (Gemini Pro / Claude
Opus / etc.) architectural consultation, following the pattern
of `theory/essays/pure_funext_avoidance.md` (where 4 architectural
patterns came out of one consultation cycle).

The 213 framework has a `Nat → Nat → Bool` cut representation
of real numbers, where `cx m k = true` means *"the represented
real ≤ m/k"*.  Arithmetic operations are **bounded Bool
searches** — they return `Bool` and are decidable by inspection
of a finite witness space.  This works perfectly for addition.
**Multiplication hits a structural artifact** that we believe
is fundamental, but want a second opinion before declaring it
unfixable.

## The problem

### Setup

**Definitions** (in `lean/E213/Lib/Math/Real213/`):

```lean
-- The canonical constant cut at ratio a/b
def constCut (a b : Nat) : Nat → Nat → Bool :=
  fun m k => decide (a * k ≤ b * m)

-- Pointwise cut equality
def cutEq (cx cy : Nat → Nat → Bool) : Prop := ∀ m k, cx m k = cy m k

-- The parametric N-aware addition (Wave 13)
def cutSumN (N : Nat) (cx cy : Nat → Nat → Bool) (m k : Nat) : Bool :=
  -- bounded search over m1 ∈ [0, N·m] checking
  -- cx m1 (N·k) ∧ cy (N·m − m1) (N·k)
  ...

-- The parametric N-aware multiplication (Wave 14 Phase 1)
def cutMulN (N : Nat) (cx cy : Nat → Nat → Bool) (m k : Nat) : Bool :=
  -- nested bounded search over m1, m2 ∈ [0, N²·(m+1)·(k+1)] checking
  -- cx m1 (N·k) ∧ cy m2 (N·k) ∧ m1·m2 ≤ N²·m·k
  ...
```

### What works (Wave 13: addition)

**`cutSumN_same_denom` is bidirectional**: for any `N > 0`, `a, c : Nat`,

```
cutSumN N (constCut a N) (constCut c N) m k = constCut (a + c) N m k
```

(pointwise equal as `Bool` functions, for all `m`, `k`).  This
closes additive algebra at the cut level.  Bundled `ValidCutN N`
inherits associativity, commutativity, and parametric closure
for all naturals `N ≥ 1`.

### What partially works (Wave 14 Phase 1+2: multiplication)

**Phase 1** (`cutMulN_const_const_forward`):

```
cutMulN N (constCut a N) (constCut c N) m k = true
  → constCut (a · c) (N · N) m k = true     -- FORWARD only
```

**Phase 2** (bundled `mulN`, bypass): define product structurally
at the `ValidCutN N` level by using the canonical `constCut`
directly:

```lean
def mulN (N : Nat) (hN : 0 < N) (va vc : ValidCutN N) :
    ValidCutN (N * N) where
  cut := constCut (va.represents * vc.represents) (N * N)
  represents := va.represents * vc.represents
  is_at_denom := cutEq_refl _
```

This **bypasses cutMulN's search** — algebra at represents level
via `Nat.mul_comm`, `Nat.mul_assoc`.

### The asymmetry — what FAILS

**The backward direction of cutMulN_same_denom is false**:

```
constCut (a · c) (N · N) m k = true
  → cutMulN N (constCut a N) (constCut c N) m k = true     -- ✗ FALSE
```

**Concrete counterexample**:

  · `N = 1, a = 10, c = 0, m = 1, k = 1`.
  · RHS: `constCut(10·0)(1·1) 1 1 = constCut 0 1 1 1 = decide(0 ≤ 1) = true` ✓
  · LHS: `cutMulN 1 (constCut 10 1) (constCut 0 1) 1 1`:
    - search bound = `1·1·(1+1)·(1+1) = 4`
    - Need `cx m1 1 = constCut 10 1 m1 1 = decide(10 ≤ m1) = true` for some `m1 ≤ 4`
    - But `m1 ≤ 4 → 10 ≤ m1` is **false** for all `m1` in range
    - cutMulN = **false**

Same artifact (with `cutMul`'s factor-2 bound) is documented in
`Mul/CutMulConstConst.precision_artifact_at_k3` (`a = 1, c = 1,
b = 2, m = 1, k = 3` case).

### The structural cause

When the *underlying numerator* `a` (or `c`) is larger than
`N²·(m+1)·(k+1)/k`, the natural witnesses `m1 = a·k`, `m2 = c·k`
**exceed the search bound**.  The bound is computed from `(N, m,
k)` only — the function `cutMulN N` receives `cx, cy` as *opaque
`Bool` functions*, so no access to the underlying `a, c`.

**This is fundamentally different from cutSum's situation**:

| Property | `cutSumN N` | `cutMulN N` |
|---|---|---|
| Fiber transform | `N → N` (preserves) | `N → N²` (grows) |
| Natural witness | `m1 ≤ N·m` | `m1 = a·k` (unbounded in `a`) |
| Search bound | `N·(m+1)·(k+1)` ≥ witness | `N²·(m+1)·(k+1)` ≱ witness |
| Closure | **bidirectional** at cut level | forward only |

### What we've tried

1. **Increase bound**: any *fixed* bound `f(N, m, k)` eventually
   loses to large `a` or `c`.  Cannot make `f` depend on `a, c`
   because `cutMulN N` doesn't see them.

2. **Divisibility hypothesis** `N ∣ k`: orthogonal to the
   problem.  Counterexample above has `N = k = 1`, so `N ∣ k`
   trivially holds.  Doesn't help.

3. **Pre-compute witnesses**: even knowing `m1 = a·k, m2 = c·k`
   would close the case, but `cutMulN N` operates on opaque
   cuts and cannot extract `a, c` from `cx = constCut a N`.

4. **Structural bypass** (Wave 14 Phase 2): define `mulN` at the
   bundled `ValidCutN N` level using direct `constCut(a·c)(N²)`
   as the cut field.  *Works but circumvents the question* —
   doesn't fix `cutMulN N`, just provides a different operation.

## The 213-native diagnosis

Per `theory/essays/bool_assoc_failure_meaning.md` (the analog
diagnosis for cutSum's earlier b ≥ 3 artifact):

> Factor-N hardcode under-realizes some algebraic commitment.
> The framework's signal is that the formulation needs to be
> reformulated, not patched.

For cutSum: factor-2 → factor-N parametric → bidirectional.
For cutMul: factor-N already parametric, yet artifact persists
because the underlying issue is **multiplication's fiber-
growing nature** (N → N²) combined with **unbounded-numerator
inputs**.

The 213 four patterns from `pure_funext_avoidance.md`:

  1. **State Accumulator** — carry chain → 1-bit state.
  2. **Bundled Subtype** — invariant in type-level (this IS
     `mulN` Phase 2).
  3. **Setoid Category** — equality as internal relation.
  4. **Residual Induction** — truncation-level recurrence.

Pattern 2 (Bundled Subtype) is what `mulN` (Phase 2) does — but
that's a *sibling operation*, not a closure of `cutMulN N`
backward.

## The question

Is there a 213-native architectural pattern (existing or new)
that closes `cutMulN N` **backward direction** without:

  (a) Changing `cutMulN`'s signature (must remain `Bool`-valued
      on opaque cuts);
  (b) Adding `propext` / `Quot.sound` / `Classical.choice`
      (would violate 0-axiom standard);
  (c) Reducing to `mulN`'s bundled bypass (that's a different
      operation, not a closure);
  (d) Restricting input domain to "bounded numerator" cuts
      (defensible but feels like surrender);
  (e) Adding `decide`-based unbounded search (would lose
      decidability).

If **no such pattern exists**, what is the cleanest way to
declare the precision artifact as a *structural feature* rather
than an open question?  The current candidate:

> The cut framework has TWO multiplications:
> (i) `cutMulN N` — bounded-search Bool-valued witness;
>     forward-direction certificate of products.
> (ii) `mulN` — bundled algebraic operation on `ValidCutN N`;
>     bypass the search, work at the represents level.
>
> They diverge only at "input numerator exceeds search bound" —
> the precision artifact — which is the framework's signal that
> bounded computation of products is not closed.  The
> bundled form is the canonical multiplication; the search form
> is a verification tool.

Is this an honest closure?  Or is there a better architectural
pattern we're missing?

## What an answer would look like

Concretely, we want either:

  (A) A new architectural pattern (5th to add to the four in
      `pure_funext_avoidance.md`) that *does* close
      `cutMulN N` backward — with a sketch of how it would
      apply, in PURE Lean.

  (B) A clear "this is fundamentally impossible because ..."
      with the mathematical statement of *why* (probably some
      cardinality / decidability argument).

  (C) A reformulation of the question: "you're asking the
      wrong thing.  The right closure statement is ..."

Any of (A), (B), (C) is useful.  We've spent ~3 hours pushing
on direct attacks and keep hitting the same wall (search bound
vs. unbounded input numerator).

## Anchor files

  · `lean/E213/Lib/Math/Real213/Mul/CutMulN.lean` — Wave 14 P1
    (cutMulN N definition + forward closure + cutEq congruence)
  · `lean/E213/Lib/Math/Real213/NValidCutMul.lean` — Wave 14 P2
    (bundled mulN bypass)
  · `lean/E213/Lib/Math/Real213/Mul/CutMulConstConst.lean` —
    standard cutMul's forward + precision_artifact_at_k3
  · `lean/E213/Lib/Math/Real213/Sum/CutSumN.lean` — Wave 13
    cutSumN (the analog that DOES close bidirectionally)
  · `lean/E213/Lib/Math/Real213/NValidCut.lean` — bundled
    ValidCutN N with addN (the analog that uses cutSumN)
  · `theory/essays/bool_assoc_failure_meaning.md` — cutSum's
    factor-2 artifact diagnosis (analog of present problem)
  · `theory/essays/pure_funext_avoidance.md` — the four
    architectural patterns
  · `STRICT_ZERO_AXIOM.md` — current PURE status (136 / 0)
  · `CLAUDE.md` "Hard rules" — 0-axiom standard, no Classical,
    no Mathlib, no `propext`, no `Quot.sound`

## What we do NOT want from consultation

  · Suggestions involving Mathlib imports (forbidden)
  · Suggestions involving `Classical.choice` / `propext` /
    `Quot.sound` (would falsify 213's axiom contract)
  · Generic "use Topos theory" / "use Setoid quotients"
    answers — we've considered these and rejected for reasons
    detailed elsewhere (`research-notes/G29_residue.md`,
    earlier conversation with Mingu about Topos rejection).

We want: 213-native architectural insight, in the style of the
four existing patterns.
