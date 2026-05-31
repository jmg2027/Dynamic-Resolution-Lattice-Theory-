# Completeness as a Relocated Operation — the algebraic/transcendental split

The standard construction of the real numbers makes **completeness
constitutive**: ℝ is *defined* as the completion of ℚ (Cauchy sequences
modulo null sequences, or the set of all Dedekind cuts), and then
characterised up to isomorphism as "the complete ordered field".
Completeness is the defining axiom — it is what is added to ℚ to get ℝ.

A consequence usually passed over in silence: `√2` and `e` enter on
*identical* terms.  Both are simply elements of a complete field.  The
construction shows nothing about how their constructive costs differ — an
algebraic number you can pin with a finite decision rule and a
transcendental you cannot are, definitionally, the same kind of thing.

This chapter records a different arrangement, realised in
`lean/E213/Lib/Math/Real213/`, in which **completeness is not in the
definition of a real at all**.  It re-enters only as one operation on
*sequences* of reals, and there it splits the reals sharply by where the
constructive cost actually lives.  Every claim below is a Lean fact,
∅-axiom (`#print axioms` clean), hence falsifiable per
`seed/AXIOM/08_falsifiability.md`.  Lean is the source of truth; this is
its mirror.

## 1. What a real is: a decision procedure, not a point

A Real213 value is a `ValidCut` (`Real213/Core/ValidCut.lean`): a
function

    c : ℕ → ℕ → Bool,    c m k  =  ⟦ x ≤ m/k ⟧

answering, at each rational probe `m/k`, whether the magnitude lies at or
below it — subject to two monotonicities (`upM` raising the numerator
preserves `true`; `dnK` lowering precision preserves `true` downward).

There is no hidden point `x` that `c` approximates.  `c` *is* the object;
what the real **is** is exhausted by what it answers.  Asking "what is
the number behind the cut?" imports an exterior the construction does not
have (`seed/AXIOM/05_no_exterior.md`): the pointing is the comparison
behaviour, and the comparison behaviour is all there is to point at.

This is what *tangible / 손에 잡힌다* means here — and it is worth
separating from a wrong turn the project already discarded.  Tangibility
is **not finiteness**.  An earlier framing tried to make reals concrete
by positing a largest resolution `N_U`, a universe-constant ceiling on
precision; that was an external dialer with no operand and is catalogued
as a failure mode ("Universe-constant framing").  The tangibility that
survives is **queryability**: for *any* probe `m/k` the cut returns a
definite bit in finite work, with no appeal to a completed totality.  A
real is graspable because you can interrogate it to arbitrary
precision — not because the precisions stop.

## 2. Completeness is a leaf of the import graph, not a root

That completeness is not constitutive here is a checkable fact about the
dependency graph, not a manner of speaking:

  - **The cut object needs no completeness.**  `Core/ValidCut`,
    `Sum/CutSum`, `Mul/CutMul`, `Core/CutPoset` — the type, arithmetic,
    and order — import nothing from `Analysis/CauchyComplete`.
  - **A named irrational needs no completeness.**  `PhiAsCut.phiCut`
    gives φ as a *closed-form decidable cut*,
    `phiCut m k := decide (k ≤ 2m ∧ 5k² ≤ (2m−k)²)`, with no Cauchy
    machinery anywhere beneath it.  φ is irrational and is written down
    directly as a comparison procedure, not obtained as a limit.
  - **Everything importing `CauchyComplete*` is downstream analysis** —
    bisection, Riemann integration, the `AbCutSeq` completion.  Nothing
    in the *definition* of a real, an *operation* on reals, or an
    *algebraic* real passes through it.

So completeness, in 213, is not what reals are.  It is one operation you
may perform on a sequence of cuts — take its limit — and its content is
the subject of the rest of this chapter.

## 3. The relocation: where completeness is actually load-bearing

Completeness is not eliminated.  It is moved to the one place genuine
non-constructivity lives, and made **visible as a hypothesis** instead of
hidden in a definition.  Three Lean files make the trichotomy exact.

### 3.1 The shared carrier — `AbCutSeq`

`Real213/AbCutSeq.lean`: **every monotone, positive-denominator sequence
of rationals is a Real213 cut.**  An `AbCutSeq` is a sequence `xs : ℕ →
Raw` that climbs (`IsAbMonotonic`) with positive denominators
(`IsAbPositiveB`).  From those two facts alone:

  - `cut n` (layer `n` as a Cut) is a `ValidCut` and `RatioCut`;
  - `cut_false_fwd` — a `false` reading **nests** forward (once the
    climbing rationals pass `m/k`, they stay past it);
  - `cut_eventually_const` — at any threshold with a `false`-witness the
    sequence is eventually constant (the per-`(m,k)` order-Cauchy fact);
  - `toCauchy` / `toCauchy_limit_valid` — *given a modulus*, the
    completed limit is again a `ValidCut`;
  - `limit_brackets` — the completed limit inherits any rational bracket
    its approximants establish.

This is more than any single constant: the cut representation is closed
under the limit operation for the whole class of climbing rational
sequences.  φ, e, π are then three instances of one structure.

### 3.2 Algebraic — completion is unconditional and redundant

`Real213/PhiAbCut.lean` makes φ an `AbCutSeq` (the even-indexed Fibonacci
convergents `fib(2n+2)/fib(2n+1)`; the monotonicity step **is** the
Cassini norm, `fib(2n+2)·fib(2n+3) + 1 = fib(2n+4)·fib(2n+1)` —
`cassini_mono_step`).  Because φ is algebraic, its order-Cauchy modulus
is **closed-form**:

  - `phi_cut_eventually_const` supplies `N(m,k) = 2k` with **no
    hypothesis** — past `2k` the convergent cut equals `phiCut m k`
    exactly (`FibCassiniNat.cs_eq_phiCut`);
  - `phiCompletion : CauchyCutSeq` is therefore a **closed term**;
  - `phiCompletion_limit_eq_phiCut` — completing the sequence recovers the
    closed-form `phiCut` on the nose.

For an algebraic real, completion is available unconditionally *and adds
nothing*: the limit was already writable as a finite decision procedure.
This is √2, the golden ratio, and their kin.

### 3.3 Transcendental — completion needs a hypothesis-modulus

`Real213/ExpLog/EulerCut.lean` (e = Σ 1/k!) and `PiCut.lean` (π/2 via
Wallis, π by doubling) are the *same* `AbCutSeq` carrier with the *same*
per-threshold facts.  Each constant is genuinely located:

  - e is pinned strictly inside `(8/3, 3)` at every tail layer
    (`eulerCut_in_8_3_to_3`);
  - π/2 inside `(7/5, 2)`, π inside `(14/5, 4)` (`piCut_in_14_5_to_4`) —
    the sharp lower bound from `W₂ = 64/45 > 7/5` by `decide` plus
    nesting.

You can compare e or π to **any** specific rational and get the bit.
What you cannot do — without leaving the falsifiability contract — is
hand over a *total* modulus `N(m,k)` covering every threshold at once.
That total object is the global order-Cauchy closure, and
`Cauchy/MonotonicBounded` (§180–194) refuses it deliberately: a case
split on "`true` at every `n`" versus "`false` at some `n`", quantified
over all `(m,k)`, is `LEM` — the constructive analogue of ZFC's
commitment to arbitrary subsets.  So `eulerCut`/`halfPiCut` complete via
`AbCutSeq.toCauchy` only with the modulus supplied as a **hypothesis**.

### 3.4 The trichotomy, stated

Same structure for φ, e, π — one carrier, `AbCutSeq`.  The only
difference is the modulus that completes it:

| Real             | Cut object     | Completion modulus                    |
|------------------|----------------|---------------------------------------|
| rational         | `constCut a b` | trivial (constant sequence)           |
| algebraic (φ, √2)| `AbCutSeq`     | **closed-form**, unconditional        |
| transcendental   | `AbCutSeq`     | **hypothesis** (no LEM-free total one) |

The classical construction collapses this table to one row: every real is
an element of a complete field, and the algebraicity of the modulus is
invisible.  Real213 keeps the column.  **Algebraicity, here, just is the
existence of a closed-form completion modulus** — a fact the structure of
the cut exhibits, rather than a property proved after the fact about
points in a pre-built continuum.

## 4. Why this is the rigorous form, and how it is falsifiable

The thesis is not "completeness is false" or "classical reals are wrong".
It is constructive and positive:

  1. a real is a decision procedure against the rationals;
  2. that procedure is the object (no exterior point);
  3. arithmetic, order, and the algebraic reals are built without ever
     invoking completeness;
  4. completeness re-enters only as a limit operation on sequences —
     unconditional exactly for the algebraic case, modulus-gated for the
     transcendental case.

Each clause is a Lean fact, ∅-axiom:

  - (A) algebraic real with no completion — `PhiAsCut.phiCut` PURE;
  - (B) arithmetic/order independent of completion — the import graph;
  - (C) completion derived and, for algebraic reals, redundant —
    `PhiAbCut.phiCompletion_limit_eq_phiCut` PURE;
  - (D) completion modulus-gated for transcendentals — `EulerCut` /
    `PiCut` take it as a hypothesis; the refusal of the total modulus is
    `Cauchy/MonotonicBounded` §180–194.

Falsification would be concrete: exhibit a Real213 arithmetic or order
theorem whose `#print axioms` reveals a dependence on `CauchyComplete`,
or a PURE total order-Cauchy modulus for e (which would mean the §180 LEM
barrier was illusory).  Neither exists in the current tree.

## 5. Grouping the groupings: the tower closes (no regress)

Completion groups an infinite family of threshold decisions into one cut.
A natural worry pushes the other way: if a real *is* the grouping of
infinitely many thresholds, then is the grouping itself just one more
threshold to be grouped — a sequence of groupings, then a grouping of
*those*, without end?  Does the construction only ever defer, never land?

`lean/E213/Lib/Math/Analysis/CompletionTower.lean` shows it lands, by
`rfl`.  The grouping operation is a **fixed point**, not a regress, for
three reasons that are each a one-line Lean fact.

  - **Type closure.**  `limit : CauchyCutSeq → (ℕ → ℕ → Bool)`.  A cut is
    `ℕ → ℕ → Bool`; a cut-*sequence* is `ℕ → ℕ → ℕ → Bool`.  Completion
    consumes the sequence and returns a cut — *the same type a single
    threshold-family already inhabits*.  The tower never escalates to
    ever-higher types; every level lands back on `ℕ → ℕ → Bool`
    (`tower_stays_in_cut`).
  - **Collapse.**  A level-2 tower — an outer cut-sequence whose `i`-th
    term is itself a completed limit — completes to *one* inner
    completion read at the outer modulus (`tower_is_single_inner`, `rfl`).
    No second object is built; the two levels flatten.  Completing a cut
    that is already a limit is the identity (`completion_idempotent`).
  - **Only the modulus moves.**  What accumulates up the tower is not
    objects but the **modulus** — level 2 reads at the composite of the
    inner and outer moduli.  And `tower_value_stable` makes the consequence
    sharp: once one completion pins the value at a probe, further grouping
    only re-indexes *which* layer answers — never the answer.

`Analysis/ModulusMonoid.lean` names the bookkeeping exactly.  The moduli
form a commutative monoid — pointwise `(ℕ, +, 0)`:

    Modulus := ℕ → ℕ → ℕ,   madd N₁ N₂ := (m,k) ↦ N₁ m k + N₂ m k,
    mzero := (m,k) ↦ 0,

with the laws `madd_zero_{l,r}`, `madd_assoc`, `madd_comm` (pointwise, so
∅-axiom), and the tower is an **action** of it: `tower_resolves_at_madd`
— the level-2 tower resolves at the composite `madd No Ni`, stacking
levels *adds* moduli; `identity_level_is_mzero` — the trivial grouping
adds the identity `mzero`.

This is the *same* `(ℕ, +)` bookkeeping as the `(ℕ,+)`-graded cut
transformers of `Analysis/ResolutionShift`, carried pointwise.  The link
is honest — a scalar grade `E : ℕ` is not literally a modulus function,
but it **embeds**: `gradeToModulus E := (m,k) ↦ E` is a *monoid
homomorphism* (`gradeToModulus_zero`, `gradeToModulus_add`), so the
ResolutionShift grade monoid sits inside the tower's modulus monoid as
the constant sub-monoid, and grade addition `E₂ + E₁`
(`IsResolutionShift_compose`) is `madd` of the embedded moduli
(`shift_grade_embeds`).  Grouping-of-groupings and resolution-shifting
are one `(ℕ,+)` — one scalar, one pointwise.

So the "threshold of thresholds of thresholds …" sequence is the
**self-similar floor** (`Theory/Raw/Lambek.self_similar_floor`) read at
the cut scale, under the scale-invariance of
`ObjectIsReadingScaleInvariant`: one fixed shape — *group an indexed
family into one object of the same kind* — recurring at every level, the
descent of moduli the only thing in motion.  This is the same structural
signature as the residue itself (peel and you find the same shape, the
descent terminates), now at the level of real numbers.  Tangibility
survives the iteration precisely because each grouping returns an object
you can query, of the kind you started with — the tower is a finite-depth
read at every probe, never an appeal to a completed infinity of levels.

## Anchors

  - `lean/E213/Lib/Math/Real213/AbCutSeq.lean` — the shared carrier
  - `lean/E213/Lib/Math/Real213/PhiAbCut.lean` — algebraic case
  - `lean/E213/Lib/Math/Real213/ExpLog/{EulerCut,PiCut}.lean` —
    transcendental case
  - `lean/E213/Lib/Math/Real213/PhiAsCut.lean` — φ closed-form cut
  - `lean/E213/Lib/Math/Analysis/CauchyComplete{,Valid}.lean` — the
    completeness operation and its closure under valid cuts
  - `lean/E213/Lib/Math/Analysis/CompletionTower.lean` — grouping the
    groupings closes (type closure, collapse, modulus composition)
  - `lean/E213/Lib/Math/Analysis/ModulusMonoid.lean` — the modulus monoid
    `(ℕ→ℕ→ℕ, +, 0)`, the tower as its action, ResolutionShift grades
    embedded as the constant sub-monoid
  - `lean/E213/Lib/Math/Analysis/ResolutionShift.lean` — the `(ℕ,+)`-graded
    monoid the tower's moduli compose in
  - `lean/E213/Theory/Raw/Lambek.lean` — `self_similar_floor` (the same
    shape at the Raw scale)
  - `lean/E213/Lib/Math/Cauchy/MonotonicBounded.lean` §180–194 — the
    deliberate LEM refusal

Companions: `theory/math/real213.md` (the Real213 sub-tree),
`theory/math/phi_self_similarity.md §3.5` (φ as a Cauchy-complete limit
object).
