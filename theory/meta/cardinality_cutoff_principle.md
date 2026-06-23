# Cardinality cut-off principle

A 213-native methodology for locating structural slices where two
**independent complexity measures** match in scale.  Extracted from
the Hunter ⇔ Aurifeuillean campaign chain
(`theory/math/cohomology/aurifeuillean.md`); applies to any pair
of complexity measures on naturals where one comes from external
algebra and the other from DRLT-internal atomicity.

## §1 The principle

Given:
  · An **external sequence** `f : ℕ → ℕ` with magnitude growing
    polynomially / super-polynomially in the index (e.g.
    `f(m) ≥ b^{m²}` for some base `b`).
  · A **DRLT-internal complexity class** `H_k ⊆ ℕ` parametrised by
    depth / size budget `k`, where each `H_k` is **finite** and
    bounded above by a fixed value `M_k` (independent of `m`).

The cardinality cut-off principle says:

> For every fixed budget `k`, there exists `m_0(k)` such that for
> all `m ≥ m_0(k)`, `f(m) ∉ H_k`.

**Proof outline**: pick the smallest `m_0` with `f(m_0) > M_k`;
since `f` is increasing and `H_k ⊆ [0, M_k]`, all `f(m)` for
`m ≥ m_0` land outside `H_k`.

The principle is trivial as stated — the structural content is
the **identification** of `f`, `H_k`, and the uniform bound `M_k`.

## §2 Why this is 213-native

DRLT forced atomic primitives `{NS = 3, NT = 2, d = 5}` (multiplicity
`c` a free presentation parameter, read at `c = 2`) and
operations `{+, *, ^}` generate a **bounded-description-length**
complexity hierarchy `H_0 ⊆ H_1 ⊆ H_2 ⊆ …`.  Each level
`H_k = {v ∈ ℕ : v has Hunter expression of depth ≤ k}` is
finite.

External algebraic sequences (Aurifeuillean L-coefficients,
cyclotomic values, Galois norms) grow polynomially or
super-polynomially in their index.

The cut-off principle says: external sequences eventually leave
any finite Hunter complexity class.  The **structural content** is
identifying the slice where they coincide before separating —
that slice (if it exists) carries 213-internal information about
the external sequence.

## §3 The exemplar — Hunter ⇔ Aurifeuillean at m = 1

`f(m) := L_m` = Aurifeuillean L-coefficient of `Φ_{2·5·m²}(5)`
(the cyclotomic norm pair generator in `ℤ[√5]`).  Magnitudes:

```
L_1 = 29     (= d² + NT² = NT^d − NS, three Hunter forms)
L_3 ≈ 8.5 × 10⁸   (Φ_90(5) norm)
L_7 ≈ 10⁵⁹       (Φ_490(5) norm)
L_9 ≈ 10⁷⁵       (Φ_810(5) norm)
...               super-polynomial in m
```

`H_k` = depth-`k` Hunter expression values over `{2, 3, 5}` with
`{+, *, ^}`.  Uniform bound at depth 1:

```
M_1 = 5^5 = 3125
```

(maximum being `pow gd gd`).  Hence:

> `∀ v > 3125, v ∉ H_1`.  Since `L_m ≥ L_3 ≈ 8.5·10⁸ ≫ 3125` for
> every `m ≥ 3`, the entire infinite tail `{L_m : m ≥ 3}` lies
> outside `H_1`.

The match slice: **only `L_1 = 29 ∈ H_1`** (in fact `∈ H_2` if we
require non-generator depth ≥ 1).  This is the **single
coincidence** that the chain isolated.

Lean realisation: `cutoff_marathon_at_depth_1` in
`Lib/Math/Cohomology/Fractal/AurifeuilleanFullCutoff.lean`
(28 PURE / 0 DIRTY).

## §4 The literal-vs-refined distinction

The principle's **literal form** ("∀ depth k, f(m) ∉ H_k for
m > m_*") is generally FALSE.  In the Hunter algebra over
`{2, 3}` with `+`, Frobenius (Chicken McNugget) gives: every
`n ≥ 2` is expressible as `2x + 3y`, hence at sufficiently
high depth, every natural number is in some `H_k`.

Hence the **refined form**:

> "For every fixed budget `k`, eventually `f(m) ∉ H_k`."

quantifies `k` first.  The required depth grows unboundedly as
`m` grows, even if every specific `m` has SOME depth
representation.

The literal-vs-refined pivot is itself part of the principle:
diagnosing the literal version's failure is what forces the
refined statement.  In the exemplar chain, this took the form of
an explicit Frobenius witness theorem
(`literal_cutoff_vacuous_at_L_90`).

## §5 The methodology — three-step pattern

The exemplar chain established a reusable three-step pattern:

  **Step 1 — Locate the coincidence**.  Identify a slice where
  `f(m_*) ∈ H_k` for small `k`.  In the exemplar:
  `L_1 = 29 = d² + NT² ∈ H_2`.

  **Step 2 — Diagnose the literal-form failure**.  Find an
  explicit witness that `f(m) ∈ H_∞` for `m > m_*` at some
  (huge) depth.  In the exemplar: `850554441 = 2·425277219 + 3`,
  Frobenius witness.

  **Step 3 — Prove the refined form at minimal depth**.  Establish
  a uniform bound `M_k` on `H_k`, show `f(m) > M_k` for all
  `m ≥ m_0`.  In the exemplar: `M_1 = 3125`, `L_m ≫ 3125` for
  `m ≥ 3`.  Formalise via `decide`-checked Fin-quantified
  enumeration.

Each step yields a concrete Lean deliverable:
  1. Positive witness theorem (`∃` form).
  2. Vacuousness theorem (Frobenius / Chicken McNugget witness).
  3. Cardinality cut-off capstone (`∀ v > M_k, v ∉ H_k`).

## §6 Honest scope and limitations

The principle is **strongest at depth 1** where uniform bounds
are explicit and small.  At depth `k ≥ 2`, the uniform bound `M_k`
grows tower-fast (e.g., depth-2 Hunter includes `5^3125` via
`pow gd (pow gd gd)`), making `M_k` astronomical and the
"`f(m) > M_k`" criterion much weaker.

The depth-≥-2 extension requires either:
  · **Enumeration**: list all depth-`k` Hunter expressions, check
    `f(m) ∉ list` — kernel-intractable for `k ≥ 3` (~22M
    expressions at depth 3).
  · **Structural impossibility**: prove `f(m)` has algebraic
    properties incompatible with any depth-`k` Hunter expression
    (e.g., prime factorisation constraints).  Requires
    domain-specific Galois-theoretic infrastructure.

The principle is **not** a proof technique for `∀ depth`
cut-offs.  Such cut-offs are typically false.  The principle is
for `∃ depth` (uniform bound) and `∀ m ≥ m_0(k)` (asymptotic
tail) statements.

## §7 Applicability beyond Aurifeuillean

The principle generalises to any pair `(f, H_k)` satisfying:
  · `f` is an external sequence with explicit unbounded growth
    (cyclotomic values, prime sequences, Galois norms, lattice
    point counts).
  · `H_k` is a DRLT-internal finite complexity class with explicit
    uniform bound at small `k`.

Candidate applications (continuation work):
  · **Higher Aurifeuillean indices**: `Φ_490(5)`, `Φ_810(5)`, …
    Cut-off at depth 1 follows from `L_m ≫ 3125` trivially.
    Cut-off at depth ≥ 2 requires extended infrastructure.
  · **Catalogue prime sequences**: are the primes appearing in
    Hunter atomic catalogue (`2, 3, 5, 7, 13, 41, 137, 521`)
    closed under any depth-`k` Hunter operation?  If so, that
    closure is itself structural.
  · **Cyclotomic value sequences** at other bases (`Φ_n(d)` for
    `d ≠ 5`).  Each base induces its own Hunter algebra; cut-offs
    can be compared.
  · **Galois norms of small algebraic integers** in real quadratic
    fields `ℤ[√d]`.  Norms grow polynomially; Hunter expressions
    are bounded.  Cut-off applies.

## §8 Methodological vs. mathematical content

The principle's **mathematical content** is modest: a pigeonhole
argument plus an explicit bound.  Its **methodological content**
is the **identification protocol**:

  1. Take a vague structural intuition ("X happens only at slice
     Y").
  2. Distinguish literal vs. refined forms (Frobenius diagnosis).
  3. Identify the explicit finite class and uniform bound.
  4. Formalise the cut-off in Lean as the rigorous form of the
     intuition.

This protocol converts **poetic structural intuitions** into
**verified asymptotic theorems** while preserving the original
direction of insight.

## §8.5 Other instantiations across the corpus

The (locate / diagnose-literal-failure / prove-refined-per-case)
recipe is documented here in its Aurifeuillean home, but the same
three-step shape recurs in two cross-domain places that are not
literally cardinality cut-offs.  Cataloguing them grounds the
methodology as a research technique, not a one-off.

  · **Physics — C2b monotonicity at the atomic constants.**
    `theory/physics/foundations/atomic_constants.md` Step 4 closes
    `∀ m, constraint_C2b m 2 ↔ m = 3` by the same three-step shape:
    (a) **locate** the coincidence at `m = 3, n = 2`; (b) **diagnose**
    that the literal constraint `2mn = m² + m + n − 2` is impossible
    for `m ≥ 4` because `m²` outgrows `2m + 3`; (c) **prove the
    refined form** as explicit small-case checks at `m ∈ {0,1,2,3}`
    plus the monotonicity bound `msq_gt_2m_p3 : 2m + 3 < m²` for
    `m ≥ 4`.  The literal failure is not vacuousness (as in the
    Hunter case) but arithmetic impossibility past a threshold.

  · **Cohomology — α-power truncation at the K_{3,2}^{(c=2)}
    skeleton boundary.**  `theory/math/cohomology/cup_ladder_graduation.md`
    "Higher truncations" closes the structural identity
    `max α-power = (top skeleton dim) + 1` by the same shape:
    (a) **locate** the truncation at the 2-skeleton boundary
    (`α³ = H² ω contribution`); (b) **diagnose** that any literal
    "Steenrod operations remain non-vacuous at higher dim" fails
    because `Sq²(ω) = ω ⌣_0 ω` lands in `C⁴ = ∅`; (c) **prove the
    refined form** as the per-operation vacuity ladder
    (`SteenrodSquaresAtOmega`, `AdemUniversal`, `CartanAtTruncation`).
    The literal failure is the disappearance of the cochain target
    space at the skeleton extension.

Both instances exhibit the same three steps without involving
Aurifeuillean cyclotomic factors or Hunter algebra.  The first
substitutes "explicit small-case checks + monotonicity bound" for
"explicit finite class + uniform bound"; the second substitutes
"target cochain space vanishes" for "Hunter value set sparse beyond
a cardinality bound".  The methodology survives the substitution,
which is what makes it a methodology rather than a single theorem.

## §9 Cross-references

  · `cardinality_cutoff_applications.md` — six concrete realisations
    (Directions B/D/A/C/E/F, 291 PURE total) instantiating the
    methodology across different external sequences, complexity
    classes, and primitive sets.
  · `theory/physics/foundations/atomic_constants.md` Step 4 — C2b
    monotonicity instance (§8.5).
  · `theory/math/cohomology/cup_ladder_graduation.md` — α-power
    truncation instance (§8.5).
  · `theory/math/cohomology/aurifeuillean.md` — exemplar
    application (Hunter ⇔ Aurifeuillean cut-off at m = 1).
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanFullCutoff.lean`
    — formal realisation (28 PURE / 0 DIRTY).
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanCutoff.lean`
    — bounded-parameter precursor (9 PURE).
  · `catalogs/atomic-integers.md` — Hunter primitive catalogue.

## §10 Status

  · **Principle stated**: §1–§4.
  · **Methodology codified**: §5 (three-step pattern).
  · **Exemplar formalised**: §3 (`cutoff_marathon_at_depth_1`,
    28 PURE).
  · **Scope honestly documented**: §6 (depth-≥-2 open).
  · **Generalisation directions**: §7 — instantiated as the
    six-direction application family
    `cardinality_cutoff_applications.md` (291 PURE total across
    six Lean files).
  · **Cross-domain instantiations**: §8.5 — two further occurrences
    of the (locate / diagnose / prove-refined) shape in physics
    (`atomic_constants.md` C2b monotonicity) and cohomology
    (`cup_ladder_graduation.md` α-power truncation), confirming
    the recipe as research technique.

The principle is a **promotion of methodology** — recording the
recurring three-step pattern (locate, diagnose, prove-refined)
as a 213-native research technique for asymptotic structural
claims.  Its concrete reach is documented in the applications
chapter.
