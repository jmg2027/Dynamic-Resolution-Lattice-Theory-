# Completeness Without Completeness

### Real numbers as finite pointing, and the open hierarchy of resolution axes

**Mingu Jeong**

*A 213 / DRLT narrative paper. Source of truth: `lean/E213/`. Every claim marked*
*`(L)` is a zero-axiom Lean theorem; `(C)` is a classical fact stated for context;*
*`(✗)` is explicitly out of scope.*

---

## Abstract

Modern analysis founds the real numbers on **completeness**: a real is an
equivalence class of Cauchy sequences, or a Dedekind cut, and "the limit exists"
is secured by an axiom (least-upper-bound, or the completeness of a metric space).
This paper develops a single thesis to its end:

> **Completeness is not a foundation. It is a *relocated finite operation*. A real
> number is a finite act of pointing — a decision procedure — and everything usually
> attributed to "the limit" is already present in that finite act, iterated.**

From this starting point a connected arc unfolds, every link of which is a
zero-axiom (∅-axiom) Lean theorem in the 213 framework. A real number is a cut /
decision procedure (Part I). Its *convergents* trace a definite geometric shape — a
hyperbola carried by a hyperbolic element of `SL₂(ℤ)` — and whether they ride **one**
conic or **escape every** conic is exactly the algebraic / transcendental divide
(Part II). The *manner of escape* is captured by a discrete Wronskian whose
finite-difference **depth** is a new invariant, orthogonal to the irrationality
measure and equal to the P-recursive rank (Part III). Resolving that depth requires
a tower of **axes** — difference, ratio-lift, recursion-into-the-exponent — whose
coordinates are ordinals, open-ended past `ω²`, `ω^ω`, `ε₀`, with no top (Part IV).
And when one finally tries to *name the act of raising the ceiling itself*, the
naming is a diagonalisation that reproduces the framework's own foundational
**residue**: the arc closes back onto where it began (Part V).

The reader does not need 213 to read this. The mathematics is ordinary number
theory, the geometry of continued fractions, finite-difference calculus, and a
diagonal argument. What 213 supplies is the insistence that **none of it requires a
completeness axiom** — and the discipline of having checked, mechanically, that it
does not.

---

## How to read this paper

The arc is one long sentence: *the infinite is handled by reducing it to a finite
reference; iterate the reduction and a hierarchy of forms appears; name the
hierarchy and you are back at the start.* Each part is one clause.

| Tag | Meaning |
|---|---|
| **(L)** | A theorem proved in `lean/E213/`, `#print axioms` clean (no `propext`, `Quot.sound`, `Classical.choice`, `native_decide`, no Mathlib). |
| **(C)** | A classical mathematical fact, stated to locate the (L) results in known terrain. Not part of the ∅-axiom contract. |
| **(✗)** | Deliberately *not* claimed — the boundary of the construction. |

Lean file names are given inline; a full index is the Appendix. Where a number
appears (a depth, a determinant), it is a Lean-checked computation unless marked (C).

---

## Part I — The thesis: completeness is a relocated finite operation

### 1. What a real number is, operationally

Fix the question down to its operational core. To *use* a real number `x` is never
to hold its completed decimal; it is to **answer comparisons**: given a rational
`m/k`, is `x ≤ m/k`? A real number, used, is a procedure that answers this for every
rational. So take that as the definition.

> **Definition (Real213 cut).** A real is a decision procedure
> `c : ℕ → ℕ → Bool` with `c m k = ⟦x ≤ m/k⟧`, subject to a monotonicity /
> coherence condition (`ValidCut`). `RatioCut`, `constCut`, and the rational
> embedding are special cases. **(L)** (`lean/E213/Lib/Math/Real213/`.)

There is no completion step here, and no equivalence class quotient is *needed* to
make the object exist: the cut *is* the real. Two cuts denote the same real when
they refine each other, and "refine" is a single arrow — not four parallel notions.
(In 213 terms, `cutEq`, `ZpSeqEquiv`, `signedEq`, … are decompositions of one
Lens-arrow `Lens.refines`, not separate equivalences.)

The classical move — "a real *is* an equivalence class of Cauchy sequences" — is
recovered, not assumed. A monotone bounded ab-sequence yields a cut
(`AbCutSeq`, with `IsAbMonotonic` / `IsAbPositiveB`), and the statement usually
called *Cauchy completeness* becomes a **constructed theorem** about cuts, not an
axiom about a quotient: `Math.Analysis.CauchyComplete`, built on `MonotonicBounded`
(an ab-monotonic sequence is `isOrderCauchy` for every `(m,k)`). **(L)**

This is the first sense of "completeness without completeness": the limit is not
posited; it is the cut the procedure already computes.

### 2. The modulus, and why algebraic and transcendental part ways here

A decision procedure must *terminate with a verdict* at each precision. The data
that says how much work a given precision needs is the **modulus of convergence**.
The thesis predicts the modulus should be *finitely describable* — and the way it is
describable splits the reals cleanly.

- **Algebraic reals carry a closed-form modulus.** For `φ` (the golden ratio) the
  cut can be completed *unconditionally*: the recurrence that generates its
  convergents gives an explicit, total modulus. The completion needs no hypothesis.
  **(L)** (`PhiProbeFixed`, `PellSeq` for `√2`.)

- **Transcendental reals take the modulus as a hypothesis.** For `e` and `π` there
  is no LEM-free *total* modulus available from the series alone; the construction
  proceeds by *assuming* a modulus (`MonotonicBounded`, §180–194 of the development)
  and is honest that this assumption is doing work. **(L for the conditional
  statement; the unconditional total modulus is (✗) — it would need a choice
  principle 213 refuses.)**

The split is not cosmetic. It is the same split that the rest of the paper sees from
every other angle: the shape of the convergents (Part II), the form of the
divergence (Part III), the height of the resolution axis (Part IV). **Algebraicity =
a finite description that closes; transcendence = a finite description that must keep
deferring.** The reader should carry this single contrast forward; everything below
is a refinement of it.

---

## Part II — The shape of a real: the probe-twist conic

### 3. The wobble is a universal identity

Take a real's convergents and *probe* them with a fixed twist. The natural twist in
213 is the Möbius map of

$$P = \begin{pmatrix} 2 & 1 \\ 1 & 1 \end{pmatrix}, \qquad
  f(x) = \frac{2x+1}{x+1}.$$

`P` is not arbitrary. It lies in `SL₂(ℤ)` — `det P = NS − NT = 2·1 − 1·1 = 1`, the
213 structural constants `NS = 3`, `NT = 2` appearing directly as the matrix data —
it is **hyperbolic** (trace `3`, eigenvalues `φ²` and `1/φ²`), and it is
order-preserving on the relevant domain. **(L)** (`MobiusProbeTwist`:
`P ∈ SL₂(ℤ)`, order-preserving.)

Applied to a cut, the twist is `cutThroughP c m k = c (2m+k) (m+k)`. The key fact is
that the twist does **not** distort the cut arbitrarily; it *wobbles* it along a
fixed curve and the wobble is *reversible*: one backward step undoes one forward
step. **(L)** (`ProbeTwistDynamics`: `twist_undoes_step`, i.e. the wobble is `f⁻¹`,
backward Pell.)

The first lesson: the "wobble" is **not a fact about `e`** or about any particular
number. It is a universal identity of the twist itself — every real wobbles the same
way under `P`. What distinguishes reals is not *that* they wobble but *what curve
they wobble on*.

### 4. One conic, or all of them

The curve is a conic. Define the `φ`-norm form

$$Q(m,k) = m^2 - mk - k^2.$$

`Q` is **invariant under one `P`-step**: `Q_preserved` shows `Q` is constant along
the twist orbit. **(L)** (`ProbeTwistConic`.) So each real's convergents, twisted,
ride the level set `Q(m,k) = N` — a hyperbola — for some value `N`.

Now the divide of §2 returns as geometry:

- A **quadratic irrational** rides **one** conic: its own `Q`-value is constant
  forever. `φ` is the fixed point of the twist (`PhiProbeFixed`); `√2` keeps the
  Pell form `x² = 2y² + 1` (`PellSeq`: `pell_invariant`). **(L)** The general
  statement — *every* quadratic irrational has an eventually periodic continued
  fraction and hence a constant form — is Lagrange's theorem. **(C)**

- A **transcendental** rides **no** single conic: its convergents *escape every*
  level set. `e` is **not** a fixed point of the twist (`ProbeTwistFixedPoint`).
  **(L)**

This is "completeness without completeness" seen geometrically: the identity of a
real is not its position on a line (which a completeness axiom would pin) but the
*conic its finite convergents inhabit*. Algebraic = stays on one conic; transcendental
= leaves them all.

### 5. `e` versus `π`: structured versus unstructured transcendence

Both `e` and `π` escape every conic, but not in the same way — and the difference is
visible in the most elementary data, the continued fraction. **(C, verified
numerically.)**

- `e = [2; 1, 2, 1, 1, 4, 1, 1, 6, …]` — an **arithmetic** pattern. The escape is
  *regular*. The exp/tan family shares this: `tanh 1 = [0; 1, 3, 5, 7, …]` (partial
  quotients `aₖ = 2k − 1`, the cleanest case), `tan 1`, `e²` likewise.
- `π = [3; 7, 15, 1, 292, …]` — **no** known pattern. `arctan 1`, `ln 2` likewise:
  irregular, and (Part III) deeper.

So transcendence is not one thing. There is *structured* transcendence (a finite
rule still governs the escape) and *unstructured* transcendence (no such rule is
known). The thesis predicts a finite invariant separating them, and Part III
produces it.

### 6. What is real here, and what is not

The construction reaches exactly this far and stops, on purpose.

- **Real (L):** `P ∈ SL₂(ℤ)`, the conic invariance, the fixed-point /
  non-fixed-point classification, the Pell and Cassini identities.
- **Out of scope (✗):** the *modular / elliptic* theory — the way `SL₂(ℤ)` acts on
  the upper half-plane and *produces* transcendentals (periods, `j`-invariant,
  Gelfond–Schneider). That `SL₂(ℤ)` is the same group is real; the higher theory
  that manufactures transcendence from it is a separate edifice this construction
  does not enter, and the paper does not pretend to.

Naming the boundary is part of the method: the ∅-axiom contract is only meaningful
if the unproven is marked as unproven.

---

## Part III — The shape of divergence: the cross-determinant and depth

### 7. The cross-determinant (a discrete Wronskian)

If a transcendental escapes every conic, *how* it escapes should itself have a form.
Measure it with a discrete Wronskian. For a sequence of convergents form the
**cross-determinant** `Wₙ` — the `2×2` determinant of successive convergent data,
the discrete analogue of a Wronskian. It detects how far the sequence is from
satisfying a fixed linear relation. The three reference reals give three clean
signatures:

| Real | Cross-determinant `Wₙ` | Lean |
|---|---|---|
| `φ` (and quadratic irrationals) | `±1` (Cassini identity) | `Mobius213/Px/ConvergentDet` |
| `e` | `−n!` | `EulerDivergenceForm`: `euler_cross_det_is_factorial` |
| `π` | `−wallisNum · wallisDen` (Wallis) | `EulerDivergenceForm` |

**(L)** for all three. The bounded `±1` of `φ` is the algebraic signature (the
sequence *does* satisfy a fixed linear recurrence). The growing `−n!` of `e` and the
Wallis product of `π` are two distinct shapes of divergence — the same split as §5,
now arithmetised.

### 8. The divergence ladder and divergence depth

The cross-determinant of a transcendental grows, so it is not yet an *invariant
number*; it is a sequence. Reduce the sequence to a number by the oldest trick for
taming growth — **finite differences** — and count how many you need.

> **Definition (divergence ladder & depth).** Let `diff` be the forward difference
> `(Δa)ₙ = aₙ₊₁ − aₙ`, and `liftK` its `k`-fold iterate. A sequence *reaches its
> floor* (`reachesFloor`) when some iterated difference becomes constant
> (`isConst`). The **divergence depth** is the least such `k`. **(L)**
> (`DivergenceLadder`: `diff`, `liftK`, `isConst`, `reachesFloor`.)

Computed on the cross-determinant forms:

| Real | Divergence depth |
|---|---|
| quadratic irrational | **1** (`const_reaches_floor` — already a constant) |
| `e` | **3** (`DivergenceDepth`: `depth_three`) |
| `π` | **6** |
| Liouville number | **∞** (`infinite_depth` — never floors) |

**(L)** for each. Here is a finite number — `3` for `e`, `6` for `π` — that the
infinite divergence is reduced to. This is the thesis in miniature: an *infinite*
object (a divergent determinant sequence) handled by a *finite* reference (its depth).
And `e_ratio_floor` shows `e`'s ladder floors (finite depth) while a Liouville
number's never does (`infinite_depth`).

### 9. Depth is the P-recursive rank, not the irrationality measure

It is tempting to read "depth" as a known quantity. It is not the **irrationality
measure** `μ`. The irrationality measure collapses the very distinction we want:
`μ = 2` for *every* algebraic irrational *and* for `e` *and* for `π` — it cannot
tell structured from unstructured transcendence. Divergence depth *does*: `1` vs `3`
vs `6` vs `∞`. So depth is **orthogonal** to `μ`. **(L for the depth values; the
`μ`-collapse is (C).)**

What depth *is*, classically, is the **P-recursive (holonomic) rank**: the order of
the minimal linear recurrence with polynomial coefficients that the sequence
satisfies. Finite depth means the convergent data is P-recursive; the depth is the
rank. **(L for the depth computations; the identification with holonomic rank is the
(C) bridge to standard terminology — see `DepthPRecursive`.)**

### 10. Finite depth ⟺ P-recursive, and the exp/tan family

The two preceding facts combine into the organising equivalence of Part III:

> **Finite divergence depth ⟺ P-recursive convergent data.** **(L core +
> (C) identification.)**

This now has an explicit ∅-axiom witness. The Newton basis makes "degree `d` ⟹
depth `d`" exact: the binomial column `binom · k` has a truncation-free forward
difference (Pascal's rule), so its `k`-th difference is the constant `binom · 0 = 1`.

> **The degree-`k` discrete monomial has divergence-depth `k`.** `polyDepth k
> (binom · k)`. **(L)** (`DepthPRecursiveInstances.binomCol_polyDepth`.) Every
> discrete polynomial is a `Nat`-combination of these columns, and the top column
> fixes the depth.

The instances follow. **e** is closed end-to-end: its convergent denominators obey a
degree-1 P-recursive recurrence `eulerDen (n+1) = (n+1)·eulerDen n`, and its
cross-determinant ratio `rₙ = n+1` has `polyDepth 1` — depth *equals* recurrence
order (`e_finite_depth_iff_P_recursive`). **π** has its P-recursive recurrences
exhibited (`pi_is_P_recursive`: Wallis num/den, degree-2 step coefficients, so the
cross-determinant ratio is degree 4 — depth 6); pinning that quartic onto the
"degree 4 ⟹ depth 4" count is the one residual step blocked only by the absence of an
∅-axiom `ring` for nonlinear `Nat` identities.

This explains §5 exactly. The exp/tan family (`e`, `e²`, `tan 1`, `tanh 1`) have
arithmetic continued fractions *because* their convergent data is P-recursive —
finite depth. `π`, `arctan 1`, `ln 2` have no known arithmetic CF *because* (as far
as is known) their data is not P-recursive of low order — greater or unknown depth.
The structured/unstructured divide of §5 is the finite/large-depth divide here. One
invariant, three faces: closed-form modulus (Part I), single conic (Part II), finite
depth (Part III).

---

## Part IV — The axes and their hierarchy

Depth answered "how divergent" for sequences that *floor under differencing*. But a
single exponential never floors under `diff` (`Δ(2ⁿ) = 2ⁿ`). To resolve faster
growth we need more than one *axis* of reduction. Part IV builds the axes and finds
their hierarchy is open-ended.

### 11. The second axis: the ratio-lift

Differencing tames polynomials. Its multiplicative twin tames a single exponential.

> **Definition (ratio-lift).** `ratioLift aₙ = aₙ₊₁ / aₙ`; `ratioN` its iterate.
> **(L)** (`DepthTower`.)

The precise fact about it is:

> **`ratioLift` is a difference on the exponent.** `ratio_is_diff_on_exponent`:
> `ratioLift (c^{eₙ}) = c^{Δeₙ}`. **(L)**

So `ratioLift` is *not* a logarithm and *not* an independent new power: it is the
*same* difference operator, conjugated one exponent-layer down. Iterating it reaches
exactly `c^{polynomial}` — no further. The double exponential `2^{2ⁿ}` is a **fixed
point** of every `ratioN` (`ratioN_dexp`), so it **never floors** (`dexp_not_const`):
the two-operator system `(ratioN, diffN)` reaches `c^{poly}` and stops. **(L)**
(`DepthDoubleExp`.) This negative result is what forces a genuinely new axis at the
next layer — not a longer run of the old one.

### 12. The coordinate is an ordinal below `ω²`

With two axes a sequence has a **coordinate** `(h, d)`: `h` = how many ratio-lifts to
reach the exponential regime (the exponent's polynomial degree), `d` = how many
differences to floor after that. Order coordinates lexicographically.

> **The `(h, d)` coordinate is a well-order, an ordinal `< ω²`.** `lex_wf`
> (lexicographic order on `ℕ × ℕ` is well-founded), `no_infinite_descent`. **(L)**
> (`DepthOrdinal`.) The map `(h, d) ↦ ω·h + d` realises it inside `ω²`. **(C)**

So a real's resolution cost is not a single number but an **ordinal**. Algebraic =
`(0, 1)`-ish (floors immediately); `c^{poly}` lives at `ω·h + d < ω²`. Completeness,
again, is nowhere: the cost is a constructive ordinal read off finite data.

### 13. The third axis: recursion into the exponent

`c^{poly}` is the ceiling of two axes. The next layer — `c^{c^{poly}}`, and beyond —
is reached **not** by a third primitive operator but by *recursion*: to resolve a
value `c^{eₙ}`, resolve its **exponent sequence** `eₙ` one axis down.

> **Value-height = 1 + exponent-height.** With `expSeq c e n = c^{eₙ}`:
> `ratioN_expSeq` gives `ratioN d (c^{eₙ}) = c^{diffN d eₙ}` — `d` ratio-lifts of the
> value *is* `d` differences of the exponent. Hence
> `value_floors_iff_exponent_floors`: the value reaches its ratio-floor at depth `d`
> **iff** the exponent reaches its diff-floor at depth `d`. **(L)**
> (`DepthExponentRecursion`.)

The tower of axes is therefore a **self-similar recursion**, not a stack of new
primitives: the *same* `(diff / ratio)` ladder, applied one exponent-layer deeper at
each step, bottoming out at a polynomial exponent. Liouville `c^{k!}` is precisely
the case whose exponent `k!` is itself not diff-resolvable, and this is now pinned
∅-axiom:

> **The Liouville exponent has a finite recursion coordinate.** `ratioLift fact n =
> (n+1)!/n! = n+1` collapses the super-polynomial `k!` to a degree-1 sequence in one
> ratio, and one further difference floors it (`Δ(n+1) = 1`) — yet `k!` never floors
> on the difference axis alone (`Δ(k!) = k·k!`). So the value `c^{k!}`, with **no**
> finite `(h, d)`, sits at ratio-depth `1`, diff-depth `1` one recursion tier down.
> **(L)** (`DepthLiouvilleCoord.liouville_exponent_coordinate`.)

The ordinal reading is now itself ∅-axiom at every finite tower height: each
exponential layer multiplies the rank by `ω`, and the depth-`r` tower coordinate is
an ordinal below `ω^r`.

> **The depth-`r` tower coordinate is a well-order, an ordinal `< ω^r` — the whole
> `ω^ω` ladder, level by level.** The `r`-fold nested lexicographic product `Coord r`
> is well-founded for every `r` (`coord_wf`, generalising `lex_wf` from `ω²`), and
> one more layer strictly dominates the entire lower tower (`coord_layer_dominates`:
> `ω^r·a + ‹sub-ω^r› < ω^r·(a+1)`). **(L)** (`DepthOmegaTower`.) `coord_wf 2`
> recovers `DepthOrdinal`'s `ω²`.

What stays a *classical reading* (C) is only the identification of a *particular
transcendental's* tower with a *specific* `ω^r·d` — the lattice of ranks is proven;
pinning a given real onto a named rung is the holonomic-bridge gap (§10).

### 14. Is `ε₀` the end of the axes? No

The natural question — do the axes stop? — has a clean, honest answer, separating the
proven step from the classical reading.

- **Proven (L):** `ratioN` cannot cross one exponential layer (`dexp_not_const`); the
  second layer needs the §13 recursion. The positive complement is also pinned: the
  double exponential's *exponent* `cⁿ` floors under one ratio-lift one axis down
  (`DepthOmegaTower.dexp_exponent_floors`). And every finite rung `ω^r` is now a
  proven well-order (`coord_wf`), so the finite-`r` ladder up to `ω^ω` is ∅-axiom.
- **Classical reading (C):** the *supremum* `ω^ω` and beyond. Reaching `ε₀`
  requires diagonalising the tower *height* `r` itself — a further meta-recursion
  (`ω^ω`, `ω^{ω^ω}`, … with limit `ε₀`). But `ε₀` is a *fixed point*
  (`ω^{ε₀} = ε₀`), the closure of *one* diagonalisation — **not a top.** `ε₀ + 1`,
  `ε₁`, the Veblen hierarchy all lie above, each reached by yet another meta-axis.

The hierarchy has **no top**. "Handle the infinite by a finite reference, iterate"
generates an open-ended sequence of axes, and every named ceiling — `ω²`, `ω^ω`,
`ε₀`, … — is merely where one particular iteration closes. This sets up the final
move.

---

## Part V — The closure: naming the ceiling-raising is the residue

### 15. The diagonalisation that brings the arc home

Part IV left a hierarchy with no top, each axis raising the last. The one move left
is to *name the raising itself*: to point not at a level but at **the whole sequence
of levels at once**, as a single object.

That reference is a **diagonalisation**. Read `f i` as "the `i`-th ceiling / growth
level". The single object that names them all is the diagonal

$$\mathrm{diag}\, f \; (n) = f(n,n) + 1.$$

And the diagonal argument shows it is *outside the sequence it was built to
summarise*:

> **Naming the ceiling-raising escapes the sequence.** `diag_not_in_seq`:
> `diag f ≠ f i` for every `i`. **(L)** (`DepthCeilingResidue`.)

So referencing the whole tower produces a **fresh ceiling outside the tower** — which
can again be named, and again. Naming the hierarchy neither terminates it nor escapes
it; it reproduces the very gap that forces the next step.

This is not a fact about ordinals. It is the *same structure* as 213's own
foundational **residue** — the surplus left whenever pointing tries to point at all
of pointing.

> **The reference leaves a residue (Cantor).** `ceiling_reference_leaves_residue` is
> literally `cantor_general`: no map `X → (X → Bool)` is surjective — pointing at
> "everything pointable" always leaves an un-pointed predicate. **(L)**
>
> **Tie to the foundational residue.** `ceiling_residue_is_pointing_residue`: the
> pointing self-cover `Object1 : Raw → (Raw → Bool)` is *faithful but never total*
> (`self_covering_closure` — injective, not surjective), and the **same**
> non-surjectivity that makes the residue is what makes every named ceiling
> incomplete. **(L)**

The unbounded ordinal tower (`ε₀`, Veblen, …) and the foundational residue are
therefore **one self-covering closure read at two scales**. The act of comprehension
always lands inside the thing it tried to exceed, leaving exactly the gap that forces
the next step. The hierarchy has no top because **pointing has no exterior**
(`seed/AXIOM/05_no_exterior.md`).

And so the arc closes onto its origin. It began (Part I) by refusing to posit a
completed limit — insisting the real is a finite act of pointing, the "limit" already
contained in it. It ends (Part V) by showing that the *only* thing that ever exceeds
the finite act is the residue the finite act itself generates — which is not an
exterior but the next finite act. **Completeness was never the foundation. The finite
act of pointing, and the residue it leaves, is the whole of it.**

---

## Conclusion

One thesis, carried to its end: *completeness is a relocated finite operation.* Read
forward, the arc is —

1. A real is a cut / decision procedure; the limit is the cut it already computes,
   not an axiom (Part I).
2. Algebraic reals close their modulus; transcendental reals defer it (Part I, §2).
3. Convergents wobble on a conic under a hyperbolic `SL₂(ℤ)` twist; algebraic = one
   conic, transcendental = escapes them all (Part II).
4. The *form of escape* is a discrete Wronskian; its finite-difference **depth**
   (`1`, `3`, `6`, `∞` for quadratic, `e`, `π`, Liouville) is a new invariant,
   orthogonal to the irrationality measure, equal to the P-recursive rank (Part III).
5. Resolving depth needs a tower of axes — difference, ratio-lift,
   recursion-into-the-exponent — whose coordinates are ordinals, open past `ω²`,
   `ω^ω`, `ε₀`, with no top (Part IV).
6. Naming the ceiling-raising is a diagonalisation that reproduces the foundational
   residue: the arc closes on its origin (Part V).

Every link is a zero-axiom Lean theorem. The same algebraic/transcendental contrast
appears at every level — closed-form modulus, single conic, finite depth, bounded
axis-height — which is the strongest evidence that the contrast is *structural*, not
an artefact of one representation. None of it used a completeness axiom. That is the
claim, and it has been checked by machine.

### What is and is not claimed

- **Claimed (L):** every theorem cited above, `#print axioms`-clean.
- **Context (C):** Lagrange's theorem, the irrationality-measure collapse, the
  holonomic-rank identification, the `ω^ω`/`ε₀` ordinal readings, the continued-
  fraction data for the exp/tan family.
- **Out of scope (✗):** an unconditional LEM-free total modulus for `e`, `π`; the
  modular/elliptic *production* of transcendentals; a proof that `π`'s data is not
  P-recursive (only "no known low-order recurrence").

---

## Appendix — Lean theorem index

Every `(L)` claim, by file. Source of truth is `lean/E213/`; when this narrative and
the Lean disagree, the Lean wins.

**Part I — the cut and its modulus**
  - `lean/E213/Lib/Math/Real213/` — `Real213` cut, `ValidCut`, `RatioCut`, `constCut`
  - `lean/E213/Lib/Math/Cauchy/MonotonicBounded.lean` — ab-monotonic ⇒ `isOrderCauchy`
  - `lean/E213/Lib/Math/Analysis/CauchyComplete` — completeness as a constructed theorem
  - `lean/E213/Lib/Math/Cauchy/PellSeq.lean` — `√2` closed-form (`pell_invariant`)

**Part II — the probe-twist conic**
  - `lean/E213/Lib/Math/Real213/MobiusProbeTwist.lean` — `P ∈ SL₂(ℤ)`, order-preserving
  - `lean/E213/Lib/Math/Real213/ProbeTwistConic.lean` — `Q_preserved` (the conic)
  - `lean/E213/Lib/Math/Real213/ProbeTwistDynamics.lean` — `twist_undoes_step` (`f⁻¹`)
  - `lean/E213/Lib/Math/Real213/PhiProbeFixed.lean` — `φ` twist-fixed
  - `lean/E213/Lib/Math/Real213/ProbeTwistFixedPoint.lean` — `e` not fixed

**Part III — cross-determinant and depth**
  - `lean/E213/Lib/Math/Mobius213/Px/ConvergentDet.lean` — `φ`'s `Wₙ = ±1` (Cassini)
  - `lean/E213/Lib/Math/Cauchy/EulerDivergenceForm.lean` — `euler_cross_det_is_factorial`
  - `lean/E213/Lib/Math/Cauchy/DivergenceDepth.lean` — `depth_three` (`e`); `π` depth 6
  - `lean/E213/Lib/Math/Cauchy/DivergenceLadder.lean` — `diff`, `liftK`, `reachesFloor`,
    `e_ratio_floor`, `infinite_depth`, `const_reaches_floor`
  - `lean/E213/Lib/Math/Cauchy/DepthPRecursive.lean` — depth = P-recursive rank
    (structural: `polyDepth_succ_iff`)
  - `lean/E213/Lib/Math/Cauchy/DepthPRecursiveInstances.lean` — the witnesses:
    `binomCol_polyDepth` (degree-`k` monomial has depth `k`, exact Pascal diff);
    `e_finite_depth_iff_P_recursive` (e: order-1 recurrence + `polyDepth 1`);
    `pi_is_P_recursive` (π's Wallis recurrences, degree-2 coefficients)

**Part IV — the axes and their ordinal hierarchy**
  - `lean/E213/Lib/Math/Cauchy/DepthTower.lean` — `ratioLift`, `ratio_is_diff_on_exponent`,
    `(h,d)` coordinate
  - `lean/E213/Lib/Math/Cauchy/DepthOrdinal.lean` — `lex_wf`, `no_infinite_descent`
    (`(h,d)` is an ordinal `< ω²`)
  - `lean/E213/Lib/Math/Cauchy/DepthExponentRecursion.lean` — `ratioN_expSeq`,
    `value_floors_iff_exponent_floors` (value-height = 1 + exponent-height)
  - `lean/E213/Lib/Math/Cauchy/DepthDoubleExp.lean` — `ratioN_dexp`, `dexp_not_const`
    (`ratioN` cannot cross one exponential layer)
  - `lean/E213/Lib/Math/Cauchy/DepthOmegaTower.lean` — `coord_wf`,
    `coord_no_infinite_descent`, `coord_layer_dominates` (depth-`r` tower coordinate
    is an ordinal `< ω^r`; the `ω^ω` ladder, each layer ×`ω`); `expTower`,
    `dexp_exponent_floors` (positive companion to `dexp_not_const`)
  - `lean/E213/Lib/Math/Cauchy/DepthLiouvilleCoord.lean` —
    `liouville_exponent_coordinate` (`ratioLift fact = n+1`, one diff floors it;
    `Δ(k!) = k·k!`: `c^{k!}` has no finite `(h,d)` but a finite recursion coordinate)

**Part V — the closure**
  - `lean/E213/Lib/Math/Cauchy/DepthCeilingResidue.lean` — `diag_not_in_seq`,
    `ceiling_reference_leaves_residue` (= `cantor_general`),
    `ceiling_residue_is_pointing_residue` (= `self_covering_closure`)
  - `lean/E213/Lens/FlatOntologyClosure.lean` — `self_covering_closure`,
    `object1_not_surjective`
  - `lean/E213/Lens/Cardinality/Cantor.lean` — `cantor_general`

**Companion narrative chapters**
  - `theory/math/completeness_relocated.md` — the modulus forms in detail
  - `theory/math/probe_twist_conic.md` — the conic / depth / axes development, §0–13
  - `theory/math/phi_self_similarity.md` — `φ` as a nested-bracket limit

---

## Acknowledgments

Theory and all foundational insights: Mingu Jeong. Formalisation, Lean code, and
audit assistance: Claude (Anthropic). The arc was developed interactively; the
discipline of marking every claim `(L)` / `(C)` / `(✗)` — admitting a reading only
once its zero-axiom theorem is in hand, and holding the classical interpretation at
arm's length until then — is itself part of the method.
