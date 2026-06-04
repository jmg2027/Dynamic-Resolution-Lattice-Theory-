# The probe-twist conic — how cuts wobble, and what separates the reals

This chapter answers a chain of questions about the probe-twist (`MobiusProbeTwist`,
`ProbeTwistFixedPoint`, `ProbeTwistDynamics`, `ProbeTwistConic`): *is the wobble
about e?  How do e and π differ?  what about other transcendentals, and algebraic
irrationals?*  It is careful to mark three tiers — **(L)** what is a ∅-axiom Lean
theorem here, **(C)** what is classical number theory (true, but not formalised in
this repo), and **(✗)** what is out of scope (a tempting connection that the
machinery here does *not* reach).

## 0. The setup, in one line

A Real213 cut is a comparison procedure against rationals `m/k`.  The Möbius matrix
`P = [[2,1],[1,1]]` (`det = 1`, an element of `SL₂(ℤ)`; `trace = 3 > 2`, so
*hyperbolic*) twists the probe `(m,k) ↦ (2m+k, m+k)`, i.e. acts on the rational by
`x ↦ (2x+1)/(x+1)`.  Its eigenvalues are `φ², 1/φ²`; its attracting fixed point is
φ.

## 1. The wobble is **not** about e — it is a universal identity **(L)**

`ProbeTwistConic.Q_preserved` is an identity in *every* `(m, k)`, nothing to do
with e:

    Q(2m+k, m+k) = Q(m, k),    Q(m,k) := m² − mk − k²

(stated sign-free over ℕ).  So `Pstep` **conserves the φ-norm `Q`**: every point
stays on its level set `Q = N`, a hyperbola (discriminant `1 + 4 = 5 = NS + NT`,
the same `5` that makes φ irrational).  The twist slides a point along its own
hyperbola; `N` is the conserved orbit-label; φ is the common asymptotic slope.
This holds for the cut of *any* real.  What distinguishes the reals is **how their
rational-approximation sequence sits relative to these hyperbolae** — §2.

## 2. Algebraic vs transcendental: one conic, or all of them

Track the φ-norm `Q(m_n, k_n)` along each real's convergent sequence `m_n/k_n`:

| real | `Q(mₙ,kₙ)` along convergents | reading |
|---|---|---|
| **φ** (quadratic) | `−1, −1, −1, …` **constant** | stays on the *single* hyperbola `Q=−1` |
| **√2** (quadratic) | diverges under `Q` | but its **own** form `x²−2y² = ±1` is constant |
| **√3** (quadratic) | diverges under `Q` | own form `x²−3y² ∈ {−2,+1}` cycles |
| **e** (transcendental) | `−1, 1, 11, 124, 2089, …` **diverges** | crosses every hyperbola, escaping |
| **π/2** (transcendental) | `−1, −5, −809, −801009, …` **diverges** | likewise, on the negative side |

The dichotomy:

  - **(L)** φ's convergents are a `Pstep`-orbit, so `Q = −1` exactly
    (`PhiProbeFixed.phi_is_probe_twist_fixed` — φ's *cut* is twist-fixed); the
    "wobble" of a non-φ cut is one backward Pell step `f⁻¹`
    (`ProbeTwistDynamics.twist_undoes_step`), and `ProbeTwistFixedPoint.e_not_fixed`
    shows e's cut is *not* fixed.
  - **(L)** √2 keeps its own form: `Cauchy/PellSeq.pell_invariant` proves
    `x² = 2y² + 1` along the Pell orbit ∀n — √2 is the disc-8 analogue of φ.
  - **(C)** *Every* quadratic irrational works this way — **Lagrange's theorem**:
    a real has an eventually-periodic continued fraction **iff** it is a quadratic
    irrational, and the period is exactly a hyperbolic `SL₂(ℤ)` element fixing a
    binary quadratic form of discriminant `b²−4ac > 0`.  So each quadratic
    irrational `α` rides **one** conic `(its own form) = const`, with `α` an
    asymptote; φ (disc 5), √2 (disc 8), √3 (disc 12) are instances.  The general
    statement is classical, not formalised here.
  - **(C)** A **transcendental** satisfies *no* integer polynomial, in particular
    *no* integer quadratic form, so there is no conic it rides — under any fixed
    form the values diverge.  This is why e and π escape every hyperbola.

So "is e special?" — no: e is just *a* real whose convergents are not a Pstep
orbit.  φ is the special one (the orbit itself).

## 3. e versus π: structured vs unstructured transcendence

Both diverge, but the *pattern* differs, and the difference is real:

  - **(L / repo)** their resolving moduli differ in growth — `EulerCut` (e, partial
    sums `Σ1/k!`, denominators `n!`) vs `PiCut` (π/2, Wallis product); see
    `ModulusForm` (the modulus form is a per-real invariant).
  - **(C)** e's continued fraction is **regular**: `[2; 1,2,1, 1,4,1, 1,6,1, …]`
    (Euler), so its `Q`-divergence is patterned (factorial-paced, sign-mixing).
    π's continued fraction `[3; 7,15,1,292, …]` has **no known pattern**; its
    `Q`-divergence is "rough" (Wallis-paced, monotone negative here).  e is a
    *structured* transcendental (a value of `exp` at 1, with a closed series
    fixing its modulus); π is not known to have such arithmetic regularity.

This is the cut-level shadow of a genuine arithmetic difference, but the
*classification* of that difference is open mathematics, not a repo theorem.

## 4. The `SL₂(ℤ)` connection — real; the modular/elliptic one — out of scope

  - **(L)** `P ∈ SL₂(ℤ)` here is exact: `det P = 2·1 − 1·1 = 1 = NS − NT`
    (`ProbeTwistConic.det_P_eq_NS_sub_NT`, and `MobiusProbeTwist.det_P_eq_NS_sub_NT`).
    The conic `Q = N` is the invariant binary quadratic form of this hyperbolic
    element; the whole picture is the action of `SL₂(ℤ)` on the rational line and
    its quadratic forms — the **reduction theory of binary quadratic forms**
    (Gauss), of which the Stern–Brocot / continued-fraction machinery in this repo
    is the constructive face.
  - **(✗)** *"What elliptic curve or modular form makes a transcendental?"* — this
    is **not** what the machinery here reaches, and equating them would be a
    category slip.  The honest statement:
    * The probe-twist lives at the level of `SL₂(ℤ)` acting on `ℙ¹(ℚ)` (continued
      fractions, Pell, binary quadratic forms) — degree-2, one complex dimension of
      "modulus" data.
    * **Transcendence produced by modularity** is a real and deep phenomenon —
      `e^π` (Gelfond), the modular `j`-function's values at non-CM points, periods
      of elliptic curves (Chudnovsky, Nesterenko's theorem on `π, e^π, Γ(1/4)`) —
      but it lives in *transcendence theory* (Baker, Schneider, Nesterenko), a
      strictly higher and separate edifice.  Nothing in this repo touches it, and
      the conic `Q = N` does not "explain" or "produce" those transcendentals.
    * What *is* shared is only the ambient group `SL₂(ℤ)` (the modular group):
      modular forms are functions on `SL₂(ℤ)\ℍ`, and our P is one hyperbolic
      element of that same `SL₂(ℤ)`.  That is a common stage, **not** a derivation
      of one from the other.

## 5. The *form of the divergence* — the cross-determinant **(L)**

If a transcendental's convergents escape every conic, the escape itself has a
shape.  It is the **cross-determinant** (discrete Wronskian, the symplectic area
between consecutive convergents):

    W_n := aₙ·d_{n+1} − a_{n+1}·dₙ.

This one quantity *is* the form of the spreading, and it is a closed function of
`n` for each real — the infinite divergence captured by a finite pointer (its
recurrence), then that captured again (the closed form):

| real | `W_n` | meaning |
|---|---|---|
| **φ** (algebraic) | `±1` constant | `det P = 1`, area preserved → one conic (Cassini, `ConvergentDet`) |
| **e** | `−n!` | step-transfer `(a,d)↦((n+1)a+1,(n+1)d)`, step-det `(n+1)²` → factorial area |
| **π/2** | `−wallisNumₙ·wallisDenₙ` | Wallis-product area (key: `(2n+1)(2n+3) = 4(n+1)²−1`) |

  - **(L)** `EulerDivergenceForm.euler_cross_det` proves `W_n = −dₙ` (sign-free:
    `a_{n+1}dₙ = aₙd_{n+1} + dₙ`); `eulerDen_eq_fact` gives `dₙ = n!`; so
    `euler_cross_det_is_factorial` is `|W_n| = n!`.  **e's divergence form is the
    factorial.**
  - **(L, repo)** φ's `W_n = 1` is the Fibonacci–Cassini identity
    (`Mobius213/Px/ConvergentDet`): the algebraic case is *area-preserving*, which
    is exactly why it stays on a conic.
  - **(L, verified; π proof not formalised here)** π/2's `W_n =
    −wallisNumₙ·wallisDenₙ` follows from the scalar identity `4(n+1)² =
    (2n+1)(2n+3) + 1`.

So **"what is the form?"** has a uniform answer — *the cross-determinant `W_n`* —
and three different closed values: **constant 1** (algebraic, area-preserved),
**`n!`** (e), **Wallis product** (π).  Same question, three forms; that *is* how e,
π, and the algebraic irrationals differ at this level.  The transcendence of e is
not formlessness — it is the form `W_n = −n!`: an algebraic *function of n*, not an
algebraic *number*.  This is the user's framing made literal: the infinite (the
divergent sequence) is handled by a finite reference (the recurrence of `W_n`), and
the divergence of *that* by another finite reference (the factorial / Wallis closed
form).

## 6. The divergence **ladder** — and divergence *depth* **(L)**

The form `W_n` is itself a sequence, and `n!` itself diverges.  So the question
recurs: *what is the form of that divergence?*  Lift again — take the invariant of
`W_n`, then of that, until it stops moving.  It does stop, in **finitely many
steps**, at a constant.  The number of lifts to the floor is a new invariant: the
**divergence depth** (`DivergenceDepth`).

e's ladder is exact and short (formalised, ∅-axiom):

| level | object | value | status |
|---|---|---|---|
| L0 | convergents `aₙ/dₙ` | → e | diverges |
| L1 | cross-det `|W_n| = dₙ` | `n!` | diverges (`EulerDivergenceForm`) |
| L2 | ratio `rₙ = d_{n+1}/dₙ` | `n+1` | diverges (`L1_to_L2`) |
| L3 | increment `r_{n+1} − rₙ` | `1` | **constant — floor** (`depth_three`) |

So **e has divergence depth 3**.  The depth orders the reals by *how far their
divergence is from trivial*:

  - **(L)** algebraic (φ, √2): **depth 1** — the cross-determinant is *already*
    constant (`±1`, Cassini / `pell_invariant`), the floor of an area-preserving
    (`det = 1`) orbit.  Nothing to lift.
  - **(L)** **e: depth 3** — `DivergenceDepth.depth_three`.
  - **(L, verified)** **π/2: depth 6** — its cross-det *ratio* is the degree-4
    polynomial `4(n+1)²(2n+1)(2n+3)`, which a degree-4 polynomial's four finite
    differences reduce to a constant (`1 cross-det + 1 ratio + 4 differences`).

`algebraic 1  <  e 3  <  π 6`.  This is the precise, ∅-axiom sense in which **e is
a shallower transcendental than π** — the quantification of e's *regular*
continued fraction `[2;1,2,1,1,4,…]` versus π's *irregular* `[3;7,15,1,292,…]`,
now a finite number attached to each real.

This is the user's framing reaching its floor: the infinite (a divergent sequence)
is handled by a finite reference (its level-`k` invariant); the divergence of
*that* by the next; and the tower **terminates** — every real here has a finite
divergence depth, after which the form is a bare constant (the same `±1`/`1` floor
the algebraic reals reach immediately).  The transcendentals are not "beyond form";
they are *finitely deep* in form, and the depth is what tells them apart.

## 7. Depth is **not** the irrationality measure — it is the P-recursive rank **(L + C)**

It is tempting to read divergence depth as a 213-native **irrationality measure**
`μ`.  That is **false**, and the data refutes it before any theorem:

| real | classical `μ` (Liouville–Roth) | ladder depth |
|---|---|---|
| algebraic (deg ≥ 2) | `2` (Roth) | **1** |
| e | `2` | **3** |
| π | `2` (conj.; `≤ 7.1` proved) | **6** |
| Liouville | `∞` | **∞** |

`μ` sends algebraic, e, π all to the *same* value `2` — it cannot separate them.
Depth separates them `1 < 3 < 6`.  So depth is a **finer, orthogonal** invariant:
`μ` measures *how well* the number is approximated by rationals; depth measures
*how complex the recurrence generating its approximants is*.

The honest classification (`DivergenceLadder`):

  - **(L)** **depth 1** ⟺ cross-determinant constant ⟺ *constant-coefficient*
    (autonomous, `det = 1`) recurrence ⟺ quadratic algebraic (φ, √2 — Pell/Cassini;
    `const_reaches_floor`).
  - **(L + C)** **finite depth `d`** ⟺ cross-det ratio is a degree-`(d−2)`
    polynomial ⟺ the convergents are **P-recursive** (polynomial-coefficient
    recurrence): e (coeff `n+1`, degree 1 → depth 3, `e_ratio_floor`), π (coeff
    degree 4 → depth 6).  The *structured* transcendentals.
  - **(L + C)** **depth ∞** ⟺ no polynomial-coefficient recurrence ⟺
    super-polynomial growth ⟺ Liouville-type (`infinite_depth`: if every lift stays
    strictly increasing, the ladder never terminates) — the **only** place depth
    and `μ` agree (both `∞`).

So depth aligns with the **holonomic / P-recursive** hierarchy — the *algorithmic*
complexity of the approximation — not with Diophantine approximability.  It is the
constructive, 213-native reading: a real's place is set by *how deep a finite
recurrence-tower its approximants need*, and depth counts the rungs.  This is the
user's "finite reference for the infinite, iterated until it bottoms out" given a
number: the depth, agreeing with classical `μ` only at the pathological `∞`.

## 8. Finite depth ⟺ P-recursive — and the exp/log family **(L + C)**

`DepthPRecursive` makes the depth-classification a characterization.  Define
`polyDepth d s` := *the `d`-th finite difference of `s` is constant* (`s` is a
discrete polynomial of degree `≤ d`).  The engine is that `diff` commutes through
the iterate (`liftK_diff_comm`), giving:

  - **(L)** `polyDepth_succ_iff` : `polyDepth (d+1) s ↔ polyDepth d (diff s)` —
    differencing lowers degree by exactly one; **depth = number of differences to a
    constant**.
  - **(L)** `polyDepth_reachesFloor` / `reachesFloor_lift` — finite `polyDepth` ⟺
    the ladder terminates; constants are degree 0.

So the **finite-depth reals are exactly the discrete polynomials of the
cross-determinant ladder — the P-recursive class**.  Where this lands the classical
constants **(C, by their known continued fractions)**:

  - the **exp/tan family** — e (`[2;1,2,1,1,4,…]`), e², e^{1/n}, tan 1
    (`[1;1,1,3,1,5,…]`), **tanh 1 = `[0;1,3,5,7,…]`** (`aₖ = 2k−1`, the cleanest) —
    all have **arithmetic** (linear-in-`k`) partial quotients ⟹ P-recursive ⟹
    **finite depth**.  These are exactly the values of `exp`/`tan` at rationals,
    the Riccati/linear-ODE-solvable (E-function / Hermite–Padé) class — *that* is
    what "structured transcendental" means here.
  - **π, arctan 1 = π/4, ln 2** have **no known arithmetic CF pattern** — not known
    to be P-recursive at the CF level, conjecturally deeper.  (π is forced into a
    finite ladder depth only through the *Wallis* product, depth 6, a different
    presentation.)

So depth is not just an invariant — it sorts the transcendentals into
**Riccati-solvable (arithmetic CF, finite depth)** versus **irregular**, matching
the exp-family / non-exp-family split.

## 9. The second axis — the ratio-lift, and the honest extension rule **(L)**

The difference axis (`diff`) tames polynomial growth.  `DepthTower` adds the second
axis — the **ratio-lift** `ratioLift s n = s(n+1)/s n`, the multiplicative analogue
of `diff` — and the key bridge fixes *exactly* what it does:

  - **(L)** `geom_ratio_const` : `ratioLift (cⁿ) = c`, constant — a single
    exponential floors at *ratio*-level 1, as a linear sequence floors at
    *diff*-level 1.
  - **(L)** ★ `ratio_is_diff_on_exponent` : `ratioLift (c^{eₙ}) = c^{diff eₙ}` —
    **the ratio-lift is a `diff` on the exponent.**  Hence `ratioLift^h` floors
    exactly `c^{polynomial of degree h}`: the coordinate `h` is the **exponent's
    polynomial degree** (not an iterated-logarithm height).
  - **(L)** `atTowerCoord h d` — the coordinate: `h` ratio-lifts then `d` diffs.
    `geom_at_1_0` (`cⁿ`, exponent degree 1, at `(1,0)`), `const_at_0_0`.

**The honest reach, and where the rule actually extends.**  Because `ratioLift` only
*differences* the exponent, the `(ratioN, diffN)` system captures precisely the
reals whose cross-determinant is `c^{poly}` (single exponential, polynomial
exponent): e (cross-det `n!`) and π are *not* in this class — `n!` and the Wallis
product are super-polynomial, so on the *value* axis they are difference-depth ∞ and
`ratioLift` does not floor them either (`ratioLift` sends `c^{k!} ↦ c^{k!·k}`, the
exponent still growing).  So **Liouville `c^{k!}` has no finite `(h,d)`** — it sits
at the boundary of this two-operator system.  The genuine extension is *not* "one
more `ratioLift`"; it is a **new operation one level down: a ratio on the exponent**.
The exponent `k!` floors under *ratio* (`k! ↦ k+1 ↦` diff `↦` const), so resolving
Liouville means applying the whole `(ratio, diff)` ladder *to the exponent
sequence* — a self-similar recursion.  That recursion, applied to the exponent of
the exponent and so on, is the genuine tower; its height is the third (and `h`-th)
axis.  §10 records what is proven (the `(h,d)` well-order) and marks this recursion
as the frontier.

This is the originating frame reaching its general form: the infinite is handled by
a finite reference; when that reference is itself infinite, a finite reference *one
axis higher* captures it; and the number of axes is itself the invariant.

## 10. The coordinate is an ordinal below ω² **(L)**

The `(h, d)` coordinate is not just a label — it is an **ordinal rank**.  Reading
`(h, d)` as `ω·h + d`, `DepthOrdinal` proves the lexicographic order on `ℕ × ℕ` is
a **well-founded strict linear order** — an honest model of the ordinals below `ω²`:

  - **(L)** `lex_irrefl` / `lex_trans` / `lex_total` — a strict *linear* order.
  - **(L)** ★ `lex_wf` — **well-founded** (nested `Acc.rec` on `Nat.lt_wfRel.wf`):
    the defining ordinal property.  Hence `no_infinite_descent` — no coordinate
    chain descends forever, i.e. **the resolution always terminates**.  This is the
    constructive content of the whole frame: "finite reference for the infinite,
    iterated" is a descending walk in a well-order, and termination *is*
    well-foundedness.
  - **(L)** `log_axis_dominates` — `(h,d) < (h+1,d')`: one logarithm of growth
    outweighs unboundedly many differences (`ω·h + d < ω·(h+1) + d'`).
    `floor_minimal` — `(0,0)` is the bottom (algebraic base, rank `0`).

Ranks (corrected): algebraic `(0,0)=0` · e (cross-det `n!`) `(1,1)` · π similar —
all `< ω²` and well-ordered by `DepthOrdinal`.  **Liouville is not `ω+d`**: it has
no finite `(h,d)` under `(ratioN, diffN)` (its exponent `k!` is super-polynomial,
floored only by a *ratio on the exponent*, not by `ratioLift`).  The well-order
theorem `lex_wf` stands for the reals that *do* have a finite `(h,d)`; reaching
Liouville and the iterated-exponential tower needs the genuine third axis
(ratio-on-exponent, a self-similar recursion), and the climb toward `ε₀` is that
recursion's frontier — **not** captured by finitely many `ratioLift`s.  Within its
honest reach, a constructive real's place is a single ordinal `< ω²`: how deep its
`(ratio, diff)` tower runs.

## 11. The third axis, formalised — recursion into the exponent **(L)**

`DepthExponentRecursion` builds the genuine extension.  Writing `expSeq c e n :=
c^{eₙ}`, the axis above is *not* another `ratioLift` but a **recursion into the
exponent**:

  - **(L)** `ratioLift_expSeq` — one ratio-lift peels one difference off the
    exponent: `ratioLift (expSeq c e) = expSeq c (diff e)`.
  - **(L)** ★ `ratioN_expSeq` — `d` ratio-lifts of the value = `d` differences of
    the exponent: `ratioN d (expSeq c e) = expSeq c (diffN d e)` (pointwise, no
    `funext`, for a totally-monotone exponent).
  - **(L)** ★★★ `value_floors_iff_exponent_floors` — the value reaches its
    ratio-floor at depth `d` **iff** the exponent reaches its diff-floor at depth
    `d`.  The value sits **exactly one axis above its exponent**, resolved by the
    *same* `(diff/ratio)` ladder one layer down.

So the axis tower is a **self-similar recursion**, not a stack of new primitives:
`value-height = 1 + exponent-height`, bottoming out at a polynomial
(diff-resolvable) exponent.  Liouville `c^{k!}` is exactly the case where the
exponent `k!` is itself *not* diff-resolvable (factorial outgrows every polynomial)
— it floors only under *ratio* (`k! ↦ k+1`), so `k!` is itself `expSeq`-like, and
recursing through exponent after exponent is the climb toward `ε₀`.  The user's
"infinite handled by a finite reference, iterated" frame, in its final form, *is*
this recursion: each axis is the same ladder applied one exponent layer deeper, and
the number of layers is the ordinal.

## 12. Is `ε₀` the end of the axes?  No — and the first step is proven **(L + C)**

A natural question: do the axes stop at `ε₀`?  Two things must be separated — what
is a `∅`-axiom **theorem** here, and what is the classical **ordinal reading**.

**(L) The proven structural step** (`DepthDoubleExp`): each exponential layer is a
*genuinely new* axis — iterating the previous one does **not** cross it.  Precisely,
the double exponential `2^{2ⁿ}` is a **fixed point of every `ratioN h`**
(`ratioN_dexp`: `ratioN h (2^{2ⁿ}) = 2^{2ⁿ}`), because `2ⁿ` is a fixed point of
`diff` (`diff_twoPow`, `diffN_twoPow`) and the ratio axis is a difference *on the
exponent*.  Hence `2^{2ⁿ}` never reaches a constant floor under `ratioN`
(`dexp_not_const`).  So the two-operator system `(ratioN, diffN)` reaches **exactly**
`c^{poly}` (coordinate `(h,d)`, `< ω²`); the second exponential layer `c^{c^{poly}}`
is strictly beyond it and needs the *recursion* of §11, not a longer `ratioN`.

**(C) The ordinal reading** (classical interpretation of these sequence facts):
under the recursion, each exponential layer **multiplies the rank by `ω`** (a value's
resolution depth is its exponent's depth lifted one full axis).  So:

  | object | rank |
  |---|---|
  | polynomial | `d` `(< ω)` |
  | `c^{poly}` | `ω·d` `(< ω²)` |
  | `c^{c^{poly}}` | `ω²·d` `(< ω³)` |
  | depth-`r` exponential tower | `ω^r·d` `(< ω^{r+1})` |
  | all finite `r` | sup `= ω^ω` |

`ε₀` is then the closure of diagonalising the tower **height** `r` itself — a
further meta-recursion (`ω^ω`, `ω^{ω^ω}`, … with limit `ε₀`).  **So `ε₀` is not "the
end".**  It is one fixed point (`ω^{ε₀} = ε₀`), the closure of *this* diagonalisation;
`ε₀ + 1`, `ε₁`, the Veblen hierarchy, … all lie above, each reached by yet another
meta-axis.  The picture has no top: "handle the infinite by a finite reference,
iterate" generates an open-ended hierarchy of axes, and every named ceiling (`ω²`,
`ω^ω`, `ε₀`, …) is just where one particular iteration closes.  This file proves the
first rung of that ladder (one exponential layer is uncrossable by the axis below);
the heights themselves are the classical ordinal hierarchy.

## 13. Naming the ceiling-raising is a diagonalisation — the residue, one scale up **(L)**

§12 left the hierarchy open: every named ceiling is where one iteration of "resolve
the infinite by a finite reference" closes, and the *next* axis raises it.  The
remaining move is to make **the act of raising the ceiling** itself a single
reference — to point not at a level but at the whole sequence of levels at once.

That reference is a **diagonalisation**.  Read `f i` as "the `i`-th ceiling / growth
level"; the object that names them all is `diag f n = f n n + 1`.  The diagonal
argument shows it is *outside the sequence it summarises* — `diag f ≠ f i` for every
`i` (`diag_not_in_seq`, ∅-axiom): referencing the whole tower produces a fresh
ceiling outside the tower, which can again be named, and again.  So "make the
ceiling-raising a reference" neither terminates the hierarchy nor escapes it — it
**reproduces the gap that forces the next step**.

This is not a fact about ordinals; it is the *same* structure as the foundational
residue.  `cantor_general` — the engine behind
`FlatOntologyClosure.object1_not_surjective` — says any map `X → (X → Bool)` fails to
be surjective: pointing at "everything pointable" always leaves an un-pointed
surplus.  The depth-ceiling diagonal is one instance of exactly that map in temporal
guise.  `ceiling_residue_is_pointing_residue` (∅-axiom) ties them: the pointing
self-cover `Object1 : Raw → (Raw → Bool)` is faithful but never total
(`self_covering_closure`), and the *same* non-surjectivity is what makes every named
ceiling incomplete.  The unbounded ordinal tower (`ε₀`, Veblen, …) and the residue
are **one self-covering closure read at two scales**.  The hierarchy has no top
because *pointing has no exterior* (`seed/AXIOM/05_no_exterior.md`) — and so the arc
that began with "completeness is a relocated finite operation" closes back onto the
residue it set out from.

## Summary

The wobble's *shape* (hyperbola `Q = N`, `ProbeTwistConic`) and *step* (`f⁻¹`,
`ProbeTwistDynamics`) are universal ∅-axiom facts.  What sorts the reals is whether
their convergents ride **one** conic (quadratic irrational — own form constant; φ
and √2 formalised, the general case Lagrange's theorem) or **escape every** conic
(transcendental — e and π, differing only in the regularity of the escape).  The
group behind it all is `SL₂(ℤ)`; the elliptic/modular *production* of
transcendentals is a separate, higher theory this construction does not reach.

## Anchors

  - `lean/E213/Lib/Math/NumberSystems/Real213/ProbeTwistConic.lean` — `Q_preserved` (the conic)
  - `lean/E213/Lib/Math/NumberSystems/Real213/ProbeTwistDynamics.lean` — `twist_undoes_step` (`f⁻¹`)
  - `lean/E213/Lib/Math/NumberSystems/Real213/PhiProbeFixed.lean` — φ twist-fixed
  - `lean/E213/Lib/Math/NumberSystems/Real213/ProbeTwistFixedPoint.lean` — e not fixed
  - `lean/E213/Lib/Math/NumberSystems/Real213/MobiusProbeTwist.lean` — `P ∈ SL₂(ℤ)`, order-preserving
  - `lean/E213/Lib/Math/Analysis/Cauchy/PellSeq.lean` — `pell_invariant` (√2 keeps `x²=2y²+1`)
  - `lean/E213/Lib/Math/Analysis/Cauchy/EulerDivergenceForm.lean` — `euler_cross_det_is_factorial`
    (e's divergence form `|W_n| = n!`)
  - `lean/E213/Lib/Math/Algebra/Mobius213/Px/ConvergentDet.lean` — φ's `W_n = 1` (Cassini)
  - `lean/E213/Lib/Math/Analysis/Cauchy/DivergenceDepth.lean` — the divergence ladder;
    `depth_three` (e bottoms out at depth 3); algebraic depth 1, π depth 6
  - `lean/E213/Lib/Math/Analysis/Cauchy/DivergenceLadder.lean` — abstract depth
    (`diff`/`liftK`/`reachesFloor`); `e_ratio_floor` (finite), `infinite_depth`
    (Liouville ∞), `const_reaches_floor` (algebraic floor); depth = P-recursive
    rank, **not** the irrationality measure
  - `lean/E213/Lib/Math/Analysis/Cauchy/DepthTower.lean` — the ratio axis (= diff on the
    exponent); `(h,d)` coordinate
  - `lean/E213/Lib/Math/Analysis/Cauchy/DepthOrdinal.lean` — `(h,d)` is an ordinal `< ω²`
    (`lex_wf`, `no_infinite_descent`)
  - `lean/E213/Lib/Math/Analysis/Cauchy/DepthExponentRecursion.lean` — the third axis:
    recursion into the exponent (`ratioN_expSeq`, `value_floors_iff_exponent_floors`)
  - `lean/E213/Lib/Math/Analysis/Cauchy/DepthDoubleExp.lean` — `ratioN` cannot cross one
    exponential layer (`ratioN_dexp`, `dexp_not_const`); each layer a new axis; the
    rank-`×ω` / `ω^ω` / `ε₀`-is-not-the-end reading
  - `lean/E213/Lib/Math/Analysis/Cauchy/DepthCeilingResidue.lean` — naming the ceiling-raising
    is a diagonalisation (`diag_not_in_seq`); it reproduces the foundational residue
    (`ceiling_reference_leaves_residue` = `cantor_general`,
    `ceiling_residue_is_pointing_residue` = `self_covering_closure`); the arc closes
  - Companion: `theory/math/numbersystems/completeness_relocated.md` (modulus forms),
    `theory/math/algebra/phi_self_similarity.md` (φ as nested-bracket limit).
