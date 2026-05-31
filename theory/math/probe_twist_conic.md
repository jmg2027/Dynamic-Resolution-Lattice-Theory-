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

## Summary

The wobble's *shape* (hyperbola `Q = N`, `ProbeTwistConic`) and *step* (`f⁻¹`,
`ProbeTwistDynamics`) are universal ∅-axiom facts.  What sorts the reals is whether
their convergents ride **one** conic (quadratic irrational — own form constant; φ
and √2 formalised, the general case Lagrange's theorem) or **escape every** conic
(transcendental — e and π, differing only in the regularity of the escape).  The
group behind it all is `SL₂(ℤ)`; the elliptic/modular *production* of
transcendentals is a separate, higher theory this construction does not reach.

## Anchors

  - `lean/E213/Lib/Math/Real213/ProbeTwistConic.lean` — `Q_preserved` (the conic)
  - `lean/E213/Lib/Math/Real213/ProbeTwistDynamics.lean` — `twist_undoes_step` (`f⁻¹`)
  - `lean/E213/Lib/Math/Real213/PhiProbeFixed.lean` — φ twist-fixed
  - `lean/E213/Lib/Math/Real213/ProbeTwistFixedPoint.lean` — e not fixed
  - `lean/E213/Lib/Math/Real213/MobiusProbeTwist.lean` — `P ∈ SL₂(ℤ)`, order-preserving
  - `lean/E213/Lib/Math/Cauchy/PellSeq.lean` — `pell_invariant` (√2 keeps `x²=2y²+1`)
  - `lean/E213/Lib/Math/Cauchy/EulerDivergenceForm.lean` — `euler_cross_det_is_factorial`
    (e's divergence form `|W_n| = n!`)
  - `lean/E213/Lib/Math/Mobius213/Px/ConvergentDet.lean` — φ's `W_n = 1` (Cassini)
  - `lean/E213/Lib/Math/Cauchy/DivergenceDepth.lean` — the divergence ladder;
    `depth_three` (e bottoms out at depth 3); algebraic depth 1, π depth 6
  - Companion: `theory/math/completeness_relocated.md` (modulus forms),
    `theory/math/phi_self_similarity.md` (φ as nested-bracket limit).
