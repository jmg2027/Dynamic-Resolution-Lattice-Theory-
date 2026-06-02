# Newton–Gregory over ℤ — the faithful forward-difference reconstruction

**Status**: Closed.  Source of truth (all ∅-axiom):
`lean/E213/Lib/Math/Cauchy/NewtonGregory.lean` (41 PURE / 0 dirty), built on the
213-native `binom` and the divergence-ladder `diff`/`liftK` of
`Cauchy/DepthPRecursive`, lifted to `ℤ` via `E213.Meta.Int213.Core`.

## Overview

`DepthPRecursiveInstances` proves the **forward** law over `ℕ`: a degree-`d`
Newton-form polynomial `Σ_{i≤d} cᵢ·binom(·,i)` has divergence-depth `d`
(`newton_polyDepth`).  The **converse** — reconstruct a depth-`d` sequence *from*
its iterated differences-at-a-point — cannot be stated over `ℕ`: the forward
difference `s(n+1) − s n` uses **truncated** subtraction, so a single negative
intermediate difference is clamped to `0` and its information is lost.

The generalization runs the finite-difference calculus over `ℤ`, where subtraction
is faithful.  Over `ℤ` the operator identity `Eⁿ = (I + Δ)ⁿ` (shift `E`, difference
`Δ = E − I`) becomes a hypothesis-free reconstruction, and its sign-twisted inverse
makes the whole thing an invertible change of basis.

## The difference-Lens and its readout group

`Δ` is a count-Lens reading of a sequence — the "how much did the next term move"
reading.  It does **not close under its own iteration** over `ℕ`: iterating `Δ`
demands differences that `ℕ` cannot represent and clamps.  The readout group in
which `Δ` *does* close under iteration is `ℤ`.  This is not "fixing ℕ" and not an
ℕ-vs-ℤ dichotomy: `ℤ` is simply the group the difference-Lens lands in.  (It is
axiom-clean — a definable inductive type with ∅-axiom ring laws in `Int213.Core`,
no Mathlib, no `Classical`.)  Over `ℤ` the calculus is `diffZ`, `liftKZ`,
`polyDepthZ`.

## The four faces

### 1. Universal identity (`newton_gregory`)

For **every** `s : ℕ → ℤ` and all `m, n`:

> `s(m + n) = Σ_{j=0}^{n} binom(n,j) · (Δʲ s)(m)`.

No polynomiality hypothesis — it is `Eⁿ = (I+Δ)ⁿ` expanded by the binomial theorem
for the commuting operators `E`, `Δ`.  Proof: one induction on `n` generalized over
the base point `m`; each step expands `(Δʲs)(m+1) = (Δʲs)(m) + (Δʲ⁺¹s)(m)` and
Pascal-recombines the binomial weights (`bsum_pascal`).

### 2. Inverse transform (`newton_gregory_inverse`)

> `(Δⁿ s)(m) = Σ_{j=0}^{n} (−1)^{n−j} binom(n,j) · s(m + j)`.

The matched `Δⁿ = (E − I)ⁿ`.  Together with face 1 this exhibits the binomial
transform `F : s ↦ (Δʲs)(0)` and its sign-twisted partner `G` as a mutually
inverse pair — `binomial_transform_roundtrip` bundles `F ∘ G = id`.  A sequence and
its iterated differences-at-a-point are **one object in two bases** (monomial ⇄
Pólya–Ostrowski/binomial), not two objects.  The sign is carried *without* a second
Pascal induction: on the effective range `j ≤ n` (where `binom n j ≠ 0`),
`(−1)^{n−j} = (−1)ⁿ·(−1)ʲ`, so the inverse sum is `(−1)ⁿ · bsum n (fun j => (−1)ʲ
s(m+j)) n` and the already-proven `bsum_pascal` carries it.

The transform is an involutive change of basis with a **rich fixed-point set** (any
±1-eigen-sequence is fixed): grounding (Nat-style, §5.2), not the fixed-point-free
oscillation of a Bool-style liar.  Characterizing that eigenspace ∅-axiom is the
open frontier (see below).

### 3. Reconstruction (`reconstruct`)

For a faithfully depth-`d` sequence (`polyDepthZ d s`):

> `s n = Σ_{i=0}^{d} (Δⁱ s)(0) · binom(n, i)`.

Every such sequence is its own Newton series, truncated at `d`, with coefficients
the iterated differences-at-`0` — the Pólya–Ostrowski coordinates (the `binom(·,i)`
ℤ-basis of integer-valued polynomials, Pólya 1915 / Ostrowski 1919).  Corollary of
face 1 once `Δʲs ≡ 0` for `j > d`.  **This is the converse `ℕ` could not state**
(HANDOFF Open Problem #4).

### 4. Polynomial growth bound (`poly_bound`)

> `polyDepthZ d s ⟹ |s n| ≤ C · (n+1)^d`,  with `C = Σ_{i≤d} |(Δⁱ s)(0)|`.

Read off face 3 + the ℤ triangle inequality (`natAbs_add_le`, proved ∅-axiom
since core `Int.natAbs_add_le` pulls `propext`) + `binom n i ≤ (n+1)ⁱ ≤ (n+1)^d`.
This is the ∅-axiom half of the classical chain **Hurwitzian (quasi-polynomial
partial quotients) ⟹ partial quotients polynomially bounded ⟹ irrationality
measure `μ = 2`** (the `μ = 2` step is classical, cited); it unblocks the general
bridge `QuasiPolyCF ⟹ polynomially-bounded` that was Newton–Gregory-blocked over
`ℕ`.

## The obstruction, pinned

The witness `vObs` = the genuine nonneg values `2, 0, 0, 2, 6, 12, …` of
`(n−2)(n−1)`.  The **values are identical** in `ℕ` and `ℤ`; the genuine first
difference `s(1) − s(0) = −2` is faithful over `ℤ` but clamps to `0` over `ℕ`
(`obstruction_first_diff_clamp`).  That single clamp makes the `ℕ` second
difference jump `0, 2, 2, …` — so `¬ polyDepth 2 vObs` (`obstruction_nat`) — while
the `ℤ` second difference is the constant `2` (`obstruction_int_constant`).
ℕ-`diff` is therefore a **different Lens**, agreeing with ℤ-`diff` exactly on the
monotone-difference cone; not a broken one.

## Application — quasi-polynomial CFs are polynomially bounded (closed)

Built directly on `poly_bound` in `Cauchy/QuasiPolyBound.lean` (14 PURE):

> `quasiPolyCFZ_poly_bounded` : `QuasiPolyCFZ p a ⟹ ∃ C D, ∀ n, a n ≤ C·(n+1)^D`.

`QuasiPolyCFZ p a` = every residue section `k ↦ a(p·k+r)`, lifted to `ℤ`, is
genuinely `polyDepthZ`-`dᵣ`.  Each section is bounded by `poly_bound`; the
per-residue bounds are reassembled with a pure finite max and the (pure)
decomposition `n = p·⌊n/p⌋ + n%p`.  By the classical `μ = 2 + limsupₙ(ln a_{n+1}/ln
qₙ)` (cited), polynomially-bounded partial quotients ⟹ `μ = 2` — the ∅-axiom half
of "Hurwitzian ⟹ μ = 2", the general bridge that was Newton–Gregory-blocked over
`ℕ`.  Witnesses: **periodic** CFs (quadratic irrationals, Lagrange) land at degree
0 — *bounded* partial quotients (`periodic_partial_bounded`); **e** = [2;1,2k,1,…]
lands with a linear residue section (`e_cf_quasiPolyCFZ`,
`e_partial_quotients_poly_bounded`), the general machinery subsuming the hand-built
`HurwitzianCF.ePQ_linear_bound`.

## The finite-depth ring (closed)

`Cauchy/FiniteDepthAlgebra.lean` (22 PURE) makes the finite-faithful-depth
`ℤ`-sequences a ring closed under `+`, scalar `·`, shift, and **product with
additive depths**:

> `polyDepthZ_mul` : `polyDepthZ d s → polyDepthZ e t → polyDepthZ (d+e) (s·t)`.

Via the discrete **Leibniz rule** `Δ(s·t) = (E s)(Δt) + (Δs)t` (`diffZ_mul`) driven
through induction on the degree bound (`mul_vanish`, in the vanishing view
`polyDepthZ d s ↔ Δ^{d+1}s ≡ 0`).  This turns the hand-counted depth arithmetic of
`DivergenceDepth` — "a product of a degree-`d` and a degree-`e` discrete polynomial
is degree `d+e`", e.g. π's degree-4 cross-determinant ratio as the product of two
degree-2 Wallis coefficients — into a theorem.

`Cauchy/WallisDepthProduct.lean` (6 PURE) carries this out on the real π data:
`polyDepthZ_affine` (affine ⟹ depth 1), then each Wallis coefficient `4(n+1)²`,
`(2n+1)(2n+3)` is a product of two affine factors (depth 2, `polyDepthZ_mul`), and
π's ratio is their product — `pi_ratio_polyDepthZ` : `polyDepthZ 4` — with **no**
nonlinear-`ℤ` expansion, closing the residual step `DepthPRecursiveInstances` left.

## The involution, and the §5.2 self-reference question (closed)

`Cauchy/BinomialTransform.lean` (6 PURE) makes the "self-inverse Lens" reading a
theorem.  Define the sign-twisted transform `T s n = Σ_{j≤n} (−1)ʲ binom(n,j)
s(j)`.  Then:

> `binomialT_involutive` : `T (T s) = s` — `T` is a genuine **involution** (a
> self-inverse change of basis, Pólya–Ostrowski ⇄ monomial).
> `binomialT_fixed` : for *every* `s`, `s + T s` is a fixed point of `T`.

The proof reuses `binomial_transform_roundtrip`: `T s n = (−1)ⁿ·(Δⁿ s)(0)`
(`binomialT_eq`), and `(−1)ⁿ·(−1)ⁿ = 1` collapses `T∘T` onto the forward Newton
identity.  This **settles the §5.2 question** (`seed/AXIOM/05_no_exterior.md`): the
binomial transform is **fixed-point-rich** — an involution with a large fixed set
(`s + T s` for any `s`) — which is **Nat-style** grounding (a fixed point exists and
the iteration settles), the *opposite* of the fixed-point-free Bool-style liar
oscillation `not ∘ not = id`.  The "two readings of one residue related by an
involution" framing is thereby earned with an actual fixed set, not asserted.

The full spectral picture: `binomialT_antifixed` (`s − T s` is a `−1`-eigenvector)
+ `binomialT_eigendecomp` (`(s + T s) + (s − T s) = 2s`) — `T` has eigenvalues `±1`
and both eigenspaces are large (they span up to a factor 2), the definitive
fixed-point-richness.

## The classification boundary (closed)

`FiniteDepthAlgebra.periodic_finite_depth_const` (§5): a periodic `ℤ`-sequence of
finite faithful depth is **constant**.  So the Newton-reconstructible (finite-depth)
class and the periodic (quadratic-irrational / Markov) class are disjoint apart from
the constants — the boundary of the divergence-depth classification.  Proof:
induction on depth — `diffZ s` is periodic and one depth lower, hence constant `c`
by IH; the sequence is then affine `s k = s 0 + k·c`, and periodicity forces
`p·c = 0` at the period, so `c = 0` and `s` is constant.

## Frontier

- The combinatorial e/π depth separation (e depth 1, π Wallis-coeff depth 2) as a
  bare invariant — *not* a claim about transcendence (classically open).
- Exact depth as a grading: `depth(s·t) = depth s + depth t` (leading-coefficient
  lower bound, complementing the `≤` of `polyDepthZ_mul`).

Anchors: Gregory c.1670 / Newton *Methodus Differentialis* 1711 (operator form);
Rota–Kahaner–Odlyzko 1973 (finite operator calculus; `Δ` a delta operator, falling
factorial its basic sequence); Pólya 1915 / Ostrowski 1919, Cahen–Chabert 1997
(integer-valued-polynomial basis); Hurwitz 1896 (Hurwitzian = integer-valued-
polynomial partial quotients).  Out of ∅-axiom scope (analytic, cited only):
Nörlund–Rice integral; Newton-series convergence / Carlson's theorem.
