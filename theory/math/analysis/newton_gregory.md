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

## Frontier

- **Apply to partial quotients**: `QuasiPolyCF ⟹ poly-bounded p.q. ⟹ μ = 2` for
  the ℕ-valued sections (mechanical follow-on to `poly_bound`).
- **Depth-additivity** of the finite-depth ring (`diffZ`-Leibniz), turning π's
  hand-counted "depth 6 = 1+1+4" into a theorem.
- **Fixed-point eigenspace** of the binomial transform — the definable ℤ-subspace
  of `s = Σ (−1)^{n−j} binom(n,j) s(j)`; settles Nat-style vs Bool-style for the
  involution and earns the "self-inverse Lens" reading with an actual fixed set.

Anchors: Gregory c.1670 / Newton *Methodus Differentialis* 1711 (operator form);
Rota–Kahaner–Odlyzko 1973 (finite operator calculus; `Δ` a delta operator, falling
factorial its basic sequence); Pólya 1915 / Ostrowski 1919, Cahen–Chabert 1997
(integer-valued-polynomial basis); Hurwitz 1896 (Hurwitzian = integer-valued-
polynomial partial quotients).  Out of ∅-axiom scope (analytic, cited only):
Nörlund–Rice integral; Newton-series convergence / Carlson's theorem.
