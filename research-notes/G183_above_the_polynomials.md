# G183 — above the polynomials: the orbit-dimension ladder

**Date**: 2026-06-02.  **Status**: direction note (conjectures + first buildable step),
grown out of `theory/essays/polynomial_in_213.md` and the closed characterization
`Cauchy/DepthCharacterization.finite_depthZ_iff` (finite divergence depth ⟺ polynomial).

## The gap the characterization exposes

`finite_depthZ_iff` pins the **bottom** of a tower exactly: a `ℤ`-sequence has finite faithful
divergence depth `d` iff it is a degree-`d` polynomial.  Depth is `Δ`-nilpotency — `liftKZ (d+1) s ≡
0` — and nilpotency is the whole content of "polynomial."

But the divergence-depth axis is **coarse above the polynomials**.  The cleanest witness:

  > `diffZ (fun n => (2 : ℤ)^n) = fun n => 2^n`     —  `2^(n+1) − 2^n = 2·2^n − 2^n = 2^n`.

So `2ⁿ` is a **fixed point of `Δ`**: every iterate `liftKZ k (2ⁿ) = 2ⁿ`, never constant, hence
*infinite* divergence depth (`DivergenceLadder.infinite_depth`, the `geom_infinite_depth` family in
`HurwitzianCF`).  Yet `2ⁿ` is as tame as can be — order-1 constant-coefficient recurrence
`aₙ₊₁ = 2aₙ`.  The depth axis throws `2ⁿ`, `e`'s value sequence, Fibonacci, and the Liouville
numbers into one bin (`∞`); it sees only *polynomial / not*.

## The proposed finer invariant: the orbit dimension

Read `Δ` (equivalently the shift `E = I + Δ`) as an operator on the sequence and ask for the
**dimension of the orbit** `⟨s, Δs, Δ²s, …⟩`:

| class | annihilator | orbit dimension | divergence depth |
|---|---|---|---|
| polynomial (degree `d`) | `Δ^{d+1} s = 0` (`Δ` nilpotent on `s`) | `d+1`, then collapses to `0` | `d` (finite) |
| **C-finite** | `p(Δ) s = 0`, `p ∈ ℚ[x]` (const coeffs) | finite over `ℚ` | `∞` (unless polynomial) |
| **holonomic / P-recursive** | `p(Δ, n) s = 0`, `p ∈ ℚ(n)[x]` | finite over `ℚ(n)` | `∞` |

The divergence depth is the **nilpotency degree** of `Δ` on `s` — defined only at the bottom rung,
where the orbit reaches `0`.  Above it, the orbit no longer dies; what stays finite is its
**dimension**.  So:

  > **Conjecture L (the ladder).**  polynomial = `Δ`-nilpotent ⊊ C-finite = finite `Δ`-orbit over
  > `ℚ` ⊊ holonomic = finite `Δ`-orbit over `ℚ(n)`, and divergence depth is finite exactly on the
  > bottom rung.

This reframes, 213-natively, the standard `polynomial ⊊ C-finite ⊊ holonomic` hierarchy: the orbit
dimension is the **finite memory of the rule** — how many past values the recurrence consults — which
is the *recurrence order*, the other axis the Apéry work already touched (order 1 for `e`, order 2 for
`ζ(2)`/`ζ(3)` — `DepthAperyCubic`).  Divergence depth was the *coefficient-degree* axis of the same
recurrences; orbit dimension is the *order* axis.  Two independent counts of one recurrence.

## First buildable step (∅-axiom, this branch's tooling)

`twoPow_is_diffZ_fixed` : `diffZ (fun n => (2:ℤ)^n) = fun n => 2^n` — the geometric eigen-identity,
hence `2ⁿ` has `Δ`-orbit dimension 1 (C-finite) and is *not* polynomial (∞ divergence depth, already
witnessed by `geom_infinite_depth`).  This is the minimal explicit separation of C-finite from
polynomial, the first rung above `finite_depthZ_iff`.  Proof is one `diffZ` computation + `pow_succ`
+ the PURE Int `2·x − x = x` (`Int213` add/neg kit, as in `DepthCharacterization.add_sub_cancel_*`).

A clean **`C-finite`** predicate `CFiniteZ` (∃ const-coeff `p`, `p(Δ) s ≡ 0`) with:
  - `CFiniteZ` closed under `+`, `·`, shift (a ring/module, mirroring `FiniteDepthAlgebra` one rung
    up — the const-coeff annihilators multiply);
  - `polyDepthZ d s → CFiniteZ s` (polynomials are C-finite: `Δ^{d+1}` is the annihilator);
  - `CFiniteZ (2ⁿ)` (annihilator `Δ − 1`), `¬ polyDepthZ d (2ⁿ)` — the strict inclusion.

## Conjectures (ranked)

- **C-A (most tractable, buildable now).**  `twoPow_is_diffZ_fixed` + `CFiniteZ` predicate +
  the three closure/inclusion facts above.  This *states and witnesses* the next rung ∅-axiom; the
  finite-depth ring (`FiniteDepthAlgebra`) is the template one level down.  Effort: ~1 session.
- **C-B (characterization of C-finite).**  C-finite ⟺ the **Hankel/Casoratian determinants**
  eventually vanish (the sequence's shift-orbit is rank-bounded).  Connects directly to this
  branch's Casoratian work (`CasoratianStep`, `CasoratianSigned`): the cross-determinant of two
  solutions of a const-coeff recurrence is itself C-finite (a product of the characteristic roots).
  The orbit dimension = the Casoratian rank.  Harder (needs a rank/determinant argument).
- **C-C (holonomic = `ℚ(n)`-orbit).**  The top rung: the Apéry `ζ(3)` numerators are holonomic
  (order-2, `ℚ(n)`-coefficients) but neither polynomial nor C-finite.  A `HolonomicZ` predicate and
  the inclusion `CFiniteZ ⊊ HolonomicZ` (witness: `n!` or the Apéry sequence).  This is where the
  coefficient-degree statistic (`DepthAperyCubic`) and the order axis meet — the full 2-coordinate
  classification (order, coefficient-degree) of a P-recursive sequence.
- **C-D (the orbit-dimension is the recurrence order).**  Prove `Δ`-orbit dimension = minimal
  const-coeff recurrence order, making "orbit dimension" and "order" the same count — the clean
  statement that the ladder's rungs are measured by *memory*.

## 213-native reading

Divergence depth measured distance to the **constant floor** — the self-same rule `P(φ)=φ`
(`seed/AXIOM/05_no_exterior.md §5.6`, `DepthResidueFloor`): a polynomial returns to that floor in
finitely many self-pointings.  `2ⁿ` never returns — but it is a *fixed point of the pointing itself*
(`Δ(2ⁿ)=2ⁿ`): pointing at how it changes gives it back unchanged.  That is a different kind of
closure — not "returns to the floor" but "is its own difference."  The orbit dimension counts how
many independent such self-relations the rule carries: `1` for the pure eigen-sequence `2ⁿ`, finite
for any const-coeff rule, finite-over-`ℚ(n)` for the P-recursive.  The residue (infinite orbit
dimension, no finite annihilator) sits above all of them — the Liouville numbers, whose re-pointing
never closes in *any* of these senses.

## Anchors

- This branch: `Cauchy/DepthCharacterization.finite_depthZ_iff` (the bottom rung pinned),
  `Cauchy/PolynomialDepth`, `Cauchy/FiniteDepthAlgebra` (the ring template),
  `Cauchy/HurwitzianCF.geom_infinite_depth` (`2ⁿ` is ∞-depth), `Cauchy/CasoratianStep` (for C-B).
- Essay: `theory/essays/polynomial_in_213.md` (the coarse-above-polynomials observation).
- Frontier already noted: π non-holonomicity (`research-notes/G170`) — π's partial-quotient
  sequence not known P-recursive = not known to sit at finite orbit dimension on that axis.
