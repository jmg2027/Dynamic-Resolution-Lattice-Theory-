# G183 — above the polynomials: the orbit-dimension ladder

**Date**: 2026-06-02.  **Status**: **Conjecture C-A built** (`Cauchy/OrbitDimension`, 15 PURE) —
the strict inclusion `polynomial ⊊ C-finite` is now an ∅-axiom theorem.  Remaining: the full
`ℤ[Δ]`-ring closure (C-A's product/general-sum part), C-B (Casoratian rank), C-C (holonomic),
C-D (orbit dim = order).  Grown out of `theory/essays/polynomial_in_213.md` and the closed
characterization `Cauchy/DepthCharacterization.finite_depthZ_iff` (finite divergence depth ⟺
polynomial).

## What is built (`lean/E213/Lib/Math/Cauchy/OrbitDimension.lean`, 15 PURE / 0 DIRTY)

- `twoPow_is_diffZ_fixed` : `Δ(2ⁿ) = 2ⁿ` — the geometric eigen-identity, via `ring_intZ` over
  the core-free `powInt` (`2·2ⁿ − 2ⁿ = 2ⁿ`).
- `liftKZ_twoPow_fixed` : every iterate `Δᵏ(2ⁿ) = 2ⁿ` — the orbit is the single line `⟨2ⁿ⟩`.
- `CFiniteZ s := ∃ k c, ∀ n, Δᵏs n = Σ_{i<k} cᵢ·Δⁱs n` — the monic constant-coefficient
  `Δ`-orbit recurrence (finite orbit dimension), with `linComb` the lower-part sum.
- `polyDepthZ_cfiniteZ` : **polynomial ⟹ C-finite** (zero lower part; annihilator `Δ^{d+1}`).
- `cfiniteZ_twoPow` : **`2ⁿ` C-finite** (annihilator `Δ − 1`, orbit dim 1).
- `twoPow_not_polyDepthZ` : **`2ⁿ` not polynomial** — the strict inclusion.  (`Δᵏ(2ⁿ)=2ⁿ` never
  `≡0` since `2⁰=1≠0`.)  This is C-A's headline.
- `cfiniteZ_smul`, `cfiniteZ_shift`, `cfiniteZ_add_sameRec` : C-finite is a module, shift-stable,
  closed under `+` of sequences sharing one annihilator (the linear half of the ring closure).
- **Concrete witnesses** (`Cauchy/OrbitDimension` §5–§6): the general geometric family `geomZ c = cⁿ`
  (`geom_diffZ` `Δ(cⁿ)=(c−1)cⁿ`, `liftKZ_geomZ`, `cfiniteZ_geom` orbit dim 1, `geom_not_polyDepthZ`
  for `c≠1`) and **Fibonacci** `fibZ` (`cfiniteZ_fib`, orbit dim 2 via `Δ²f=f−Δf`) — concrete
  sequences at orbit dimensions 1 and 2 above the polynomials.
- **Abelian group / module structure**: `cfiniteZ_congr` (respects pointwise eq), `cfiniteZ_zero`,
  `cfiniteZ_neg`, `cfiniteZ_smul`, `CFiniteRing.cfiniteZ_sub` — C-finite is an abelian group under
  `±` (commutative ring under `+`).  `cfiniteZ_geom_mul` (`cⁿ·dⁿ=(cd)ⁿ`) is the geometric instance of
  the open Hadamard product.
- **C-D foundation** (`CFiniteRing` §8): `applyOp_shift` (`E = applyOp [1,1] = I+Δ`), `ePow k` (`=Eᵏ`
  via `conv` of `[1,1]`), `applyOp_ePow` (`applyOp (ePow k) s n = s(n+k)`) — **the shift is a `Δ`-operator**,
  so a monic shift recurrence is a monic `Δ`-annihilator.  This reduces C-D's reverse direction to
  degree-tracking on `ePow` (no binomial sums); forward direction uses `newton_gregory`(+inverse).

**The operator algebra + ring law are built (`Cauchy/CFiniteRing`, 28 PURE).**

- `applyOp p s = Σ_i pᵢ·Δⁱs` (coefficient list low-to-high `Δ`-power); linearity, `Δ`-commutation,
  and ★ `applyOp_comm` (`p(Δ)q(Δ)s = q(Δ)p(Δ)s` — difference operators commute, *no* `conv_comm`
  needed: commutativity proven directly by induction via `applyOp_diffZ` + linearity).
- `conv` (coefficient convolution) + `applyOp_conv` (`(p·q)(Δ) = p(Δ)∘q(Δ)`).
- ★★★ **the ring law** `conv_annih_add`: `Annih p s → Annih q t → Annih (conv p q) (s+t)`.  The
  constant-coefficient annihilators *multiply* — this IS "C-finite closed under `+`" at the operator
  level (the orbit dimensions add).  Via `conv_annih_left`/`right` (the product kills what either
  factor kills, using `applyOp_comm`).
- **Bridge both ways**: `cfiniteZ_to_annih` (`CFiniteZ ⟹ ∃ monic operator annihilating`, the operator
  is `opOf c k = [−c₀,…,−c_{k-1},1]`, `applyOp_opOf` evaluates it to `Δᵏs−ΣcᵢΔⁱs`) +
  `annih_snoc_to_cfiniteZ` (a monic `lo++[1]` annihilator *is* an orbit recurrence).  So **C-finite ⟺
  has a monic constant-coefficient annihilator** — my orbit-recurrence `CFiniteZ` = the standard
  annihilating-polynomial definition.

**`cfiniteZ_add` is built — the full ring closure under `+`** (`CFiniteZ s → CFiniteZ t →
CFiniteZ (s+t)`).  The monic annihilators of `s`, `t` multiply (`conv_snoc`: leading coefficients
multiply, `1·1=1`) to a monic annihilator of `s+t` (`conv_annih_add`), recovered as an orbit
recurrence (`annih_snoc_unit`).  The `+0`/`*1` syntactic noise `addL` injects is absorbed by stating
`conv_snoc` with an existential leading value (`∃ r v, conv … = r++[v] ∧ v = a·b ∧ |r|=|p|+|q|`).
`Nat.max`-free toolkit: `length_snoc`, `smulL_snoc`, `length_smulL`, `addL_nil_right`,
`addL_zero_cons`, `addL_snoc_right`, `length_addL_right_ge`, `conv_snoc`, `opOf_snoc`.  Concrete
witness `cfiniteZ_one_add_twoPow` (`1+2ⁿ` C-finite, neither polynomial nor geometric).

**Pointwise (Hadamard) product `s·t`** (the other ring operation) is genuinely harder — the
characteristic roots multiply pairwise (tensor of recurrences), degree `k·m` — this is C-B territory
(`DepthCharacterization` already has `polyDepthZ_mul` for the *finite-depth* case via the discrete
Leibniz rule; the C-finite analogue needs the Hadamard/resultant construction).

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

- **C-A (separation + module DONE; ring closure remaining).**  `twoPow_is_diffZ_fixed` +
  `CFiniteZ` predicate + `polyDepthZ_cfiniteZ` + `cfiniteZ_twoPow` + `twoPow_not_polyDepthZ`
  (the strict inclusion) + module/shift/same-annihilator-`+` closure are built ∅-axiom in
  `Cauchy/OrbitDimension` (15 PURE).  The general `+`/`·` ring closure (distinct annihilators)
  is the remaining piece — see "Remaining for the full C-A ring" above.
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
