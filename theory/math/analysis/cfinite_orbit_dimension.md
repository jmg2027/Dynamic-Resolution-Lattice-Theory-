# C-finite and the orbit-dimension ladder — above the polynomials

**Status**: The `+`-ring, the orbit-recurrence ⟺ annihilator characterization, the
**orbit dimension = recurrence order** equivalence, and the **Hadamard (pointwise) product**
`s·t` (the full ring — closed via integer Cayley–Hamilton) are all closed.  So the **C-finite
sequences are a commutative ring** under `+` and pointwise `·`.  Source of truth (all ∅-axiom):
`lean/E213/Lib/Math/Analysis/Cauchy/OrbitDimension.lean` (32 PURE), `CFiniteRing.lean` (82 PURE), and
`CFiniteHadamard.lean` (21 PURE, the Hadamard product), on the `Linalg213` determinant +
Cayley–Hamilton tower.

## Overview

[`divergence_depth_characterization.md`](divergence_depth_characterization.md) pins the
**bottom** of the divergence ladder exactly: a `ℤ`-sequence has finite faithful divergence
depth `d` iff it is a degree-`d` polynomial — depth is `Δ`-nilpotency, and nilpotency is the
whole content of "polynomial."  But the divergence-depth axis is **coarse above the
polynomials**: it bins `2ⁿ`, `e`'s value sequence, Fibonacci, and the Liouville numbers all
into the single class `∞`, seeing only *polynomial / not*.

The finer invariant is the **dimension of the `Δ`-orbit** `⟨s, Δs, Δ²s, …⟩`.  A **C-finite**
sequence is one whose top difference is a `ℤ`-linear combination of the lower ones —
`Δᵏ s = Σ_{i<k} cᵢ Δⁱ s`, a *monic constant-coefficient* annihilator `p(Δ) s ≡ 0` — so the
orbit is finite-dimensional, of dimension `≤ k`.  The orbit dimension counts how many
independent self-relations the generating rule carries: `0` for a polynomial (the orbit dies),
`1` for a geometric sequence, `2` for Fibonacci.  This chapter is the rung strictly above the
polynomials, and the algebraic structure carried on it — a commutative ring under `+`.

  | class | annihilator | orbit dimension | divergence depth |
  |---|---|---|---|
  | polynomial (degree `d`) | `Δ^{d+1} s = 0` | `d+1`, then `0` | `d` (finite) |
  | geometric `cⁿ` (`c ≠ 1`) | `(Δ − (c−1)) s = 0` | `1` | `∞` |
  | Fibonacci | `(Δ² + Δ − I) s = 0` | `2` | `∞` |
  | C-finite (general) | `p(Δ) s = 0`, `p` monic over `ℤ` | finite | `∞` (unless polynomial) |

## Lean source

| Theorem | Module | Statement (informal) |
|---|---|---|
| `CFiniteZ` | `OrbitDimension` | `∃ k c, ∀ n, Δᵏs n = Σ_{i<k} cᵢ Δⁱs n` (monic `Δ`-orbit recurrence) |
| `twoPow_is_diffZ_fixed` | `OrbitDimension` | `Δ(2ⁿ) = 2ⁿ` — the geometric eigen-identity |
| `polyDepthZ_cfiniteZ` | `OrbitDimension` | polynomial ⟹ C-finite (annihilator `Δ^{d+1}`) |
| `cfiniteZ_twoPow` | `OrbitDimension` | `2ⁿ` is C-finite (annihilator `Δ − 1`, orbit dim 1) |
| `twoPow_not_polyDepthZ` | `OrbitDimension` | `2ⁿ` is not a polynomial — the strict inclusion |
| `cfiniteZ_geom` / `geom_not_polyDepthZ` | `OrbitDimension` | every `cⁿ` is C-finite (orbit dim 1); not polynomial for `c ≠ 1` |
| `cfiniteZ_fib` | `OrbitDimension` | Fibonacci is C-finite (orbit dim 2) |
| `cassini_fibZ_step` | `OrbitDimension` | the Fibonacci Cassini det `Cₙ = fibₙfibₙ₊₂ − fibₙ₊₁²` oscillates `Cₙ₊₁ = −Cₙ` — the orbit's conserved unit `±1` |
| `cfiniteZ_zero` / `cfiniteZ_neg` / `cfiniteZ_smul` | `OrbitDimension` | the `ℤ`-module structure |
| `cfiniteZ_geom_mul` | `OrbitDimension` | `cⁿ·dⁿ = (cd)ⁿ` is C-finite — the geometric Hadamard case |
| `applyOp` / `conv` / `applyOp_comm` | `CFiniteRing` | the difference-operator algebra; operators commute |
| `applyOp_conv` | `CFiniteRing` | `(p·q)(Δ) = p(Δ) ∘ q(Δ)` — convolution is operator composition |
| `conv_annih_add` | `CFiniteRing` | `p` annihilates `s`, `q` annihilates `t` ⟹ `p·q` annihilates `s+t` |
| `cfiniteZ_to_annih` / `annih_snoc_to_cfiniteZ` | `CFiniteRing` | C-finite ⟺ has a monic constant-coefficient annihilator |
| `cfiniteZ_add` / `cfiniteZ_sub` | `CFiniteRing` | C-finite is closed under `±` — a ring under `+` |
| `applyOp_shift` / `applyOp_ePow` | `CFiniteRing` | `E = applyOp [1,1] = I+Δ`; `Eᵏ` as a `Δ`-operator, `applyOp (ePow k) s n = s(n+k)` |
| `applyShift_diffBase` / `applyShift_dPow` | `CFiniteRing` | `Δ = applyShift [-1,1] = E−I`; `Δᵏ` as a shift operator, `applyShift (dPow k) s n = Δᵏs(n)` |
| `cfiniteZ_iff_shiftRec` | `CFiniteRing` | **C-finite ⟺ has a monic shift recurrence** — orbit dimension = recurrence order |
| `cfiniteZ_geomScale` | `CFiniteRing` | `cⁿ · s` is C-finite for every C-finite `s` (Hadamard, geometric factor) |
| `cfiniteZ_geomCombo_mul` | `CFiniteRing` | `(Σ aᵢcᵢⁿ) · t` is C-finite (Hadamard, explicit-spectrum factor) |
| ★★★ `cfiniteZ_mul` | `CFiniteHadamard` | **`s·t` is C-finite for any C-finite `s,t`** (the full Hadamard product, via integer Cayley–Hamilton) — the C-finite sequences are a commutative ring |

## Narrative

### The strict inclusion

`Δ(2ⁿ) = 2ⁿ` (`twoPow_is_diffZ_fixed`): `2^(n+1) − 2^n = 2·2^n − 2^n = 2^n`, so the geometric
sequence is a **fixed point of the difference operator**.  Every iterate fixes it
(`liftKZ_twoPow_fixed`), so the `Δ`-orbit is the single line `⟨2ⁿ⟩` — it never collapses to
`0`, and `2ⁿ` has no finite divergence depth.  Yet it is annihilated by the monic operator
`Δ − 1` (`cfiniteZ_twoPow`), orbit dimension `1`.  Since `Δᵏ(2ⁿ) = 2ⁿ` is never `≡ 0`
(`2⁰ = 1 ≠ 0`), `2ⁿ` is not a polynomial (`twoPow_not_polyDepthZ`).  Polynomials embed
(`polyDepthZ_cfiniteZ`, with the pure-monomial annihilator `Δ^{d+1}`), so the inclusion
`polynomial ⊊ C-finite` is strict.

The general geometric family `cⁿ` carries the same structure for every base: `Δ(cⁿ) = (c−1)·cⁿ`
(`geom_diffZ`), `Δᵏ(cⁿ) = (c−1)ᵏ·cⁿ` (`liftKZ_geomZ`), C-finite with annihilator `Δ − (c−1)`
(`cfiniteZ_geom`), and not polynomial unless `c = 1` (`geom_not_polyDepthZ`, since `(c−1)ᵏ⁺¹ = 0`
forces `c = 1` over `ℤ`).  Fibonacci is the first **non-geometric** witness: the shift
recurrence `f(n+2) = f(n+1) + f(n)` becomes the `Δ`-orbit recurrence `Δ²f = f − Δf` (because
`E² − E − I = Δ² + Δ − I` under `E = I + Δ`), orbit dimension exactly `2` (`cfiniteZ_fib`).  Its
`2×2` Casoratian (Cassini cross-determinant) is the **conserved unit** `±1` oscillating with period
2 (`cassini_fibZ_step`, `cassini_fibZ_zero`): the same unimodular `det Qⁿ = ±1` the number-tower
founding reads as `ℚ`'s lowest-terms / the shared unit `det P = NS − NT = 1` (`RatioLensFounding`),
the period-2 flip being the count-Lens negation — so the C-finite orbit's conserved unit *is* the
founding's shared unit, on the difference axis.

This sits one rung above [`cf_holonomicity_hierarchy.md`](cf_holonomicity_hierarchy.md), where
`2ⁿ` already appears as the inhabitant of the non-Hurwitzian top tier that is *still* C-finite,
witnessing `QuasiPolyCF ⊊ C-finite ⊊ holonomic`.

### The difference-operator algebra

A monic `Δ`-orbit recurrence is annihilation by a difference-operator polynomial.  `applyOp p s`
reads the coefficient list `p` (low-to-high `Δ`-power) as `Σ_i pᵢ Δⁱ s`, peeling `a·s` and
recursing on the differenced sequence.  The algebra is linear (`applyOp_add`, `applyOp_smul`),
commutes with the difference (`applyOp_diffZ`, `p(Δ)(Δs) = Δ(p(Δ)s)`), and — the engine of the
ring — **operator-commutative**: `applyOp_comm` proves `p(Δ) q(Δ) s = q(Δ) p(Δ) s` directly by
induction, because `Δ` commutes with itself.  Coefficient convolution `conv` realizes the
operator product: `applyOp_conv` gives `(p·q)(Δ) = p(Δ) ∘ q(Δ)`.

The two forms of "C-finite" coincide: `cfiniteZ_to_annih` builds, from a `CFiniteZ` recurrence,
the explicit monic operator `Δᵏ − Σ cᵢ Δⁱ` and shows it annihilates `s` (its leading coefficient
is `1`); `annih_snoc_to_cfiniteZ` reads any monic `lo ++ [1]` annihilator back as the orbit
recurrence `Δ^{|lo|}s = Σ cᵢ Δⁱs`.  So **C-finite ⟺ has a monic constant-coefficient
annihilator** — the orbit-recurrence definition is the standard annihilating-polynomial one.

### The ring closure

The headline is that C-finite is closed under pointwise sum.  The mathematical heart is
`conv_annih_add`: if `p` annihilates `s` and `q` annihilates `t`, the product operator `p·q`
annihilates `s + t` — the constant-coefficient annihilators **multiply** (the orbit dimensions
add).  The proof needs no resultant: `conv_annih_left`/`right` use operator commutativity to
show the product kills whatever either factor kills, and linearity finishes the sum.

`cfiniteZ_add` upgrades this to the predicate level.  The only delicacy is that the combined
annihilator must be monic to read back as an orbit recurrence: `conv_snoc` proves the leading
coefficients of two snoc-lists multiply (`1·1 = 1`), with the `+0`/`*1` arithmetic noise that
`addL` injects absorbed by stating the leading value existentially.  A small `Nat.max`-free list
toolkit (`length_snoc`, `smulL_snoc`, `addL_snoc_right`, `length_addL_right_ge`, `opOf_snoc`)
carries the degree bookkeeping.  With `cfiniteZ_zero` (the zero sequence), `cfiniteZ_neg`
(`−s = (−1)·s`), and `cfiniteZ_sub`, the C-finite sequences form an **abelian group under `±`**,
a commutative ring under `+`.  `cfiniteZ_one_add_twoPow` exhibits `1 + 2ⁿ` as a concrete witness
the sum generates: C-finite, yet neither polynomial nor geometric.

### Orbit dimension and recurrence order

The orbit dimension (the `Δ`-recurrence order) and the classical **shift recurrence order**
coincide.  The bridge is that the forward shift is itself a difference operator: `E = applyOp
[1,1] = I + Δ` (`applyOp_shift`, `(I+Δ)s(n) = s(n) + (s(n+1)−s(n)) = s(n+1)`), so `Eᵏ` is the
`Δ`-operator `(I+Δ)ᵏ`, built by convolving `[1,1]` with itself `k` times, and `applyOp (ePow k)
s n = s(n+k)` (`applyOp_ePow`) — with no binomial sums.

Both directions close, giving `cfiniteZ_iff_shiftRec`: **`CFiniteZ s ↔ ∃ K b, ShiftRecZ K b s`**.
The reverse (`cfiniteZ_of_shiftRec`) reads a monic order-`k` shift recurrence `s(n+k) = Σ_{i<k} bᵢ
s(n+i)` (the standard definition of a constant-recursive / C-finite sequence) as the `Δ`-operator
annihilator `ePow k − Σ bᵢ ePow i`, monic of degree `k` because the lower `ePow i` are strictly
shorter.  The forward (`shiftRec_of_cfiniteZ`) is the exact mirror: a dual shift-operator algebra
`applyShift` carries `Δ = applyShift [-1,1] = E − I` (`applyShift_diffBase`) and `Δᵏ` as the shift
operator `dPow k = (E−I)ᵏ` (`applyShift_dPow`), so the `Δ`-orbit recurrence becomes the *shift*
annihilator `dPow k − Σ cᵢ dPow i`, monic of degree `k`, which reads off as the shift recurrence.
So the two notions of order — the `Δ`-orbit dimension and the shift recurrence order — are one;
`CFiniteZ` is exactly the standard constant-recursive class.  `cfiniteZ_fib_via_shift` validates
the reverse end-to-end (Fibonacci's natural shift recurrence ⟹ `CFiniteZ fibZ`, orbit dimension 2).

The forward-difference calculus that underwrites the two pictures — `s(n+m) = Σ binom(m,j) Δʲs(n)`
and its inverse `Δⁿ = (E−I)ⁿ` — is the binomial transform of
[`newton_gregory.md`](newton_gregory.md); here the change of basis is carried *operator-side* by
`ePow`/`dPow` (convolutions of `[1,1]`/`[-1,1]`), with no binomial sums.

## The Hadamard product (closed) — integer Cayley–Hamilton

**The general pointwise product `s·t` is C-finite** (`CFiniteHadamard.cfiniteZ_mul`, ∅-axiom),
for any C-finite `s, t` — including both-non-split factors with irrational spectra (`fib·fib`).
This was the last ring operation; the C-finite sequences are now a full commutative ring.

The corners came first and remain the cheap routes when a factor splits: `cfiniteZ_geomScale`
(`cⁿ · s` for every C-finite `s` — a geometric weight rescales the shift coefficients,
`(cⁿs)(n+k) = Σ aᵢ c^{k−i} (cⁿs)(n+i)`) and `cfiniteZ_geomCombo_mul` (`(Σ aᵢ cᵢⁿ) · t`, the
multiplicative root-pairing one geometric at a time).

The **general** construction realizes the tensor of the two shift recurrences.  If `s` satisfies a
monic order-`p` shift recurrence and `t` order-`q`, the `pq` products `w(n)_{(a,b)} = s(n+a)·t(n+b)`
are closed under the shift, `w(n+1) = M·w(n)` for a fixed `pq×pq` integer **Kronecker companion** `M`
(`CFiniteHadamard.vecRec`; `M` factors as `Ms·Mt` since the `s`- and `t`-shifts are independent).
The characteristic roots multiply pairwise, and the monic-over-`ℤ` annihilator that `CFiniteZ`
strictly requires is the characteristic polynomial `χ_M = det(X·I − M)` — which the
**determinant-free** routes (finite-orbit linear dependence; the power-sum twin of `conv`,
`pₗ(αβ)=pₗ(α)pₗ(β)` with Newton's identities) cannot reach (they give only *non-monic* relations, the
power-sum `÷k` integrality being "the determinant in disguise").  So the proof goes through the full
`n×n` determinant: a ∅-axiom **integer Cayley–Hamilton** `χ_M(M) = 0`
(`Linalg213.CharPolyAdj.cayley_hamilton`), built on the Leibniz determinant
(`Linalg213.Permutation`/`PermClosure` — alternating via antisymmetrization), cofactor expansion and
the adjugate identity `M·adj M = det M·I` (`Linalg213.Laplace`), lifted to `ℤ[X]` by polynomial
uniqueness (`PolyZ.coeff_unique`).  The **recurrence bridge** `CharPolyAdj.ch_recurrence` then turns
`χ_M(M)=0` into the monic order-`pq` recurrence on the first component `w_{(0,0)} = s·t`, with the
leading coefficient `1` from monicity (`PolyDet.charPoly_monic`), and `cfiniteZ_of_shiftRec` closes
it.  `Linalg213.FibCassiniDet` grounds the base size: `det 2` of the Fibonacci Casoratian
`[[fibₙ, fibₙ₊₁], [fibₙ₊₁, fibₙ₊₂]]` is exactly the orbit's conserved unit `(−1)ⁿ⁺¹` (= `det Qⁿ`).
`FiniteDepthAlgebra.polyDepthZ_mul` (see [`newton_gregory.md`](newton_gregory.md)) is the finite-
*depth* analogue via the discrete Leibniz rule.

## Open frontier

Two directions remain, in rough difficulty order.

- **Casoratian rank = orbit dimension** — C-finite iff the Hankel/Casoratian determinants of the
  shift-orbit eventually vanish, the orbit dimension equalling that rank.  **The forward direction is
  done** (`CasoratianRank.casoratian_det_zero`, ∅-axiom): a sequence with a monic order-`k` shift
  recurrence has its `(k+1)×(k+1)` Casoratian (Hankel) determinant `det [s(n+i+j)] ≡ 0`, because the
  bottom row is the recurrence combination of the upper rows — a direct application of
  `Linalg213.RowDependence.det_row_combo_zero` (row dependence ⟹ `det=0`, from the new determinant
  tower's multilinearity + alternating).  The *converse* (Casoratian rank `k` ⟹ C-finite of order
  `k`) remains — a Cramer/rank argument extracting the recurrence from the vanishing minors.
  Connects to the discrete-Wronskian work of `divergence_depth_characterization.md`
  (`CasoratianStep`/`CasoratianSigned`).

- **Holonomic = `ℚ(n)`-orbit** — the top rung of the ladder, where the recurrence coefficients are
  rational *functions* of `n` rather than constants (the Apéry `ζ(3)` numerators are the model
  inhabitant, holonomic but neither polynomial nor C-finite).  The full two-coordinate
  classification (recurrence order, coefficient degree) of a P-recursive sequence lives here.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Analysis.Cauchy.OrbitDimension E213.Lib.Math.Analysis.Cauchy.CFiniteRing
cd ..
python3 tools/scan_axioms.py E213.Lib.Math.Analysis.Cauchy.OrbitDimension
python3 tools/scan_axioms.py E213.Lib.Math.Analysis.Cauchy.CFiniteRing
```
Reports `32 pure / 0 dirty` and `82 pure / 0 dirty`.
