# Convolution generating functions — the cut comultiplication and its semiring

## Overview

A sequence `f : ℕ → ℕ` is a **generating function read coefficient-by-coefficient**;
its product is the **Cauchy convolution** `conv f g n = Σ_{i+j=n} f i · g j`, computed by
the **cut comultiplication** `natSplits n = [(0,n), (1,n−1), …, (n,0)]` — the explicit ℕ
co-operation that cuts `n` into ordered pairs. This chapter records the closed ∅-axiom
algebra of `conv`: it is a commutative semiring with unit `δ`, carries a derivation (the
formal derivative obeys Leibniz), its `ones`-convolution is the discrete antiderivative
(prefix sum), and its binomial row `brow m = C(m,·)` makes Pascal's triangle a
**convolution power**. The figurate sum identities (odds, triangular, Nicomachus,
sum of squares, hexagonal, tetrahedral) are applications of the same prefix-sum machine.

The structural reading: **commutativity and associativity of `conv` are both shadows of a
swap/reglue symmetry of `natSplits`** — `conv_comm` from cut-reversal, `conv_assoc` from
the *coassociativity* of the cut (cutting `n` into three pieces two ways enumerates the
same `{(i,j,k) : i+j+k=n}`). This is the **sequence-scale rung** of the slot-programme
doctrine "comm/assoc are shadows of a comultiplication swap symmetry", alongside `+`
(`UnitList.append_comm`) and `×` (`UnitGrid.mul_comm_from_grid`).

## Lean source

- Umbrella: `lean/E213/Lib/Math/Combinatorics.lean`
- Files:
  - `Meta/Nat/Convolution213.lean` (408 lines) — `natSplits`, `conv`, the semiring,
    coassociativity, the derivation
  - `Lib/Math/Combinatorics/ConvolutionPrefixSum.lean` (68) — `conv ones` = prefix sum
  - `Lib/Math/Combinatorics/ConvolutionBinomial.lean` (167) — `brow`, `convPow`, Vandermonde,
    binomial theorem, exponential law
  - `Lib/Math/Combinatorics/CatalanSegner.lean` (89) — Catalan as the convolution self-square
  - `Lib/Math/Combinatorics/SumIdentities.lean` (76) — figurate sums via the prefix sum
- ∅-axiom status: 0 DIRTY, all PURE (`#print axioms` empty — verified, e.g.
  `ConvolutionBinomial` reports 12 pure / 0 dirty).

## Narrative

### The cut comultiplication and the semiring

`natSplits n` enumerates every ordered cut `(i, j)` with `i + j = n` (sound by
`natSplits_sound`, length `n+1` by `length_natSplits`). `conv f g n` sums `f i · g j` over
those cuts (`sumMap`). The unit is `δ = [1, 0, 0, …]` (`conv_delta_left`,
`conv_delta_right`: only the cut `(0,n)` / `(n,0)` survives). `conv` is right- and
left-bilinear (`conv_add_left`, `conv_add_right`, `conv_smul_left`) and commutative
(`conv_comm`, from the cut-reversal swap). Associativity (`conv_assoc`) is the
**coassociativity** of `natSplits`, proven in the same end-peel style — peel the outer-left
cut on both sides; the shifted head splits by bilinearity + scalar linearity, the inner
block folds by induction, the heads agree by `mul_assoc`. So `(ℕ→ℕ, +, conv, δ)` is a
commutative semiring.

### The formal derivative is a derivation

`deriv f n = (n+1)·f(n+1)` (shift-and-weight). It is additive (`deriv_addSeq`), scalar
(`deriv_smul`), kills the unit (`deriv_delta = 0`), and obeys the **Leibniz rule**
`deriv (conv f g) = conv (deriv f) g + conv f (deriv g)` (`conv_deriv_leibniz`,
`deriv_is_derivation`) — the semiring is a **differential ring** in the 213-native sense.

### Prefix sum is the discrete antiderivative

`conv ones f n = Σ_{j≤n} f j` (`conv_ones_prefixSum`): convolving with the constant `1`
sequence is the **discrete integral**. Hence `conv ones ones n = n+1`
(`conv_ones_ones`, the cut-count generating function `1/(1−x)²`), and iterating gives the
double prefix sum (`conv_ones_ones_prefixSum`) — the discrete `∫∫`.

### Binomial rows: Pascal is a convolution power

`brow m k = C(m,k)` is the `m`-th binomial row. **Vandermonde** is a convolution product:
`conv (brow a) (brow b) k = C(a+b, k)` (`conv_brow`). Defining `convPow f n` as the `n`-fold
self-convolution, the **binomial theorem** is `convPow (brow 1) n k = C(n,k)`
(`convPow_brow1`) — `(1+x)ⁿ` is the `n`-th convolution power of `1+x`. The
**exponential law** `convPow_add : convPow f (m+n) = conv (convPow f m) (convPow f n)`
makes `n ↦ (1+x)ⁿ` a monoid homomorphism `(ℕ,+) → (conv-powers)`, and
`convPow (brow a) n k = C(a·n, k)` (`convPow_brow_gen`) the generalized power.

### Catalan as the convolution self-square

`catSeg` (Segner's Catalan numbers) satisfies `catSeg (n+1) = conv catSeg catSeg n`
(`catSeg_succ`) — the Catalan generating function is the fixed point `C = 1 + x·C²`, here
the **convolution self-square** with a shift, derived from the segment recursion
`catSegF`/`catSegF_eq` (the partial-sum stabilization at `n ≤ f`).

### Figurate sums are prefix-sum applications

All over the same `sumTo` prefix-sum: `Σ_{i<n}(2i+1) = n²` (`sumTo_odds`),
`2·Σ_{i<n} i = n(n+1)` (triangular, `two_sumTo_id`), **Nicomachus**
`(Σ cubes) = (Σ i)²` (`nicomachus`), `6·Σ i² = n(n+1)(2n+1)` (`six_sumTo_sq`),
hexagonal = triangular (`hexagonal_triangular`), and the tetrahedral identity
`three_sumTo_consec`. These are the prefix-sum machine (`conv ones`) read on the figurate
sequences — the discrete-antiderivative side of the same generating-function ring.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `conv_comm` | Convolution213 | `conv f g = conv g f` (cut-reversal swap) |
| `conv_assoc` | Convolution213 | `conv (conv f g) h = conv f (conv g h)` (coassociativity) |
| `conv_delta_left/right` | Convolution213 | `δ` is a two-sided unit |
| `deriv_is_derivation` | Convolution213 | Leibniz: `deriv` is a derivation on the semiring |
| `conv_ones_prefixSum` | ConvolutionPrefixSum | `conv ones f` = discrete antiderivative |
| `conv_ones_ones` | ConvolutionPrefixSum | `conv ones ones n = n+1` (`1/(1−x)²`) |
| `conv_brow` | ConvolutionBinomial | Vandermonde: `conv (brow a)(brow b) = brow (a+b)` |
| `convPow_brow1` | ConvolutionBinomial | binomial theorem: `convPow (brow 1) n = brow n` |
| `convPow_add` | ConvolutionBinomial | exponential law (monoid hom `+ → conv`) |
| `catSeg_succ` | CatalanSegner | Catalan = convolution self-square |
| `nicomachus` | SumIdentities | sum of cubes = square of triangular |
| `six_sumTo_sq` | SumIdentities | `6·Σ i² = n(n+1)(2n+1)` |

## Research-note provenance

Convolution coassociativity vein dossier (scout `09_new_vein.md`); the slot-programme
"comm/assoc are shadows of a comultiplication swap symmetry" doctrine (`UnitList.append_comm`,
`UnitGrid.mul_comm_from_grid`). The figurate-sum frontier (`numbersystem_square.md`
prefix-sum applications).

## Open frontier

- The multivariate / `convPow` exponential generating-function side (the `exp` law for
  divided powers) is not built; tracked under the convolution topic in `frontiers/`.
- The Catalan ↔ central-binomial closed form `catSeg n = C(2n,n)/(n+1)` (division by `n+1`)
  is not stated in the ℕ semiring (no division); only the self-square recursion is closed.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Combinatorics
python3 tools/scan_axioms.py E213.Lib.Math.Combinatorics.ConvolutionBinomial
python3 tools/scan_axioms.py E213.Meta.Nat.Convolution213
```
