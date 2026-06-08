# The Legendre symbol — quadratic residues and their characterizations

The quadratic-reciprocity chapter (`quadratic_reciprocity.md`) is the capstone of a
package of more basic facts about *when an integer is a square mod an odd prime*.  This
chapter collects that package: Euler's criterion, multiplicativity, the two supplements
(`−1` and `2`), and Gauss's lemma — all strict ∅-axiom.

## 213-native answer

There is **no Legendre-symbol primitive** `(a/p)`.  "`a` is a quadratic residue mod `p`"
is a count-Lens reading (`seed/AXIOM/06_lens_readings.md` §6.7): the predicate

```
QR(a) := ∃ x, 1 ≤ x ∧ x < p ∧ x² % p = a
```

— "`a % p` lies in the image of the squaring map `z ↦ z² % p` on `[1,p)`".  Primality is
carried as the divisor condition `∀ d, d ∣ p → d = 1 ∨ d = p`, and the half-system size is
`m = (p−1)/2` (`2·m = p − 1`).  Every "symbol value `±1`" below is the parity bit of an
explicit count or the sign-product over the half-system — the count-Lens read one bit
further by `mod 2`, never an assumed primitive.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/NumberTheory/ModArith/` (the Legendre-symbol files)
- **∅-axiom status**: **54 PURE / 0 DIRTY**

| file | content | PURE |
|---|---|---|
| `EulerCriterion.lean` | `euler_dichotomy`, `euler_qr_pow_one` (the `aᵐ ≡ ±1` dichotomy) | 2 |
| `EulerConverse.lean` | `euler_criterion` (full iff `p ∣ aᵐ−1 ⟺ QR(a)`), `euler_converse`, the squares-list saturation infra (`sqFrom`, `firstSqrt`) | 15 |
| `LegendreMultiplicative.lean` | `qr_iff_pow_one` (Euler's criterion, pow form), `legendre_mul` (multiplicativity) | 5 |
| `EulerFirstSupplement.lean` | `neg_one_qr_iff` (first supplement), `neg_one_pow_dvd_iff_even` | 4 |
| `SecondSupplement.lean` | `two_qr_iff`, `second_supplement` (`2` QR), `gauss_mu` | 8 |
| `GaussLemma.lean` | `gauss_core`, `gauss_qr` (Gauss's lemma) | 20 |

## Key results

| Theorem | Lean | Statement (informal) |
|---|---|---|
| `qr_iff_pow_one` | `LegendreMultiplicative` | **Euler's criterion**: `QR(a) ⟺ aᵐ % p = 1` |
| `euler_criterion` | `EulerConverse` | full iff `p ∣ (aᵐ − 1) ⟺ QR(a)` (converse = squares-list saturation of `RootBound.eval_zero`) |
| `legendre_mul` | `LegendreMultiplicative` | **multiplicativity**: `QR(a·b) ⟺ (QR(a) ⟺ QR(b))` |
| `neg_one_qr_iff` | `EulerFirstSupplement` | **first supplement**: `QR(−1) ⟺ p ≡ 1 (mod 4)` |
| `second_supplement` | `SecondSupplement` | **second supplement**: `QR(2) ⟺ p ≡ 1 ∨ 7 (mod 8)` (i.e. `p ≡ ±1 mod 8`) |
| `two_qr_iff` | `SecondSupplement` | `QR(2) ⟺ ∏_{x∈[1,m]} (2x ≤ m ? 1 : −1) = 1` (the sign-product form) |
| `gauss_qr` | `GaussLemma` | **Gauss's lemma**: `QR(a) ⟺ ∏_{x∈[1,m]} sgFn(a,p,m,x) = 1` |
| `gauss_mu` | `SecondSupplement` | the `μ`-count form feeding the Eisenstein reciprocity route |

## Narrative

**Euler's criterion** is the engine.  `qr_iff_pow_one` reads `QR(a)` as the value of `aᵐ`
mod `p`: `a` is a square exactly when `aᵐ ≡ 1` (and a non-residue gives `aᵐ ≡ −1`, the
`euler_dichotomy`).  The forward direction is a counting argument over the squaring map;
the converse (`euler_converse`) is the **saturation** of the squares list — the `m` squares
`x² % p` for `x ∈ [1,m]` are exactly the residues (each hit, none missed), proven via the
root bound `RootBound.eval_zero` (a degree-`m` polynomial has `≤ m` roots), with the
pure-`cnt` list infrastructure `sqFrom`/`firstSqrt`.

On that base the **Legendre-symbol laws** are corollaries:

- **Multiplicativity** (`legendre_mul`): `QR(a·b)` holds iff `QR(a)` and `QR(b)` agree —
  the `{±1}`-homomorphism law, read as `aᵐ·bᵐ = (ab)ᵐ` through Euler's criterion.  (The
  product over `[1,p)` of the QR predicate is a group homomorphism to `{±1}`, the count-Lens
  on the multiplicative half.)
- **First supplement** (`neg_one_qr_iff`): `−1` is a square iff `(−1)ᵐ ≡ 1`, i.e. `m` even,
  i.e. `p ≡ 1 (mod 4)`.
- **Second supplement** (`second_supplement`): `2` is a square iff the half-system
  sign-product `∏ (2x ≤ m ? 1 : −1)` is `+1` (`two_qr_iff`), which collapses to
  `p ≡ ±1 (mod 8)`.

**Gauss's lemma** (`gauss_qr`) is the bridge to reciprocity: `QR(a)` equals the sign-product
`∏_{x∈[1,m]} sgFn(a,p,m,x)` over the half-system — `sgFn` recording, per `x`, whether `a·x mod p`
exceeds `m`.  The `μ`-form `gauss_mu` (the *count* of sign flips) is what the
`quadratic_reciprocity` chapter refines to the Eisenstein lattice count `Σ ⌊a·x/p⌋`.

## Connection

- `quadratic_reciprocity.md` — the **capstone** that consumes this package: `floor_qr` runs
  `euler_criterion` ∘ `gauss_qr` ∘ `gauss_mu` to express `QR(q mod p)` as a lattice-rectangle
  parity, then the reciprocity law as a count-equality between two halves of `[1,m]×[1,n]`.
- `counting_as_cardinality.md` (`theory/essays/proof_isa/`) — the count-Lens thesis these
  `±1`-as-parity readings instantiate.

## Research-note provenance

Frontier notes `research-notes/frontiers/{reciprocity_count_lens_synthesis (deleted; seeds
folded into frontiers/INDEX), euler_criterion_converse, second_supplement}.md`.

## Open frontier

- **Zolotarev's lemma** — `(a/p) = sign(mul-by-`a` permutation)`: the `psign` machinery
  (`Algebra/Linalg213/Permutation.lean`) is the sign side, `gauss_qr` the count side; whether
  the count-Lens reading unifies them as one permutation read two ways is open
  (`frontiers/INDEX.md`, reciprocity seeds).
- **Cubic / biquadratic reciprocity** over `ℤ[ω]` / `ℤ[i]` — the same count-Lens question on
  a 2-D residue lattice.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.NumberTheory.ModArith.EulerConverse \
  E213.Lib.Math.NumberTheory.ModArith.GaussLemma \
  E213.Lib.Math.NumberTheory.ModArith.SecondSupplement
python3 tools/scan_axioms.py E213.Lib.Math.NumberTheory.ModArith.EulerCriterion \
  E213.Lib.Math.NumberTheory.ModArith.EulerConverse \
  E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative \
  E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement \
  E213.Lib.Math.NumberTheory.ModArith.SecondSupplement \
  E213.Lib.Math.NumberTheory.ModArith.GaussLemma   # → 54 pure / 0 dirty
```
