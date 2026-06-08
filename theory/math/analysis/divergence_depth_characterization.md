# Divergence depth is polynomial degree — the characterization

> **Thesis.** A sequence has *finite faithful divergence depth* `d` if and only if it is a
> polynomial of degree `d`.  Both directions, and the exactness, are ∅-axiom over `ℤ`.

This chapter closes the divergence-depth arc.  `completeness_without_completeness.md` introduced
divergence depth as the count of finite-difference lifts a sequence needs before it stops moving
(`e` depth 3, `π` depth 6, an algebraic irrational depth 0/1, a Liouville number depth `∞`), and
`newton_gregory.md` supplied the forward-difference calculus over `ℤ` — the readout group in which
the difference operator `Δ` closes under iteration.  What remained was to identify the finite-depth
class outright.  It is exactly the polynomials, and the depth is exactly the degree.

## 1. The depth operator

For `s : ℕ → ℤ`, the forward difference is `diffZ s n = s (n+1) − s n`, iterated by `liftKZ`
(`liftKZ 0 = id`, `liftKZ (k+1) = diffZ ∘ liftKZ k`).  A sequence is `isConstZ` when it never moves,
and

   `polyDepthZ d s  :=  isConstZ (liftKZ d s)`

— the `d`-th difference is constant (`NewtonGregory.polyDepthZ`).  The `ℤ` setting is essential:
over `ℕ` the difference `s(n+1) − s n` truncates, so the converse direction below cannot even be
stated.  `Δ` is the difference-Lens; `ℤ` is the group its iterated readout lands in.

The finite-depth sequences form a **ring** (`FiniteDepthAlgebra`): closed under `+`
(`polyDepthZ_add`), scalar multiplication (`polyDepthZ_smul`), shift, and product with **additive
depths** — `polyDepthZ_mul : polyDepthZ d s → polyDepthZ e t → polyDepthZ (d+e) (s·t)`, the discrete
Leibniz rule turning the hand-counted depth arithmetic of `e = 3`, `π = 6` into a theorem.

## 2. The forward direction — reconstruction

`NewtonGregory.reconstruct` is the converse the `ℕ` truncation could not state:

   `polyDepthZ d s  ⟹  s n = Σ_{j≤d} C(n,j) · (Δʲ s)(0)`        (`= newtonZ (Δ·s 0) d n`).

A finite-depth sequence is recovered from its leading differences as a degree-`d` polynomial in the
binomial (Newton) basis `{C(·,j)}`.  So **finite depth ⟹ polynomial**.

## 3. The reverse direction — Newton columns carry their index as depth

The missing half is that every Newton-basis polynomial *has* finite depth.  It rests on a single
fact: the binomial column `C(·,k)` has divergence depth exactly `k`.  Pascal's rule, read as a `ℤ`
forward difference, lowers the column by one with no truncation,

   `diffZ_binomColZ` :  `Δ C(·,k+1) = C(·,k)`            (from `C(n+1,k+1) = C(n,k) + C(n,k+1)`),

so iterating `Δ` exactly `k` times reduces `C(·,k)` to the constant `C(·,0) = 1`:

   `polyDepthZ_binomColZ` :  `polyDepthZ k (fun n => (C(n,k) : ℤ))`.

A Newton-basis polynomial `Σ_{j≤d} C(·,j)·c_j` is then a sum of scaled columns of depth `j ≤ d`;
the ring structure (`polyDepthZ_add`, `polyDepthZ_smul`) and depth-monotonicity (`polyDepthZ_mono`)
give

   `polyDepthZ_newtonZ` :  `polyDepthZ d (fun n => newtonZ c d n)`     for every coefficient family `c`.

So **polynomial ⟹ finite depth**.

## 4. The characterization

Combining §2 and §3:

   **`finite_depthZ_iff`** :  `polyDepthZ d s  ↔  ∃ c, ∀ n, s n = newtonZ c d n`.

A `ℤ`-sequence has faithful finite divergence depth `d` *iff* it is a polynomial of degree at most
`d` (Newton basis).  The forward map sends `s` to its leading-difference coefficients `c_j = Δʲs 0`;
the reverse is the column-sum of §3.

## 5. Exactness — depth *is* the degree

The bound is tight.  The `d`-th difference of a degree-`d` Newton form returns its top coefficient,

   `liftKZ_newtonZ_const` :  `Δ^d (Σ_{j≤d} C(·,j)·c_j) = c_d`        (constant),

obtained by iterating the shift `diffZ_newtonZ : Δ(Σ_{j≤d+1} C(·,j)c_j) = Σ_{j≤d} C(·,j) c_{j+1}`.
Hence a degree-`(e+1)` Newton form collapses to depth `e` precisely when its leading coefficient
vanishes:

   **`newtonZ_depth_drop`** :  `polyDepthZ e (Σ_{j≤e+1} C(·,j)·c_j)  ↔  c_{e+1} = 0`.

With the characterization, divergence depth equals polynomial degree *exactly*: a genuine
degree-`(e+1)` polynomial (leading coefficient non-zero) has depth `e+1`, never `e`.

## 6. The monomial basis and the zeta rungs

The same degree-`d`-implies-depth-`d` holds verbatim in the monomial basis.  Building `n^k` as `k`
factors of the identity sequence — depth `1` each (`Δ idZ ≡ 1`), depths adding under
`polyDepthZ_mul` — gives `polyDepthZ k (n ↦ n^k)`, and summing yields

   `polyDepthZ_polySeq` :  `polyDepthZ d (fun n => Σ_{i≤d} a_i · n^i)`     for any `ℤ`-coefficients `a`.

No Stirling conversion is needed; the finite-depth ring does the bookkeeping.  Over `ℤ` the negative
coefficients cost nothing: the `ζ(3)` Apéry leading coefficient `34n³ − 51n² + 27n − 5` is a
degree-3 polynomial directly (`aperyLeadZ_depth`, value `117` at `n = 2`), where the `ℕ`-only
statement first had to reindex `n = m + 2` to keep every coefficient non-negative.

This pins the **coefficient-degree statistic** of the zeta convergent recurrences.  Apéry's
recurrences are P-recursive of order 2 with polynomial coefficients whose degree rises by one with
the zeta argument:

| constant | recurrence | coefficient degree | depth |
|---|---|---|---|
| `e` | `dₙ₊₁ = (n+1)·dₙ` (order 1) | 1 | the ratio `n+1`, depth 1 |
| `ζ(2)` | `(n+1)²uₙ₊₁ = (11n²+11n+3)uₙ + n²uₙ₋₁` | 2 | `polyDepth 2` (`zeta2_quadratic_rung`) |
| `ζ(3)` | `n³aₙ = (34n³−51n²+27n−5)aₙ₋₁ − (n−1)³aₙ₋₂` | 3 | `polyDepth 3` (`apery_cubic_rung`) |

The depths are pinned *exactly* (`aperyTop_depth_exact`, `zeta2Top_depth_exact`).  This is a
statistic of the recurrence, not a cause of irrationality — `ζ(4)` has an order-2 recurrence that
does not prove irrationality, Catalan's `β(2)` an order-2 one with irrationality open, `ζ(5)` an
order-3 one; the `e → ζ(2) → ζ(3)` degree run does not continue as a tower.  `ζ(3)`'s degree 3 is
the exception above the order-2, degree-2 Apéry-like (sporadic) family, itself capped by
`quadratic_polyDepth : ∀ A B C, polyDepth 2 (A·n²+B·n+C)`.

## 7. The cross-determinant and its native sign

The order-2 recurrences carry a discrete Wronskian (Casoratian) `Cₙ = aₙbₙ₋₁ − aₙ₋₁bₙ` of any two
solutions.  Its propagation law `c₂(n)·Cₙ = −c₀(n)·Cₙ₋₁` holds subtraction-free over `ℕ`
(`casoratian_step`: the middle coefficient `c₁` cancels, so only the outer coefficients propagate —
which is why the relevant degree is `deg c₂ = deg c₀`, the `n³`/`(n−1)³` of `ζ(3)`, the
`(n+1)²`/`n²` of `ζ(2)`).  Telescoping the outer-coefficient product (`telescope`) gives the `1/n³`
(resp. `1/n²`) shape.

The *sign* needs no exterior integers: an integer is a pair of naturals (`Lens.Number.Nat213.Tower.NatPairToInt`,
`(a,b) = a − b`, negation = the swap of the two axes), so the Casoratian is the pair
`(aₙbₙ₋₁, aₙ₋₁bₙ)` and the signed law `c₂Cₙ = −c₀Cₙ₋₁` is the `npairEquiv` of the scaled pair against
the swapped predecessor — which unfolds to `casoratian_step` verbatim (`casoratian_signed`).
Telescoped on the pair, the closed forms are `+6/n³` for `ζ(3)` (constant sign — the trailing
coefficient sits on the negative axis, swap-free) and `±5/n²` for `ζ(2)` (alternating, the sign being
`iterNeg n = (−1)ⁿ`, the axis swap accumulated).  The two readings of one Casoratian are the two
non-trivial outcomes of self-reference: its **magnitude** telescopes (the converging/escaping ladder)
and its **sign** toggles with period 2 (the oscillation), independent of each other.

The depth-0 instance is the residue's own algebraic floor.  The Fibonacci Cassini identity
`fib(n+2)·fib(n) − fib(n+1)² = (−1)ⁿ⁺¹` is the simplest signed Casoratian — magnitude `1` (the
`det P = 1` invariant of the `P = [[2,1],[1,1]]` / `φ` orbit, already at the floor) with sign the
period-2 axis toggle (`cassini_pair`).

### 7.1 The single-sequence determinantal ladder — all orders at once

A second, parallel determinant rides the depth ladder: for **one** sequence `s` obeying a
*constant-coefficient* order-`k` recurrence `s(m+k) = Σ_{l<k} a l · s(m+l)`, the `k×k` **Hankel
(Casoratian) determinant** `Hₖ(n) = det[s(n+i+j)]_{i,j<k}` multiplies by the **companion
determinant** at every step:

> `Hₖ(n+1) = altSign(k−1) · a 0 · Hₖ(n)`   (`CasoratianDeterminant.casoratian_det_step`).

This is the determinantal / arithmetic ascent of the depth ladder — order-`k` ↦ the `k×k`
determinant, multiplier `= det(shift)` — and it is closed at **every** order in one structural
theorem, not order by order.  The proof needs no expansion: the shifted Hankel matrix is the
companion matrix times the original, `H(n+1) = C·H(n)` (the recurrence read as a single linear
map, `hankel_shift_eq_matMul`), so `det H(n+1) = det C · det H(n)` (`DetMul.det_matMul`), and the
companion determinant is `det C = (−1)^{k−1}·a 0` (`det_companion`, cofactor expansion along the
single-entry first row, recursing on the `(0,1)`-minor).  The order-2 (`CassiniUnimodular.det_step`,
multiplier `q`) and order-3 (`SecondCasoratian.second_casoratian`, multiplier `c`) rungs — each
previously proved by a direct `ring_intZ` expansion — are the `k = 2, 3` instances; the order-4 rung
(`fourth_order_multiplier`, multiplier `−a 0`) is the first the direct expansion **could not reach**
(its `4×4` normal form overflows the kernel), now a one-line instance of the structural law.  The
conserved object is the companion-matrix determinant — a toric / genus-0 invariant whose *size*
grows with the order, the genus staying `0` at every rung (the precise replacement for the mistaken
"order-3 ↦ genus-1 curve").

## 8. The reading

Read in residue terms, `diff` is a pointing event — pointing again at how a sequence changes — and
depth counts the re-pointings until self-coincidence.  The floor is the self-same rule whose step
does not depend on `n`: the constant-coefficient `P`/`φ` orbit, depth 0, the residue's algebraic
image `P(φ) = φ`.  Each unit of depth is one degree of `n`-dependence away from that pure
self-reference; `e`, `ζ(2)`, `ζ(3)` sit at 1, 2, 3.  The dichotomy is sharp: a sequence either
*closes* (finite depth — it is a polynomial, by this chapter's characterization) or it *never
closes* (depth `∞`, the residue surplus that no finite reference catches — the geometric `2ⁿ` and
the Liouville numbers).  "Has finite depth" is not "an exterior reference catches it"; it is the
sequence's own structure folding onto itself in finitely many steps.

## Lean anchors

- `Cauchy/DepthCharacterization` — `finite_depthZ_iff`, `newtonZ_depth_drop`, `polyDepthZ_binomColZ`,
  `diffZ_binomColZ`, `polyDepthZ_newtonZ`, `liftKZ_newtonZ_const`, `diffZ_newtonZ`.
- `Cauchy/PolynomialDepth` — `polyDepthZ_polySeq` (monomial degree = depth), `aperyLeadZ_depth`.
- `Cauchy/NewtonGregory` — `reconstruct`, `newtonZ`, `bsum`, `bsum_pascal_aux`.
- `Cauchy/FiniteDepthAlgebra` — `polyDepthZ_{add,smul,mul}`, the finite-depth ring.
- `Cauchy/DepthAperyCubic` — `apery_cubic_rung`, `zeta2_quadratic_rung`, `*_depth_exact`.
- `Cauchy/DepthQuadraticGeneric` — `quadratic_polyDepth`.
- `Cauchy/{CasoratianStep, CasoratianSigned, CassiniSigned}` — the 2-solution Wronskian, its native
  sign, the depth-0 floor.
- `Cauchy/{SecondCasoratian, CasoratianDeterminant}` — the single-sequence determinantal ladder:
  `second_casoratian` (order 3), and ★ `casoratian_det_step` / `casoratian_det_closed` (the all-orders
  Hankel multiplier law `Hₖ(n+1) = altSign(k−1)·a₀·Hₖ(n)`, via `det_companion` + `DetMul.det_matMul`);
  `Linalg213/DetN.det_congr_lt` (det depends only on rows `< n`).
- Tooling: `Meta/Nat/PolyNatM` + `ring_nat`, `Meta/Int213/PolyIntM` + `ring_intZ` — the ∅-axiom
  multivariate polynomial-identity provers (the `ring` replacement, over `ℕ` and `ℤ`) that discharge
  the coefficient reorders throughout.
