# The degree calculus — the field operations' action on modulus degree

**Status: the first-order calculus is closed ∅-axiom.**  "Modulus degree" is the
growth-class invariant of a *pointing* (a monotone convergent presentation `a/d` of a
real), graded by the **non-unimodular adjacent cross-determinant**
`W_i = a_{i+1}d_i − a_i d_{i+1}` raced against the denominator increment `d_{i+1}−d_i`
(`DegreeCriterion`).  It is **presentation-relative**: a property of the pointing, not the
real (`e+e` via `(i!)²` is rate-free though `2e` is degree 1).

This note records how the four field operations act on the degree — the calculus assembled
from `RateArithmetic` (sum), `RateProduct` (product), `RateAffine` (affine + reciprocal).

| operation | cross-determinant action | racing increment | degree law | Lean |
|---|---|---|---|---|
| matched sum `x+y` | `W^x + W^y` | same `Δd` | **additive** (joint budget) | `RateArithmetic.matched_sum_*` |
| matched product `xy` | `≤ d_i d_{i+1}(W^x+W^y) + W^x W^y` | **squared** `Δ(d²)` | **−1 degree** (loses one) | `RateProduct.prod_*` |
| reciprocal `1/x` | `−W^x` (magnitude `W^x`) | numerator `Δa` | **preserved** (if `a ≍ d`) | `RateAffine.recip_*` |
| translate `x+m` | **invariant** `W^x` | same `Δd` | **preserved** (no cost) | `RateAffine.trans_*` |
| scale `q·x` | `q·W^x` (constant `q`) | same `Δd` | **preserved** (class) | `RateAffine.scale_*` |

**The structural reading.**  Reciprocal (`J = [[0,1],[1,0]]`, `det −1`) and integer
translation (`T = [[1,m],[0,1]]`, `det +1`) are the two `GL₂(ℤ)` generators; the degree is
**invariant under both** ⟹ degree is a `GL₂(ℤ)/Möbius` invariant of the pointing.  Scaling
(diagonal) absorbs a constant.  Sum and product are the *non-Möbius* (genuinely arithmetic)
directions, where the calculus has content: **additive** on `+`, **loses a degree** on `·`.

## Honest novelty split (adversarial web check — `research-notes/drafts/publishability_audit.md`)

- **Conceded re-skins.**  μ(x), the irrationality exponent, is a textbook
  `GL₂(ℤ)/Möbius`-invariant of the *number* (Diophantine approximation); the `GL₂(ℤ)` action
  on continued fractions and the unimodular `±1` simple-CF determinant are classical;
  computable-analysis divergence-bounded classes are field-closed.  So *each Möbius row,
  taken at the number level, is a re-skin* of μ's Möbius-invariance.
- **Genuinely unwritten.**  μ is **presentation-blind** (it sees only the number) and has
  **no calculus** — there is famously no formula for μ(x+y) or μ(xy).  The object here is a
  **per-pointing** degree graded by the *non-unimodular* cross-determinant `W` (general-CF,
  `W ≠ ±1`), with an **explicit action of all field operations**: additive (sum) / −1
  (product) / Möbius-invariant (reciprocal, translation, scaling).  The Möbius rows are the
  *check* that the per-pointing degree restricts to the classical invariant on the Möbius
  directions; the sum/product rows are where it carries content μ cannot see.  That
  juxtaposition — a presentation-relative degree calculus of the cross-determinant — is the
  unwritten object.  Modest, defensible; the individual Möbius row is not.

## Open frontier (next starting points)

- **Product tightness**: a concrete witness where `xy` sits exactly one degree below each
  factor (the product analogue of `RateHierarchy.sepDenS`), upgrading "loses ≤ 1" to "loses
  exactly 1".
- **Reciprocal total modulus**: weld the *decreasing* reciprocal pointing to the two-sided
  `BracketModulus` upper companion (route R1), giving `1/x` a total `rcut`-style modulus, not
  just the per-layer `DominatesS`.
- **Composition / `xⁿ`**: iterate the product law — does `xⁿ` lose `n−1` degrees, or is there
  a sharper power law on a single shared denominator?
