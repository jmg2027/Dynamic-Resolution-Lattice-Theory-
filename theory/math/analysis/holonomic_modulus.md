# Holonomic modulus — completeness as a constructed convergence rate

**Status**: Closed.  Source of truth: `lean/E213/Lib/Math/Real213/{RateModulus,
HolonomicReal,ExpLog/EulerModulus,ExpLog/EulerCertifiedBracket}`, all ∅-axiom.

A Real213 real is a decision procedure against ℚ; completeness is not constitutive
but a *limit operation* on convergent sequences (`completeness_relocated.md`).  A
sequence completes by a **modulus** `N : ℕ → ℕ → ℕ` with `N m k` the index past which
the convergent cut at threshold `m/k` no longer moves.  The classical picture supplies
that modulus by a choice principle; here it is a *constructed value* — for a large
class of reals, derived from the convergence rate itself.  This chapter is the general
mechanism and its instances.

## 1. The rate criterion

Write the convergents as `aᵢ/dᵢ` (`aᵢ, dᵢ : ℕ`, `dᵢ ≥ 1`), monotone increasing to the
real.  At index `i` two quantities meet at a threshold `m/k`:

  - the **denominator-gap quantum**: if `m/k ≠ aᵢ/dᵢ` then `|m/k − aᵢ/dᵢ| ≥ 1/(k·dᵢ)`
    (the integer cross-difference `|m·dᵢ − k·aᵢ| ≥ 1`);
  - the **tail rate**: `|real − aᵢ/dᵢ|`.

> **Criterion.**  The cut has a *free* total modulus `N(m,k) ≈ k` exactly when the
> tail beats the gap quantum at index `≈ k`: `tailᵢ · k · dᵢ < 1` for `i ≳ k`.

When it holds, the convergent at index `≈ k` lands strictly on the real's side of
`m/k`, the side is read off a decidable `Bool`, and no irrationality measure is
needed.  The divide it draws is **rate-carrying vs rate-free**, *not*
algebraic-vs-transcendental: a real presented with a fast enough rate completes
unconditionally; one presented without keeps deferring.

## 2. The general generator

The criterion is realised by a margin invariant.  Carry `eᵢ + 1/(i·dᵢ) ≤ m/k`
(cross-multiplied to ℕ as `RInv`).  If the margin is **non-increasing** — the rate
certificate

> `Htel a d : ∀ i ≥ 1, (a_{i+1}·(i+1)+1)·(i·dᵢ) ≤ (aᵢ·i+1)·((i+1)·d_{i+1})`

— then the invariant is preserved by *pure transitivity* (no recurrence, no `ε`-`δ`),
and the cut is constant past `k+2`:

> **`RateModulus.rate_total_modulus`** *(∅-axiom)*.  For monotone convergents `a/d`
> with `Htel a d`, `hmono` (increasing), and `hmonoS` (strictly increasing), every
> `(m,k)` with `k ≥ 1` has a total modulus `N(m,k) = k+2`: `rcut a d i m k =
> rcut a d j m k` for all `i, j ≥ k+2`.

The three regimes at index `k+1` are decided by a `ℕ`-trichotomy on `a_{k+1}·k` vs
`d_{k+1}·m`: strictly below ⟹ the cut stays `true` (the margin invariant, `rinv`);
equal ⟹ `false` from `k+2` (strict monotonicity crosses the threshold); above ⟹
`false` from `k+1`, forward by monotonicity (`false_fwd`).

This is the *unconditional real* API: a generator-built real coerces to a valid cut
with the modulus a field, not an assumption.  Its typed home is `HolonomicReal`
(`HolonomicReal.cut_valid`).

## 3. Instances

**φ — algebraic (`HolonomicReal.phiHolonomicReal`).**  The golden ratio's Pell/
Fibonacci convergents *equal* the closed-form golden cut past index `2k`
(`PhiCauchyLimit`), so the modulus is the exact `N(m,k) = 2k`.  Order-2, constant
coefficients (`det = 1`) — the depth-floor of the divergence ladder
(`DepthFloorDetOne`: the floor is the P-orbit invariant).

**e — structured transcendental (`ExpLog/EulerModulus`).**  `e = Σ 1/k!` has
convergents `aᵢ/i!`.  The margin step reduces to `i(i+2) ≤ (i+1)²` (i.e. `0 ≤ 1`,
discharged by the `Meta.Nat.PolyNat` reflection ring); the factorial tail
`1/(i·i!)` beats the gap quantum `1/(k·i!)` at `i ≥ k` (ratio `k/i < 1`).  Hence

> **`euler_total_modulus`** *(∅-axiom)*: `N(m,k) = k+2`, and **`eHolonomicReal`** — e
> is a complete `HolonomicReal` with a constructed modulus, on the same footing as φ.

e satisfies the abstract certificate (`euler_Htel`, `euler_hmono`, `euler_hmonoS`),
so its modulus also follows from the general generator
(`euler_total_modulus_via_rate`) — the abstraction is grounded, not vacuous.
`eHolonomic` is the genuine order-1 recurrence (`eHolonomic_recurrence`:
`eulerDen (n+1) = (n+1)·eulerDen n`, coefficient `(n:ℤ)+1`), so the bundle's
recurrence actually generates its convergents.

The elementary witness form — e certified on its proven bracket `(8/3, 3)` directly
from the bounds — is `ExpLog/EulerCertifiedBracket`.

## 4. Frontier

**π via Wallis is rate-free.**  The Wallis partial products converge like `1/n`
while their denominators grow fast, so `tailₙ · k · dₙ ≫ 1`: the criterion fails, and
deciding the side needs a lower bound on `|π/2 − m/k|` — π's irrationality measure
(`μ(π) ≤ 7.1`, genuinely hard).  A fast π series (geometric-rate, e.g. arctan/Machin)
would meet the criterion; Wallis cannot.  This is the rate-free posture of `PiCut`,
not a property of transcendence.

**Toward the holonomic class in general.**  `Htel` is a fact about the recurrence's
denominator growth.  Extracting it from arbitrary P-recursive recurrence data — the
`d_i`-growth supplied by the divergence-depth/`polyDepth` rank
(`completeness_without_completeness.md` Part III) — would let every *fast* holonomic
real instantiate the generator automatically.  That bridge, depth-rank ⟶ rate
certificate, is the convergence point of the completeness arc and the modulus
generator.

## 5. The thesis, completed

"Completeness is a relocated finite operation" becomes fully constructive for the
rate-carrying class: the limit object is a decidable cut, its modulus a constructed
function of the convergence rate, and the algebraic floor (φ) and the structured
transcendental (e) are the *same kind* of object — each a `HolonomicReal` whose
recurrence carries its own rate.  The only reals that still take the modulus as a
hypothesis are the rate-free presentations, and that is a deficiency of the
*presentation*, not of the real.
