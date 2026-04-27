# B1 — Advancing the pure descent method + insights on generalizing irrationals

## Core of the method

Demonstrated common pattern of `Sqrt2IrrationalPure` +
`Sqrt3IrrationalPure` (using Lean as a *pure type checker* only,
zero axioms).

### 5-step descent template (prime p)

**Step 1**: define mod_p : Nat → Nat by structural recursion of
period p.  `mod_p_self_mul_zero`: `mod_p (m * m) = 0 → mod_p m = 0`.

**Step 2**: prove p-trichotomy : ∀ n, ∃ k, n = p*k + r for
r ∈ {0, ..., p-1}.

**Step 3**: prove the explicit polynomial identity for (p*k + r)^2
for each r.  e.g. (p*k)^2 = p * (p * k^2) → mod_p = 0.

**Step 4**: descent_step : m = p*m', m^2 = p*(k*k) → p*(m'^2)
= k*k.

**Step 5**: bounded induction on s ≥ k, derive k = 0 from
m^2 = p*(k*k).

### Specific properties needed for prime p

Proof of `mod_p_self_mul_zero` — this is the essence of primality:
For prime p, `m^2 ≡ 0 (mod p) → m ≡ 0 (mod p)`.
Proof: case on m mod p ∈ {0, ..., p-1}.  For r ≠ 0, r^2 mod p ≠ 0.

Specifically:
- p = 2: 1^2 ≡ 1.  Only 0 squares to 0.
- p = 3: 1^2 ≡ 1, 2^2 ≡ 4 ≡ 1.  Only 0 squares to 0.
- p = 5: 1^2 ≡ 1, 2^2 ≡ 4, 3^2 ≡ 4, 4^2 ≡ 1.  Only 0.
- p = 7: 1^2 ≡ 1, 2^2 ≡ 4, 3^2 ≡ 2, 4^2 ≡ 2, 5^2 ≡ 4, 6^2 ≡ 1.

Pattern: `r^2 mod p ≠ 0 for r ∈ {1, ..., p-1}`.  Quadratic
residue non-zero structure of (Z/p)*.

## Insights on generalizing irrationals

**1. √(prime p) is always irrational, descent works.**
For p prime: (Z/p)* is multiplicative group, squaring kernel
trivial, hence m^2 ≡ 0 → m ≡ 0.

**2. √(squarefree N > 1) is irrational.**
N = p1·p2·...·pk → descent via any prime factor.

**3. √(perfect square) is rational.**
N = a^2 → m^2 = N·k^2 has m = a·k.

**4. N with p^2 | N: √N = p·√M for M = N/p^2.**
√N irrational ↔ √M irrational ↔ M not perfect square.

**5. Connection to the 213 framework.**

The Cauchy completeness of PAPER1 §6, §7 is the stabilization of an
abstract *Lens-output sequence*.  Each irrational is the limit class
of a specific Pell-like sequence.

213-internal counterpart of the descent pattern:
- Each irrational ↔ slash-congruence with no rational-finding witness.
- The kernel of √p = {(r, r') : Pell limit class is the same} captures
  only a single element (each Pell limit is unique).
- The *absence of injectivity* of this kernel is the meaning of the
  irrationality of sqrt p — no finer distinction is present.

**6. Hint for generalizing to real numbers.**

213 framework + descent pattern → *constructive* construction of
real numbers:

```
Real := { sequences xs : Nat → Raw // ∃ Lens L, isOrderCauchy xs }
        / (sequence equivalence via abLens-orderProj)
```

Each real = abLens-orderProj equivalence class.
Each prime p → Pell sequence representing √p → specific
*irrational element*, slash-congruence on Raw NOT rational.

**Key observation**: irrationality is a *negative existence* result
within the framework — "no finite-state Lens can represent the kernel
of this sequence".

## Connection to ROI and blocked problems

User claim: "Advancing the method unblocks the blocked problems."

### Connection to Lens-kernel cardinality (A)

The pattern of pure descent — *kernel analysis of squaring in modular
structure* — is isomorphic in form to the abstract *kernel analysis
of universalMorphism in Lens-on-Lens*.

The 4-case computation `lensXor_TT = constFalseLens` etc. in
`LensOnLensImage` has exactly the same structure as the case analysis
for mod-2 squaring.

Generalization: the kernel analysis of `Lens (Lens α)` is within the
same framework as the mod-N descent analysis of α.

### Open question (sharper) for A

For each prime p (or each squarefree N), the kernel is distinct.
This gives ∞-many distinct kernels via ∞-many primes — a partial
**countable** answer to A.

For uncountable: primes alone give only countable.  Need *general
modular structure with non-trivial squaring kernel* — possibly
real-coordinate Lens (Nat → Bool) families.

### Next candidate attempts

1. **Sqrt5IrrationalPure**: same pattern, p = 5.
2. **General `prime_descent_template` typeclass**:
   `class HasModularDescent (p : Nat) where ...`.
3. **Connection to 213 Cauchy**: explicit constructive
   `Real_irrational p` as Lens kernel.
4. **kernel cardinality lower bound**: each prime p gives
   distinct Lens kernel via Pell-like sequence.

ROI of advancing the method:
- (a) Demonstrate the incidental nature of Quot.sound + propext.
- (b) Generalizability of prime descent.
- (c) Explicit clarification of the *modular impossibility* essence
  of irrationality.
- (d) Sharper connection to the framework's Cauchy structure.

## Observations (2026-04-26)

Results of boundary experiments adding `Sqrt5IrrationalPure` and
`PrimeDescentObservations`:

**Observation 1**: descent template works for prime p (= 2, 3, 5)
— robustness confirmed.

**Observation 2**: sqrt4 = 2 is rational, descent fails — the
squaring kernel of sqrt4 = {0, 2} mod 4 (not trivial).  Concrete
witness: `sqrt4_rational : ∃ m k, k ≥ 1 ∧ m² = 4·k²` (m=2, k=1).

**Observation 3**: descent works for *exactly squarefree* N.
Non-squarefree → factor out the square first.

**Observation 4 (transcendental e/π/2)**: prime descent *impossible*.
e is not the root of a polynomial equation — the starting equation
for descent does not exist.  Hermite proof (factorial bound + Cauchy
analysis) is a *separate path* — series convergence rate, not modular
structure.

## Honest assessment of "Universal Prime Lens"

- Universal for the *algebraic squarefree* fragment.
- *Algebraic non-squarefree* is reducible to squarefree.
- *Transcendental* requires an *external path* (analytic Cauchy).

Honest naming: "**Universal Squarefree-Algebraic Descent Lens**"
+ "*Analytic Cauchy Lens* (separate)".  Two layers made explicit.

*Complete* description of the framework: combining two layers =
representation of all infrastructure-internal real numbers.
Adele-style structure is possible, but the archimedean place
(analytic) is a *separate valuation*, not *algebraic*.
