# E4 — Deep tension between orderProj-Cauchy and ε-N Cauchy

## Discovery (2026-04-26)

Found a *fundamental* limitation of resolution direction (B) from E3
— StrongModulus typeclass.

## Two Cauchy forms

### orderProj-Cauchy (existing HasModulus)

```
∀ m k, k ≥ 1, ∃ N, ∀ i, j ≥ N,
  orderProj m k (view xs i) = orderProj m k (view xs j)
```

= "view eventually ends up on the same side at every rational m/k cut".

### ε-N Cauchy (StrongModulus)

```
∀ k ≥ 1, ∃ N, ∀ i, j ≥ N, |view i / view j ratio difference| ≤ 1/k
```

= "ratio is eventually within 1/k distance".

## *Non-equivalence* of the two forms

**orderProj-Cauchy ⇎ ε-N Cauchy**.

Counterexample: ratio converges oscillating around p/q on both sides.
Even n: ratio = p/q - 1/n.  Odd n: ratio = p/q + 1/n.
- ε-N Cauchy: |ratio_i - ratio_j| → 0.  ✓
- orderProj at (p, q): even true, odd false.  Never stable.  ✗

ε-N Cauchy but NOT orderProj-Cauchy.

## Significance

The two Cauchy forms define *different mathematical objects*:

- orderProj-Cauchy: native to 213 — Dedekind cut-type limit.
- ε-N Cauchy: Bishop standard — value-convergence-type limit.

The two fundamentally differ on **rational limit points**.

Within ZFC ℝ they are equivalent (both define the same element of
ℝ) because rationals are measure-zero "irrelevant" — set-theoretic
flattening.  Within 213 the two forms define *different objects*.

## Implications for Phase B (arithmetic)

- Addition on orderProj-Cauchy: ill-defined at rational points (above
  counterexample).  → a true obstruction.
- Addition on ε-N Cauchy: standard Bishop, working.  But not the
  *native* form of 213.

## Possible resolutions

### (i) Avoid rational points

Exclude rational limit points from the definition of Real213 itself.
e.g., "sequence converges *strictly* at (m, k) — eventually ratio
< m/k, or eventually ratio > m/k, or *trichotomy* with eventually
ratio = m/k".

### (ii) Union of the two forms

Real213 = (xs, hasModulus, strongModulus).  Both required.
Eliminates the ambiguity at rational points.

### (iii) Different cut form

Split orderProj into a *strict* form ("< m/k" or "> m/k").  Both
sides Cauchy separately.  Complex but more refined.

## Decision

Is this obstruction a signal of a *framework boundary* or an
*engineering challenge*?

Looks like an **engineering challenge**, but *deep* engineering —
requires a design decision on the tension between the two Cauchy forms.
Bishop's program itself proceeds with ε-N — standard flow if ε-N is
adopted within 213 too.

But the fact that 213's *native* preference, orderProj-Cauchy, breaks
at rational points is itself a question about what the *primitive* of
the framework is.

## Tentative conclusion

*True* progress on Phase B (arithmetic) is possible only after this
design decision.  Progress to this point: kernel organized, deep
obstruction diagnosed.

Next session: design decision — orderProj vs ε-N vs union vs strict.

## Cross-references

- `notes/E2_phase_b_obstruction.md` (Raw realization).
- `notes/E3_modulus_kernel_deep_obstruction.md` (insufficient
  single-precision query).
- `framework/E213/Research/Real213ModulusCombiner.lean` (kernel).
- `framework/E213/Research/StrongModulus.lean` (ε-N form attempt).
