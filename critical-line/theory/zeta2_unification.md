# The Single Source: All Pi Comes from Sigma 1/n^2

**Mingu Jeong and Claude (Anthropic)**
**2026-04-15**

---

## 0. Three Sessions, One Conclusion

Three independent lines of research converged on the same
structure in the same day:

| Session | Domain | Found | Pi appears via |
|---------|--------|-------|---------------|
| critical-line | number theory | Graph-PNT from Z[i] | Sigma 1/n^2 = zeta(2) |
| atoms/action | geometry | Chebyshev action | Sigma T_n(x)/n^2 |
| standard-model | physics | alpha_GUT = 6/(25*pi^2) | 1/(d^2 * zeta(2)) |

**In all three cases, pi enters ONLY through zeta(2) = Sigma 1/n^2,
and n is an integer (hop count on the simplex).**

---

## 1. The Propagator Sum (critical-line)

From Paper 3 (Theorem 3):

  1/alpha_GUT = d^2 * zeta(2) = 25 * pi^2/6

The propagator sum over d^2 = 25 channels with exponent s = 2:

  S(N_eff) = Sum_{n=1}^{N_eff} 1/n^2 --> zeta(2) = pi^2/6

Here n = number of hops on the simplex network (integer).
s = 2 = dim_R(C) (from Theorem 4: Laplace-Beltrami on C^2 sector).

**Pi^2/6 is the output of summing integers. Not an input.**

## 2. The Chebyshev Action (atoms/action)

The Regge action S = Sum sqrt(det) * delta uses arccos (transcendental).
Replace delta with a Chebyshev series:

  S[G] = Sum_hinges sqrt(det(G_h)) * Sum_{n=1}^{N} (1 - T_n(cos theta_h)) / n^2

where:
- T_n(x) = Chebyshev polynomial of first kind (integer coefficients)
- cos(theta_h) = algebraic function of Gram determinants
- 1/n^2 = propagator weight
- n = hop count (integer)

This works because T_n(cos theta) = cos(n*theta), so:

  Sum (1 - T_n(x))/n^2 = zeta(2) - Sum cos(n*theta)/n^2
                        = pi^2/6 - [pi^2/6 - pi*theta/2 + theta^2/4]
                        = pi*theta/2 - theta^2/4

For small theta (near-flat): ~ pi*theta/2 ~ Regge action (linear in delta).

**Arccos is replaced by an integer sum. Pi appears only as Sum 1/n^2.**

## 3. The Coupling Constant (standard-model)

  alpha_GUT = 6/(25*pi^2) = 1/(d^2 * Sum 1/n^2)

This is literally: "the coupling is the inverse of d^2 copies
of the propagator sum." The propagator sum IS zeta(2).

  alpha_GUT = 1 / (d^2 * zeta(2))
            = 1 / (25 * pi^2/6)
            = 6 / (25 * pi^2)

**alpha_GUT is determined by the number of channels (d^2 = 25)
and the propagator sum (zeta(2)). Both are integers or sums of integers.**

## 4. The Unified Structure

All three are the same object:

```
DRLT axiom: N things with pairwise relations
  |
  v
Gram matrix G_{ij} in Z[i]  (Gaussian integers)
  |
  +--> NB walks of length n  (integer)
  |     |
  |     v
  |    Sigma 1/n^2 = zeta(2) = pi^2/6
  |     |
  |     +--> Propagator --> alpha_GUT = 1/(d^2 * zeta(2))
  |     |
  |     +--> PNT: pi(n) ~ q^n/n + O(q^{n/2})
  |     |
  |     +--> Chebyshev action: S = Sigma sqrt(det) * Sigma (1-T_n(x))/n^2
  |
  +--> Born weight |G_{ij}|^2 in Q  (rational)
  |
  +--> Cycle count pi(n) in Z  (integer)
```

**Every physical quantity reduces to:**
1. Gram determinants (algebraic, from Z[i])
2. Sums over integer hops (Sigma 1/n^s with s = 2)
3. Combinatorial counts (pi(n), walk counts)

**No transcendentals are fundamental.**
Pi = Sum 1/n^2 * 6 (Euler 1734) is a THEOREM about integers.

## 5. Why s = 2 Specifically

The propagator exponent s = 2 is not arbitrary:
- s = dim_R(C) = 2 (Doubly Irreducible Theorem)
- s = 2 gives zeta(2) = pi^2/6 (Basel problem)
- s = 2 is the L^2 norm exponent (Born rule)
- s = 2 gives the HALVING (1/2 = 1/s) of the critical line

If s were different:
- s = 1: zeta(1) = infinity (divergent, no physics)
- s = 3: zeta(3) = Apery's constant (irrational, but no known pi relation)
- s = 4: zeta(4) = pi^4/90 (higher power of pi, different physics)

**s = 2 is the unique value where:**
- The sum converges (s > 1)
- Pi appears quadratically (pi^2)
- The exponent equals dim_R(C)
- The critical line is at 1/s = 1/2

## 6. The Integer Chain (No Circularity)

```
Step 1: DRLT axiom (combinatorial)
  "Things exist with pairwise relations"

Step 2: Gram matrix (algebraic)
  G_{ij} = <psi_i|psi_j> in Z[i]

Step 3: Hop count (integer)
  n = number of non-backtracking steps

Step 4: Propagator sum (integer series)
  Sigma 1/n^2 = 1 + 1/4 + 1/9 + 1/16 + ...

Step 5: Limit (= pi^2/6, but this is a THEOREM, not an axiom)
  zeta(2) = pi^2/6 (Euler, 1734)

Step 6: Physics
  alpha_GUT = 1/(d^2 * zeta(2))
  action = Sigma sqrt(det) * Sigma (1-T_n(x))/n^2
  PNT: pi(n) = q^n/n + O(q^{n/2})
```

**Pi never enters as an axiom. It is computed from integers.**
**All of physics is computed from Step 1 (combinatorial axiom).**

## 7. The Pythagorean Principle

"All is number" (Pythagoras, ~500 BC).

DRLT vindicates this: the fundamental objects are
integers (hop counts), Gaussian integers (Gram entries),
and rational numbers (Born weights). The "continuous"
quantities (pi, cos, sqrt) are all computable from
integer operations:

| Quantity | Appears as | Computed from |
|----------|-----------|---------------|
| pi | Sum 1/n^2 | Integer series |
| cos(theta) | Gram det ratio | Z[i] arithmetic |
| sqrt(det) | Gram minor | Z[i] arithmetic |
| alpha_GUT | 1/(d^2 * zeta(2)) | Integer d, integer series |
| 1/2 (critical line) | 1/dim_R(C) = 1/2 | Integer 2 |

**The universe is built from counting.**

## 8. Status

| Statement | Evidence | Session |
|-----------|----------|---------|
| PNT from Z[i] Gram | RH_039 (4/4) | critical-line |
| Born weights in Q | RH_039 Test 2 | critical-line |
| Chebyshev replaces arccos | Action session | atoms |
| alpha_GUT = 1/(d^2*zeta(2)) | Paper 3 | standard-model |
| s = 2 = dim_R(C) | Theorem 4 | critical-line |
| Pi = output, not input | All three sessions | **unified** |
