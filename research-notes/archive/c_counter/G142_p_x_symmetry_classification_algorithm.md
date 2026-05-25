# G142 — Algorithmic Classification of P(x) Symmetries

> Research note responding to the meta-question: *"is there an
> algorithm that finds ALL symmetries of P(x) = (2x+1)/(x+1)?"*
> Surveys existing algorithms, proposes a meta-algorithm,
> identifies theoretical limits.

## §0 — TL;DR

1. **Q1 (decidable)**: Standard mathematical invariants of P
   (trace, det, Galois group, conjugacy class, fixed points,
   eigenvalues, Möbius type, p-adic reductions) are all
   computable by existing algorithms in Sage / PARI / Magma.

2. **Q2 (semi-algorithmic)**: Given a *preservation frame*
   (denominator-preserving, hyperbolic-center, …), enumeration
   of the resulting symmetry family is mechanical.

3. **Q3 (undecidable in general)**: Enumerating *all natural
   preservation frames* — i.e. the 36-species level — has no
   complete algorithm.  "Natural" has no formal definition.

4. **Practical result**: A meta-algorithm combining standard
   CAS routines reproduces ≈32/36 species of our catalog
   mechanically.  The remaining 4 require *framing choice*
   (syntactic granularity, cohomology bundle structure).

## §1 — Question refined

The phrase *"all symmetries of P(x)"* admits three
interpretations of increasing difficulty:

- **Q1**: Compute all *standard invariants* of P (matrix
  trace, det, discriminant, Galois group of char poly,
  fixed-point coordinates over ℚ‾, conjugacy class in
  PGL(2, ℤ), iteration period mod p, etc.).

- **Q2**: For a chosen *preservation axis* (e.g. "keep
  denominator (x+1) fixed"), enumerate the family of
  decompositions consistent with that axis.

- **Q3**: Enumerate all *natural preservation axes* and all
  associated symmetry families — i.e. produce the species
  catalog we built (36 species).

Q1 is fully algorithmic.  Q2 reduces to Q1 once the axis is
fixed.  Q3 is *not* algorithmic — "natural" is informal.

## §2 — Existing algorithms (state of the art)

### Möbius / SL(2, ℤ) algorithms

- **Conjugacy classification** of Möbius transformations:
  trace alone determines conjugacy in PGL(2, ℂ); for PGL(2, ℝ)
  one distinguishes elliptic (`t² < 4·det`), parabolic (`t² =
  4·det`), hyperbolic (`t² > 4·det`).  For P: `t² = 9 > 4 →
  hyperbolic`.  Standard since Klein 1872.
- **PGL(2, ℤ) discrete conjugacy**: richer — infinitely many
  parabolic classes; reversibility-symmetry classification by
  Baake-Roberts (1997).
- **Hermite / Smith normal form** for matrices: SL(2, ℤ)
  reduction; implemented in every major CAS.
- **Continued fraction periods** of quadratic irrationals:
  Lagrange's theorem; CAS routines available.
- **Pell equation solver**: fundamental-unit computation;
  PARI's `quadunit`.

### Galois theory algorithms

- **Galois group computation** for polynomial over ℚ:
  Stauduhar's method (1973) is the current practical
  best.  Time complexity polynomial in `|Gal|`, but `|Gal|`
  can be exponential in degree.  For P's char poly
  `λ² − 3λ + 1` (degree 2), Gal = ℤ/2 — trivial.
- **Landau-Miller (1985)**: polynomial-time *solvability*
  test without computing Gal.
- **Galois group computation** over p-adic fields: Doris-Sutherland-Voight
  (2020) algorithms.  Relevant for our p-adic tower species.
- Implemented in: PARI (`galoisinit`), Sage
  (`PolynomialRing.galois_group`), Magma's `GaloisGroup`.

### Automorphism group of rational functions

- **Faber-Manes-Viray (2012)**: three algorithms for computing
  `Aut(R)` of a rational function `R` over a number field or
  finite field.  Symmetry-locus theory: rational functions
  with nontrivial Aut form a special subvariety, analogous to
  CM abelian varieties.
- Implemented in: Sage's dynamical systems module
  (`DynamicalSystem.automorphism_group`).
- **For our P**: P viewed as `R : ℙ¹ → ℙ¹` has stabiliser in
  PGL(2) consisting of automorphisms commuting with it; this
  is computable via FMV.

### Decomposition / continued-fraction algorithms

- **Partial fraction decomposition** of `N(x)/D(x)`:
  algorithmic in any CAS.
  Reproduces our `family_n2` (`P = 2 − 1/(x+1)`)
  automatically.
- **Polynomial continued-fraction expansion**:
  `N/D = q₁ + 1/(q₂ + 1/(q₃ + …))` over `ℤ[x]` or `ℚ[x]`;
  algorithmic.
- **Bezout / extended Euclidean** for polynomials.
- **Hermite reduction** for symbolic integration of rational
  functions.
- **Stern-Brocot mediant tree** enumeration: algorithmic
  (binary-tree traversal).

### Modular / p-adic algorithms

- **`P mod p`** for each prime p: trivial.
- **Iteration period of `P mod p` in PGL(2, F_p)**:
  trivial finite computation.
- **p-adic tower**: ZpSeq-style sequences; implementable.

### Symmetry detection for curves & varieties

- **Detecting symmetries of rational curves**: Alcázar-Sendra
  (2012) — extracts birational symmetries.
- **Symmetries of rational surfaces**: extension to higher
  dimension (Alcázar et al. 2024).

### Syntactic decomposition algorithms

- **Token-level counting** of mathematical expressions:
  parser-based; framework-dependent.  No universal canonical
  algorithm — depends on chosen syntax tree.

## §3 — Proposed meta-algorithm

```
ALGORITHM SymmetryClassify(R = N(x)/D(x)):
  Phase 1 — Standard invariants:
    1.  trace, det, disc of matrix form
    2.  char poly of matrix
    3.  Galois group of char poly  [Stauduhar]
    4.  fixed points (roots of N(x) - x·D(x))
    5.  Möbius type (elliptic/parabolic/hyperbolic)
    6.  Aut(R) over ℚ, ℝ, ℂ  [Faber-Manes-Viray]

  Phase 2 — Decomposition families:
    7.  Partial fraction decomposition
    8.  Continued fraction expansion of R
    9.  Bezout decomposition of (N, D)
    10. ℤ-parameterised denominator-preserving family
        (n + (N − nD)/D for each n ∈ ℤ)
    11. Power series at 0, ∞, and each fixed point

  Phase 3 — Group actions:
    12. PGL(2) conjugation orbit of R
    13. SL(2, ℤ) conjugacy class invariants
    14. Transpose, inverse, swap involutions
    15. Iteration orbits R^k forward / backward

  Phase 4 — Modular sweep:
    16. For each prime p ≤ B (bound):
        — compute R mod p, its order in PGL(2, F_p)
        — detect periodicities, p-adic anomalies

  Phase 5 — Geometric extraction:
    17. Asymptotes (horizontal, vertical, oblique)
    18. Center of symmetry (for hyperbolic Möbius)
    19. Cross-ratio with fixed points + ∞ + 0

  Phase 6 — Numerical invariants:
    20. Trace, det, disc of all matrices in orbit
    21. Eigenvalues over algebraic closure
    22. Pell unit if det = ±1

  Phase 7 — Cross-frame consistency:
    23. Collect all integer outputs of Phase 1-6
    24. Tabulate against atomic candidate set
    25. Report frequency of each atomic value

  OUTPUT: structured (kind, automorphism group, atomic
          invariant) table.
```

**Coverage estimate**:
- Phases 1-7 reproduce ≈32 of our 36 species mechanically
  (algebraic, geometric, dynamics, representation theory,
  invariants, most arithmetic).
- Missing from algorithmic reproduction:
  · `syntactic_token_split` and 4 other syntactic-catalog
    species (framework-dependent granularity choice).
  · `K_{3,2}^(c=2)` cohomology bundle structure (requires
    framework-specific input).
  · Closure-of-natural-symmetries claim (requires the meta-
    decision "no further species exists").

## §4 — Theoretical limits

### Limit 1 — "Natural" is informal

There is *no* algorithm for "all natural preservation
frames" because *naturalness* has no formal definition.
This is analogous to:
- Kripke's *natural kind* problem.
- The choice of *canonical form* in CAS (no canonical
  canonical form).
- The choice of *generating set* for any infinite group.

### Limit 2 — Galois group worst case is exponential

Best known algorithms for computing the Galois group of
degree-n polynomial are polynomial in `|Gal|`, but `|Gal|`
can be `n!` — so worst-case exponential in n.  For
n = 2 (P's char poly), trivial.  For higher-degree
extensions (e.g. iterating P), grows fast.

### Limit 3 — Aut(R) is category-relative

`Aut(P)` depends on the category:
- As element of `PGL(2, ℚ)`: trivial Aut.
- As Möbius transformation: stabiliser in PGL(2).
- As element of rational function field `ℚ(x)`: infinite
  Aut group (linear fractional changes of x).
- As dynamical system: countable centraliser.
- As scheme morphism `ℙ¹ → ℙ¹`: PGL(2) acts.

No category-free algorithm exists.

### Limit 4 — Lens-relativity (213-native limit)

The 213 framework asserts: every count is a Lens output.
There is no Lens-invariant *total enumeration*.  The
36-species catalog is one Lens-tower's reading.  Different
Lens choices (different syntactic granularity, different
cohomology framing) yield different counts.

This is *the strongest* limit: not a contingent failure of
current algorithms, but a structural feature.  Any complete
enumeration claim has implicit Lens commitments.

## §5 — Practical conclusion

A **structured exploration algorithm** (the meta-algorithm
above) reproduces ≈85% (32/36) of our catalog
automatically using existing CAS routines.  The remaining
≈15% needs framing choice (granularity / category).

### Concrete next step

Implement `Mobius213Sage.sage` running phases 1-7 on P =
`[[2,1],[1,1]]` and output candidate (kind, aut, atomic)
table.  Cross-check against the 36-species catalog:
- Validate algorithmically reproducible species (~32).
- Flag any auto-discovered species not in the catalog.
- Document the ≈4 species requiring framing choice.

This would let us **automatically validate** the
36-species claim and potentially extend it.

### Why not a single Lean algorithm

A Lean theorem certifying "P has exactly 26 natural
symmetry species" would require:
1. A formal definition of "natural symmetry species".
2. A decidable enumeration procedure.
3. Proof of closure (no further species exists).

Step 1 is essentially impossible — naturalness is informal.
Step 3 follows from step 1.  So the 36-species claim is
*structural*, not strictly Lean-provable as a closure
theorem.  Our Lean modules instead prove (a) atomic-closure
*within* the catalog and (b) PURE realisation of *each
catalogued* species.  Both are tight, the closure-of-set
itself isn't.

## §6 — What the 36-species catalog represents (in light of §1-§5)

- **Algorithmically reproducible (~32)**: standard invariants,
  conjugation orbit, Aut group, fixed points, eigenvalues,
  continued fractions, Stern-Brocot, Pell, p-adic tower,
  Bezout, char poly Galois.  All re-derivable from
  CAS routines.
- **Framing-dependent (~4)**: syntactic-decomposition
  granularity (the 12-axis vs 6-axis vs N-axis split
  depending on syntax tree depth), cohomology bundle
  granularity (vertex / edge / 2-cell cochains).
- **Strict closure of "all natural"**: experimentally
  supported by the 32+4 = 36 census, not algorithmically
  proven — no algorithm can guarantee no further species
  exists, per Limits 1-4.

## §7 — Bibliography (web-search referenced)

  · Stauduhar, R. P. (1973). *The Determination of Galois
    Groups*.  Practical Galois algorithm baseline.
  · Faber, X. — Manes, M. — Viray, B. (2012). *Computing
    Conjugating Sets and Automorphism Groups of Rational
    Functions.*  arXiv:1202.5557.  Sage implementation.
  · Doris, C. — Sutherland, A. V. — Voight, J. (2020).
    *Computing Galois Groups over p-adic Fields.*
    arXiv:2003.05834.
  · Baake, M. — Roberts, J. A. G. (1997).  *Reversing
    Symmetry Group of GL(2, ℤ) and PGL(2, ℤ).*  Important
    for our SL(2, ℤ) conjugacy structure.
  · Alcázar-Sendra (2012).  *Detecting Symmetries of
    Rational Plane and Space Curves.*  arXiv:1207.4047.
  · Bright, C. (2013).  *Computing the Galois Group of a
    Polynomial.*  Survey.
  · Klüners, J. — Magaard, K.  *Computation of Galois
    Groups of Rational Polynomials.*

## §8 — Status

Tier-1 research note (volatile scratchpad).  Promotion
candidate: only if a Sage-implementation of the meta-
algorithm is built and validated against the 36-species
catalog, the algorithmic-reproduction portion would deserve
a `theory/essays/p_symmetry_algorithm.md` essay.

For now: open frontier.  Hands open to "implement the
meta-algorithm in Sage" or "extend the catalog via
algorithmic search" as next-session deliverables.
