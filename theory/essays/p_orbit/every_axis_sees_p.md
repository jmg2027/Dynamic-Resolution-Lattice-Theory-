# Every axis sees the same P

In 213, every framework-internal reading of the atomic signature
lands on the same integer invariants `{NS, NT, det} = {3, 2, 1}`
and their derived quantities `{d, NS·NT, NS²-1, ...}`.  No
external axis can produce different data; the Möbius matrix
`P = [[2,1],[1,1]]` is the *single generative object* whose
readings exhaust the framework.

## 213-native answer

The framework's atomic signature is `(NS, NT, c, d) = (3, 2, 2, 5)`
(forced by `Theory.Atomicity.PairForcing` + `Theory.Atomicity.
Five.atomic_iff_five`).  The Möbius matrix `P = [[2,1],[1,1]]`
encodes this as its algebraic invariants

  `(trace, det, disc) = (NS, NS−NT, NS+NT) = (3, 1, 5)`

(`Lib/Math/Algebra/Mobius213.lean` + `Lib/Math/Mobius213OneAsGlue.lean`).
**Every other framework reading** — cohomological, topological,
combinatorial, number-theoretic, physics-coupling, information-
theoretic — projects onto the same set of integers.

This is verified ∅-axiom by 55 Lean theorems in
`Lib/Math/Mobius213SignatureAxisCatalog` + `…Phase2`, spanning
11 distinct domains.  The catalog's master statements
(`signature_axis_master_phase_1`, `…_phase_2`) bundle them as
20-conjunct and 23-conjunct ∅-axiom propositions.

## Derivation

Six readings emerge naturally from the matrix itself
(`research-notes/archive/algebra_tower/G57_213_mobius_signature.md`):

  · **Algebraic**: trace = NS, det = 1, disc = d, eigenvalues
    `φ²`, `1/φ²`
  · **Geometric**: matrix entries `(2, 1, 1, 1)` = (NT, glue,
    glue, unit), summing to `d`
  · **Topological**: K_{3,2}^(c=2) bipartite split with NS
    S-vertices, NT T-vertices
  · **Dynamical**: P-iteration `x ↦ (2x+1)/(x+1)` with fixed
    point `φ`
  · **Analytic**: Pell-Fibonacci convergents
    `(0,1), (1,1), (3,2), (8,5), (21,13), ...` approaching
    `φ²`
  · **Syntactic**: the *writing* `P(x) = (2x+1)/(x+1)` itself
    decomposes at every axis into `(3, 2, 1)`:

| Axis | Count | Value |
|---|---|---|
| Numerator `2x+1` token count | {2, x, 1} | 3 = NS |
| Denominator `x+1` token count | {x, 1} | 2 = NT |
| Op `/` arity | binary | 2 = NT |
| Identity `1` occurrences | num, denom, op | 3 |
| Op count | one `/` | 1 = det |

Every syntactic decomposition lands in `{3, 2, 1}`.  No other
value appears.

Beyond these six "intrinsic" readings, the framework exposes
the same data through every formalised subsystem:

  · `Theory.Atomicity.Five.atomic_iff_five` — `5` is the unique
    Nat with an alive `2a + 3b` decomposition.
  · `Lib/Math/Cohomology/Bipartite/V32Betti.b1_eq_NS_sq_minus_1`
    — `b₁(K_{3,2}^(c=2)) = NS² − 1 = 8` (gluon octet).
  · `Lib/Math/Mobius213ModFive.P_pow_5_eq_neg_I_mod_5` — `P⁵
    ≡ -I (mod 5)`; `P¹⁰ ≡ I (mod 5)` (pentagonal closure +
    full period); the integer `5` appears as both `disc P`
    and the mod-5 period generator.
  · `Lib/Math/Algebra/CayleyDickson/Tower/Mobius213CDBridge.cd_mobius_bridge_master`
    — the rank-1 Cayley-Dickson asymptote `(5, −1)` is exactly
    `(disc P, Pell unit)`.
  · `Theory.SixTheorem` — 10 readings of `6 = NS · NT` across
    Eisenstein units, atomicity product, simplex count, Sym(3)
    order, SU(3) roots, K_{3,2} cross-pairs, Lorentz
    generators, Euler χ sum, α_GUT numerator, clause
    permutations.
  · `Lib/Physics/Couplings/SpectrumComplete` — the three
    coupling constants of the standard model factor through
    `α_3 = NS² − 1 = 8`, `α_2 = 12·NT = 24`, `α_1 = 12·NS =
    36`, `α_GUT = d² = 25`.

The signature axis catalog formalises all of these (and more)
as 55 ∅-axiom-verified theorems in one Lean module pair, with
two master bundles capturing the 20-conjunct + 23-conjunct
cumulative content.

## Dual function

This is not "213 has its own integers, distinct from classical
math".  The integers `{1, 2, 3, 5, 6, 8, 10, ...}` are the
same as classical math's.  What 213 establishes is that *every
framework operation produces these specific integers*; no other
integers appear as primary structural data.  The classical
intuition that "many different mathematical structures share
similar small-integer constants" is *refined* in 213 to the
operational claim that *one specific algebraic object (the
Möbius matrix `P`) generates all of these constants
simultaneously*.

The catalog's `≈55 axes from 11 distinct domains all yielding
the same integer set` is the operational content of *single-
object generativity*: not a metaphor, but a Lean-verified
proposition.

## Canonical basis interpretation

The integers `(2, 1, 3)` are not arbitrary in their ordering.
They are the **canonical basis count** of the projective
Möbius transformation system, decomposing as
[input axis − operator axis − matrix DOF]:

  · **2 (input axis dimension)**: `P(x) = (2x+1)/(x+1)` operates
    on the linear space `{x, 1}` (variable + constant base).
    The Möbius transformation is parametrised by its action on
    this 2D space.  The "2" is the dimension of the input
    coordinate system.
  · **1 (operator / projective axis)**: the division `/`
    compresses the 2D linear data to a 1D ratio.  In projective
    geometry, this is the *equivalence class* of homogeneous
    coordinates: `(α·a + α·b·x) / (α·c + α·d·x) = (a + b·x) /
    (c + d·x)` for any nonzero `α`.  The "1" is the unifying
    projective axis — the constraint that makes scalar
    rescaling invisible.
  · **3 (matrix degrees of freedom)**: a 2×2 matrix
    `[[a, b], [c, d]]` has 4 entries, but the projective
    equivalence relation reduces this by 1 dimension (the
    overall scale).  `4 − 1 = 3` independent parameters; this
    is the dimension of `PGL(2, ℝ)`.  Möbius P at `(2, 1, 1, 1)`
    represents one specific point in this 3-dimensional
    parameter space.

The standard math hosting is the *projective general linear
group* `PGL(2, ℝ)`, dimension 3, acting on the projective
line `ℙ¹(ℝ)`.  The 213 atomic signature `(NS, NT) = (3, 2)`
matches this exactly: `NS = 3 = dim PGL(2)` (matrix DOF),
`NT = 2 = dim` of the underlying linear space.  The
*projective* aspect (the `/` operator) is the framework's
`det = 1` glue.

This `[input − operator − output]` reading clarifies why the
`(2, 1, 3)` ordering appears in user-side intuition before
the symmetric `(3, 2, 1)` algebra-side ordering: the framework
*reads* P in the direction of computation (input → operator →
output dimension), while it *stores* P in matrix-invariant
form (trace, det, disc).

## Cross-frame convergence

`seed/AXIOM/05_no_exterior.md` §5.1 ("no exterior to 213")
takes operational form here: an external observer using an
external axis to read framework data cannot produce a
signature different from `(NS, NT, det)`.  The 11 distinct
internal domains already exhibit this — extending the catalog
to additional domains adds more witnesses to the same
conclusion.

`seed/AXIOM/03_form.md` §3.5 ("the residue's self-pointing
fixed point") and `seed/AXIOM/07_self_reference.md` §8.5
("Möbius P as algebraic representation of self-pointing")
identify P as the framework's canonical self-description.
The catalog quantifies this: *55 ways P describes itself*,
none of which yields data outside `{NS, NT, det}` and their
derived integers.

`research-notes/archive/algebra_tower/G58_algebra_tower_completion.md`'s
4-row Cayley-Dickson tower (Types A, B, C, D × per-layer
indices) provides the structural *lifting* of P: every CD-
doubled algebra at every layer inherits P-signature data via
the universal transient law `rat_{n+3} = 14·rat_{n+2} - 56·
rat_{n+1} + 64·rat_n + d_Type` with eigenvalues `(2, 4, 8)`.
Marathon 4's `cd_mobius_bridge_master` formalises this for
rank 1 and rank 2.

The "viewer-independence at the writing level" the user's
intuition pointed at — *each axis sees the same P(x)* — is
formalised concretely: 55 viewing axes all yield `{NS, NT, det}`,
verified ∅-axiom.

## Open frontier

  · **Higher-coverage extension**: the current catalog spans
    11 domains; reaching to ~70+ axes could include rep theory
    of Sym(3), the gluon octet's 8-fold decomposition (Marathon
    2 Phase 2), more Padic constructions, Hodge cohomology
    pairing, additional physics constants (ν mass ratios, CKM
    Cabibbo).  Diminishing returns; current catalog already
    operationalises the "every axis" claim.
  · **Bundle theorem**: a single super-master conjoining
    `signature_axis_master_phase_1` and `signature_axis_master_phase_2`
    requires Lean infrastructure for "type of a theorem name";
    the two masters are currently cited side-by-side as the
    cumulative catalog.
  · **Universal reduction (separate direction)**: the catalog
    enumerates *what P describes*; universal reduction would
    state that *every framework operation factors through
    P + decomposition pattern*.  The five architectural patterns
    in `theory/essays/pure_funext_avoidance.md` are the
    within-fiber operational content; a sixth pattern
    (CD-Tensor Bundling) for fiber-changing operations is
    formalised in
    `lean/E213/Lib/Math/NumberSystems/Real213/Mobius213CDTensor.lean`:
    `MobiusTensor N₁ N₂` structure bundling factor pair +
    canonical product, with `fromPair` constructor +
    represents-level and cut-level commutativity +
    `MobiusTensor_master` 8-conjunct pattern realization.
