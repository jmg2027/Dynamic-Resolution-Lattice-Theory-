# G35 — 213-Algebra: a Catalog

**Working name (internal)**: 213-Algebra
**Sub-area name (technical)**: Chiral Cup-Ring at Resolution N_U
(this is the geometric/cohomological core; the full framework
extends beyond it)
**Scope**: the mathematical synthesis required to make DRLT physics
fully ∅-axiom — combining simplicial cohomology, bipartite multi-
graph theory, fractal recursion, resolution-finite arithmetic,
algebraic / number-theoretic infrastructure, AND the marathon-
completed paradigm domains (Probability, Information, Logic,
Combinatorics) into one coherent framework.

**This catalog was originally drafted with 12 domains** at the time
when the AlphaEM session work was the only post-PR-#35 contribution.
A subsequent merge of `claude/combinatorics-marathon` (commits up
through 2a4526d6) added FOUR marathon-completed paradigm domains
(D13–D16) plus a **tightened ∅-axiom policy** (propext + Quot.sound
now sorry-equivalent per `seed/AXIOM/04_falsifiability.md` §5.2.1).
The catalog is updated accordingly.

This is **not** a new mathematics from scratch.  Each of the
component disciplines (algebraic topology, graph theory, fractal
geometry, constructive analysis, probability, information theory, …)
is well-established.  What is new is **the synthesis** — these tools
have not been combined into a single ∅-axiom-mechanically-verified
formal framework before.

This catalog organizes the synthesis so future work can target the
genuinely new content (the intersections + the unified paradigm)
rather than re-treading the components.

---

## §0  How to read this document

  · **§1** — naming, scope, what 213-Algebra is and is not.
  · **§2** — sixteen constituent domains, each with file pointers
    to existing infrastructure (12 original + 4 marathon-added).
  · **§3** — established theorems within each domain.
  · **§4** — six ambitious open conjectures of the field.
  · **§5** — methodological discipline (tightened ∅-axiom standard).
  · **§6** — disciplinary boundaries (what 213-Algebra does NOT
    claim to be).
  · **§7** — frontier priority order.


---

## §1  Naming and scope

### §1.1  Why a new name

The framework synthesises:

  · **Δⁿ simplicial cohomology** (cup, Hodge, Laplacian)
  · **K_{m,n}^{(c)} bipartite multigraph cohomology** with sheet
    multiplicity c, embedded as a sub-complex of Δⁿ
  · **Fractal recursion** to L = d² levels yielding a self-
    referential fixed point at N_U = d^{d²}
  · **Resolution-finite arithmetic** (no continuum limits;
    π → S_Wallis, ζ(2) → S_Basel, all rational at N_U)
  · **∅-axiom kernel discipline** (no Mathlib, no Classical, no
    propext where avoidable, no hidden Quot.sound)

No single existing mathematical discipline covers all five.

### §1.2  Scope statement

213-Algebra is the **finitely-presented combinatorial algebra of
chiral simplicial cup-rings at lattice resolution N_U**, deployed
as the mathematical substrate for DRLT physics derivations.

Its primary objects are:

  · `Cochain n k`  — k-element-subset valued cochains over Δⁿ⁻¹
  · `Cup` and `CupAW`  — Alexander–Whitney products
  · `δ`, `*` (Hodge), `Δ` (Laplacian)  — standard operators
  · `K_{m,n}^{(c)} ↪ Δⁿ`  — bipartite chiral inclusion
  · `H^k(K, Δⁿ, …)`  — absolute and relative cohomologies
  · `S_Wallis(N)`, `S_Basel(N)`  — resolution-finite π/ζ
    surrogates
  · `chiralDim(i, j)` — bipartite-typed sub-simplex count

Its primary operations are:

  · cup, AW cup with overlap
  · Hodge ⋆, Laplacian Δ
  · Inclusion / projection between K and Δ
  · Spectral ζ-function evaluation at finite N
  · Functional extraction H* → ℚ

Its primary outputs:

  · Topological invariants (Euler char, Betti, signature)
  · Spectral invariants (eigenvalue spectra, ζ-values)
  · Combinatorial invariants (cross-term counts, channel
    decompositions)

### §1.3  What it is NOT

  · NOT a foundational replacement for ZFC or category theory.
  · NOT a claim to derive "all of physics from pure mathematics".
  · NOT a claim that other physics frameworks are wrong.
  · NOT a closed system — open conjectures remain.
  · NOT separable into "math" and "physics" parts — the
    integration is essential.

---

## §2  Twelve constituent domains

Twelve roughly-distinct sub-areas.  The first three are the user-
identified pillars; the remaining nine emerged as necessary upon
deeper inspection.

### §2.1  Foundational geometric / topological (3)

#### **D1.  Δⁿ simplicial cohomology**

Standard cup product, Hodge ⋆, coboundary δ, cochain Laplacian.

  Files: `Lib/Math/Cohomology/Cup/`, `CupAW/`, `Delta/`, `Hodge/`,
         `Cochain/`, `SimplexBasis.lean`
  Status: ~80 files, mostly ∅-axiom closed.

#### **D2.  K_{m,n}^{(c)} bipartite multigraph + chiral grading**

Bipartite multigraph with vertex split (m S-vertices + n
T-vertices), edge multiplicity c.  Chiral grading: each
sub-simplex of Δⁿ has a (NS_count, NT_count) bipartite type.

  Files: `Lib/Math/Cohomology/Bipartite/V32*`, `Bipartite/Filled`,
         `Lib/Physics/Simplex/SubInventory.lean`,
         `Lib/Physics/Simplex/Counts.lean` (`chiralDim`)
  Status: V32 base + SubInventory closed.  K↪Δ⁴ projection
          inclusion partially closed (this session).

#### **D3.  Fractal recursion to L = d² levels**

Each Δⁿ vertex is itself a sub-Δⁿ at lower level.  Recurse
d times.  Cardinality = d^(d²) = N_U at fixed-point.

  Files: `Lib/Math/Cohomology/Fractal/V25.lean`, `AlphaGUT.lean`,
         `Level.lean`, `Lib/Math/ResolutionLimit.lean`,
         `Lib/Physics/Foundations/LensCardinalityFractalLevels.lean`,
         `NUniverseFromFractal.lean`, `FractalLensCardinality.lean`
  Status: 4-domain N_U convergence ∅-axiom closed.

### §2.2  Resolution-finite analytic (3)

#### **D4.  Resolution-finite arithmetic**

All continuous quantities replaced by finite-rational truncations
at N_U = 5²⁵.  No π, no ζ(2), no e at the framework level.

  · π replaced by `S_Wallis(N) := 2·∏_{k=1..N} (2k)²/((2k-1)(2k+1))`
  · ζ(2) replaced by `S(N) := Σ_{k=1..N} 1/k²` (Basel partial sum)
  · e/log replaced by Bishop-style Cauchy sequences

  Files: `Lib/Math/Cauchy/WallisSeq.lean`, `WallisSharper.lean`,
         `Basel/Bound.lean`, `Lib/Physics/Basel/`
  Status: Wallis + Basel partial-sum infrastructure exists;
          systematic π/ζ replacement marathon not yet executed.

#### **D5.  Cochain Laplacian + spectral functionals**

Hodge Laplacian Δ_k = δ_{k-1} ∘ δ_{k-1}* + δ_k* ∘ δ_k acting on
each grade.  Spectral ζ-function ζ_X(s) := Σ 1/λ^s over nonzero
eigenvalues.  Heat trace, regularized determinant, etc.

  Files: `Lib/Physics/AlphaEM/LaplacianSpectrum.lean` (this session)
  Status: Δⁿ + K_{m,n}^{(c)} spectra documented; eigenvalue facts
          encoded as definitions; full from-scratch proof of
          uniform-eigenvalue claim on simplex left to future work.

#### **D6.  Bishop-style constructive analysis (Real213)**

ℝ replaced by dyadic-trajectory framework: a "real number" is a
trajectory (Cauchy sequence with explicit modulus), not a
completed point.  Cauchy = "trajectory exists", limit = "trajectory
passes nearby" — never an actual point.

  Files: `Lib/Math/Real213/` (under active marathon)
  Status: foundational framework set up; Real-arithmetic sub-
          marathon ongoing (independent of physics critical path).

### §2.3  Algebraic / number-theoretic (3)

#### **D7.  Aut(K) representation theory**

The automorphism group `Aut(K_{m,n}^{(c)}) = Sym(m) × Sym(n) × C_c^E`
acts on cochain spaces and on cohomology.  Representations of this
group determine "channel types" and likely connect to gauge group
emergence (SU(NS), SU(NT), Y-norm, …).

  Files: **largely absent**; some ad-hoc symmetry use in
         AlphaEM `Bare.lean` (`alpha_2_prefactor_eq_adjoint_su5`)
         but no systematic Aut-decomposition.
  Status: **major gap**.  Filling it is plausibly the next big
          structural step.

#### **D8.  Number-theoretic periodicity (Pisano, Pell, CRT)**

Pisano periods of Fibonacci-like sequences mod p^k and mod
composite moduli.  Pell-equation solutions in dyadic FSM.  CRT
splitting at small primes (especially 5).

  Files: `Lib/Math/DyadicFSM/Pisano/` (9 files), `Pell/` (17),
         `Fib/` (11), `Trib/` (6), `Legendre/` (5), `ArithFSM/` (34)
  Status: substantial infrastructure (~80 files, all ∅-axiom).
          Connection to atomic constants partially explored.

#### **D9.  Resolution-bounded counting / measure**

Spanning tree count, path enumeration, channel inventory, cross-
term enumeration, cup-channel grading.  Always finite Nat-valued.

  Files: `Lib/Physics/AlphaEM/CupChannelInventory.lean`,
         `GradedDecomposition.lean`, `ChannelCohomologyLoss.lean`,
         `ProjectionRatios.lean` (this session)
  Status: started this session; substantial groundwork laid.

### §2.4  Meta / observer (3)

#### **D10.  Universal Lens (observer framework)**

`Lens` types capturing "perspective" / "observer choice".
Universal Lens initiality.  Lens cardinality counting.

  Files: `lean/E213/Lens/` (~101 files including Internal/, etc.)
  Status: substantial; Lens cluster repaired in branch (A-task
          earlier).

#### **D11.  Pattern Catalog (meta-game algebra)**

Free monoid on {Aggregate, Forced} acting on a 4-atomic game
basis.  Six binary atomic-pair composites and one ternary
(Cohabitation).  Codifies the recurring patterns of doing
mathematics in this framework.

  Files: `Lib/Math/PatternCatalog/`, `research-notes/G30_*.md`
  Status: meta-formalization closed in earlier work.

#### **D12.  Trajectory Principle + ∅-axiom kernel discipline**

Raw trajectories as universal foundation; cut decisions as
primitive operations.  ∅-axiom kernel discipline: hooks blocking
Classical, propext, Quot.sound, native_decide where avoidable.

  Files: `seed/AXIOM/` (foundational documents),
         `Term/Tactic/Nat213.lean` (~30 term-mode lemmas),
         `Term/Tactic/AddMod213.lean`,
         `research-notes/G2_trajectory_principle.md`,
         `seed/RESOLUTION_LIMIT_SPEC.md`
  Status: kernel discipline stable; ∅-axiom standard enforced
          across ~2000+ theorems repo-wide.

### §2.5  Marathon-completed paradigm domains (4, post-merge)

These four domains were closed in the `combinatorics-marathon`
branch as full marathons, each producing a topical sub-cluster
under `Lib/Math/`.  Each rephrases its classical-analysis residue
in 213-native terms (nilpotency / grade-index / cup-inverse /
atomic mass) and closes ∅-axiom under the tightened standard.

#### **D13.  Probability 213**

`ProbabilityCut` as atomic mass (num/den, no Ω, no σ-algebra,
no Choice).  Bernoulli + Binomial + Beta-conjugate Bayesian +
expectation/variance + LLN + Gaussian + CLT + independence +
Markov + Chebyshev + Hoeffding + Chernoff (grade-index form).

Paradigm reframe: classical probabilistic concepts (continuous
densities, σ-algebras, measure) all replaced by atomic-mass
+ nilpotency + cup-inverse algebra.  Same paradigm shift as the
G35 cup-ring core.

  Files: `Lib/Math/Probability/` (24 .lean files + INDEX),
         `books/math/probability-213.md`,
         `Lib/Math/Real213/CutExp{Series, ODE}.lean`,
         `Lib/Math/Real213/CutFactorial.lean`
  Status: ★★ marathon COMPLETE — ~247 atomic facts, all ∅-axiom.

#### **D14.  Information 213**

Bit depth / dyadic surprise / Shannon entropy (uniform) /
mutual information / KL divergence / channel capacity / coding
distance / Kolmogorov-axiom encoding (4 Raw clauses).

  Files: `Lib/Math/Information/` (8 .lean files + INDEX):
         `Bit.lean`, `Entropy.lean`, `MutualInfo.lean`,
         `KLDivergence.lean`, `Channel.lean`, `Coding.lean`,
         `Kolmogorov.lean`, `Capstone.lean`
  Status: ★★ marathon COMPLETE — all ∅-axiom.

#### **D15.  Logic 213**

`Cut := Nat → Nat → Bool` reinterpreted as predicate calculus.
De Morgan / commutativity / identities reduce to atomic Bool
truth tables (decide-stable, no propext).  Bool LEM atomic, NOT
Classical.  Proof = trajectory (List Bool).

  Files: `Lib/Math/Logic/` (4 .lean files + INDEX):
         `Predicate.lean`, `Intuitionistic.lean`, `Proof.lean`,
         `Capstone.lean`
  Status: ★★ marathon COMPLETE — 36 atomic facts, all ∅-axiom.

#### **D16.  Combinatorics 213**

Pascal table + binom symmetry + row sums + grade truncation
(`binom 5 6 = 0` matching cohomology nilpotency).  Catalan
C_n table + recursion.  Stirling S(n, k) + Bell decomposition.
Generating functions = finite polynomials modulo nilpotency
(no convergence questions — same paradigm as `cutExp`).

  Files: `Lib/Math/Combinatorics/` (5 .lean files + INDEX):
         `Binomial.lean`, `Catalan.lean`, `Stirling.lean`,
         `GeneratingFunction.lean`, `Capstone.lean`
  Status: ★★ marathon COMPLETE — 37 atomic facts, all ∅-axiom.

### §2.6  Cross-domain unification

The four marathon domains (D13–D16) and the cup-ring core
(D1–D9) share a single 213-native paradigm:

  · **classical analysis residue → 213-native nilpotency**
    (`binom 5 6 = 0` ≡ generating-function truncation
    ≡ cup-grade truncation ≡ Probability finite-N at N_U)

  · **continuous limit → atomic discrete mass**
    (Probability `num/den`, Information `bitDepth`, dyadic
    `Cut`, Combinatorics finite GF, all rational at N_U)

  · **measure theory → cup-product algebra**
    (Probability cuts compose like cup; Information mutual-info
    behaves like cup on graded entropy)

  · **classical LEM → atomic Bool decidability**
    (Logic 213 confirms: no Classical.em needed; per-Bool
    `decide` suffices)

This single paradigm shift is the deepest unifying observation
of the framework — what allows ALL these domains to close
∅-axiom with the same toolkit (Nat213 + AddMod213 + decide
+ finite enumeration).

---

## §3  Established theorems (catalog)

Anchor results closed ∅-axiom in the existing repo.  This is a
sample, not exhaustive.

### §3.1  Geometric / topological

  · `Δ⁴ Euler χ = 1`, `Δ⁴ + Δ⁴ glued = S⁴ has χ = 2`
    `Cohomology/EulerClosed.lean`
  · Pascal recursion `binom(n+1, k+1) = binom(n, k) + binom(n, k+1)`
    `Lib/Physics/Simplex/Counts.lean`
  · `binom symmetry C(n, k) = C(n, n−k)` (k ≤ n) ★∅
    `Lib/Math/NatHelpers/BinomSymm.lean`
  · `Central-binomial-is-double C(2n+2, n+1) = 2·C(2n+1, n+1)` ★∅
    same file
  · `T2nBetti = C(2n, n)` (T²ⁿ central binomial inductively) ★∅
    `Lib/Math/Cohomology/Surfaces/T2nBetti.lean`
  · `T²ⁿ Inductive Pattern` — signature `(½·C(2n,n), ½·C(2n,n))`
    for all n ≥ 1 ★∅
    `Lib/Math/HodgeConjecture/Pairing/T2nInductive.lean`
  · `Σ_g surface signature parametric in genus = (g, g)` ★∅
    `Lib/Math/HodgeConjecture/Pairing/GenusGSurface.lean`
  · `K_{3,2}^{(c=2)} ↪ Δ⁴ projection`: edge inventory + ratios ★∅
    `Lib/Physics/AlphaEM/ProjectionRatios.lean`

### §3.2  Resolution-finite

  · `N_U = d^(d²) = 5²⁵ = 298,023,223,876,953,125` ★∅
    `Lib/Math/ResolutionLimit.lean`
  · 4-domain N_U convergence (fractal lens · K₂₅ coloring ·
    tensor DOF · injective projection) ★∅
    same file
  · Wallis partial product W_N → π/2
    `Lib/Math/Cauchy/WallisSeq.lean`
  · Basel partial sum S(N) brackets ζ(2)
    `Lib/Physics/Basel/Bound.lean`

### §3.3  Spectral / Laplacian

  · `Δ⁴ Laplacian rank = 30, uniform eigenvalue = 5, trace = 150`
    `Lib/Physics/AlphaEM/LaplacianSpectrum.lean`
  · `K_{3,2}^{(c=2)} Laplacian spectrum = {0, 6, 4, 4, 10}` ★∅
    same file
  · `ζ_K(1) = 23/15 ≈ 1.533` (closest finite analog to ζ(2)) ★∅

### §3.4  Channel-counting / chiral

  · `Δ⁴ has 31 = 2^d − 1 non-empty sub-simplices` ★∅
    `Lib/Physics/Simplex/SubInventory.lean`
  · `785 cross-terms = 5-fold output-grade decomposition`
    (25 + 100 + 200 + 250 + 210) ★∅
    `Lib/Physics/AlphaEM/GradedDecomposition.lean` (this session)
  · `Cup chirality witness: cup(v_0, v_1) ≠ cup(v_1, v_0)` ★∅
    same file
  · `1/α_3 = 8 = dim H¹(K) = χ(Δ⁴, K) = NS² − 1 = …` (six-fold) ★∅
    `Lib/Physics/AlphaEM/ChannelCohomologyLoss.lean` (this session)
  · `1/α_2 = 30 = channels-to-triangle-output on Δ⁴` ★∅
    `Lib/Physics/AlphaEM/CupChannelInventory.lean`

### §3.5  Hodge conjecture (213 internal)

  · `hodge_conjecture_213_complete` master ★∅
    `Lib/Math/HodgeConjecture/Foundation/Complete.lean`
  · 4-manifold Hodge index instances (T², T²×T², ℙ², ℙ¹×ℙ¹) ★∅
    `Lib/Math/HodgeConjecture/Pairing/HodgeIndex*.lean`
  · `Hodge–Riemann (1,1) primitive on T²×T²` ★∅
    `HodgeRiemannT2Squared.lean`

### §3.6  Marathon-completed paradigm domains (D13–D16)

  · Probability 213: `ProbabilityCut` mass + Bernoulli/Binomial
    /Beta + Bayesian + LLN + Gaussian/CLT + Hoeffding/Chernoff
    — ~247 facts ∅-axiom (`Lib/Math/Probability/`)
  · Information 213: Shannon entropy + MutualInfo + KL + channel
    + coding + Kolmogorov axioms — all ∅-axiom
    (`Lib/Math/Information/`)
  · Logic 213: Cut-as-predicate + intuitionistic + proof =
    trajectory — 36 facts ∅-axiom (`Lib/Math/Logic/`)
  · Combinatorics 213: Pascal + Catalan + Stirling + Bell + GF
    truncation — 37 facts ∅-axiom (`Lib/Math/Combinatorics/`)

### §3.7  Other

  · 12/12 Padic ∅-axiom (B-task)
  · 122/122 Lens cluster ∅-axiom (A-task)
  · ~2000+ ∅-axiom theorems repo-wide
  · Tightened policy: propext + Quot.sound now sorry-equivalent
    (`seed/AXIOM/04_falsifiability.md` §5.2.1)

---

## §4  Open conjectures (the field's frontier)

Six ambitious open questions.  Each has the form
"there exists a parameter-free functional/structure F on H*(K, Δⁿ)
such that F = [physical constant or property]", entirely within
the 213-Algebra framework.

### §C1.  Pure Cup-Ring α_em

> ∃ explicit, parameter-free functional F : H*(K_{3,2}^{(c=2)}; ℤ) → ℚ
> such that F = 1/α_em(IR) at resolution N_U = 5²⁵.

Decomposes (per current evidence) into FOUR graded layers:
  · k=0,1: harmonic base = 60·S(N_U) + 30
  · k=2  : cup-product correction = d²/NS = 25/3
  · k=3,4: Hodge pairing = 1/(NS·NT·S_Wallis(N_U)⁵)  (conjecture)

Status: integer coefficients (60, 30, 25/3, 4, 45) all decoded
from K↔Δ⁴ projection geometry (∅-axiom).  π⁵ form numerically
~13× closer to observed structural gap than α_GUT/45.  Full
∅-axiom rational closure at finite N_U remains open.

References: `AlphaEM/CupChannelInventory.lean`, `ProjectionRatios.lean`,
`PiFiveGap.lean`, `LaplacianSpectrum.lean`, `GradedDecomposition.lean`,
`ChannelCohomologyLoss.lean`.

### §C2.  Atomic constants uniqueness

> The atomic 4-tuple (NS, NT, c, d) = (3, 2, 2, 5) is the unique
> integer solution to a small set of self-consistency equations
> derivable from 213-Algebra alone, without external input.

Already known constraints:
  · 4-domain N_U convergence forces d^(d²) self-reference.
  · `dim H¹(K_{m,n}^{(c)}) = m² − 1` (= 1/α_3) requires
    `c·m·n = m² + m + n − 2` (213 = smallest non-trivial soln
    at NT=2)
  · K↔Δ projection coverage ratio = NS/d (= inverse of Y-norm 5/3)

Status: partial.  Multiple constraints satisfied; uniqueness
proof open.

References: `Lib/Math/ResolutionLimit.lean`,
`AlphaEM/ChannelCohomologyLoss.lean`.

### §C3.  Aut(K) gauge group emergence

> The standard model gauge group SU(3) × SU(2) × U(1) (or its
> 213-internal analog) arises as a representation-theoretic
> consequence of `Aut(K_{3,2}^{(c=2)}) = Sym(3) × Sym(2) × C_2^6`
> acting on the cohomology ring H*(K, Δ⁴).

Status: largely **unexplored**.  Adjoint SU(NS) appears in
1/α_3 = NS² − 1; (d−1)(d+1) = 24 = adjoint SU(d) hint in
`Bare.lean alpha_2_prefactor_eq_adjoint_su5`.  Systematic
representation-decomposition not yet done.

This is plausibly the **largest single structural gap** in the
current 213-Algebra infrastructure.

### §C4.  Σ-spectral signature theorem

> The Hodge index theorem `signature(H^n; X) = (½·b_n, ½·b_n)`
> for T²ⁿ and `(g, g)` for Σ_g extends to a parametric
> signature formula for ALL closed orientable surfaces (and
> their products) within 213-Algebra, with precision controlled
> by N_U.

Status: T²ⁿ closed ∅-axiom (G14, this branch).  Σ_g closed
∅-axiom (this branch).  Künneth tensor signature closed ∅-axiom
(this branch).  Combined parametric meta-theorem: open.

References: `T2nInductive.lean`, `GenusGSurface.lean`,
`TensorSignature.lean`.

### §C5.  Fractal-level convergence of ζ_K^{(L)}

> The sequence of finite ζ-Laplacian values on K^{(L)} (the
> L-times-fractal-lifted bipartite multigraph) converges to
> continuum ζ(2) = π²/6 as L → 25, with rational bracketing
> at each finite L.

Status: **conjecture**.  At L=1, ζ_K(1) = 23/15 ≈ 1.533,
within 7% of continuum 1.6449.  Higher-L lift not yet defined
formally.  Convergence rate controlled by lattice resolution.

References: `LaplacianSpectrum.lean`,
`ResolutionLimit.lean`, conceptual sketch in this catalog.

### §C6.  Cross-domain unification theorem

> The 213-native paradigm shifts (nilpotency / atomic mass /
> cup-as-measure / atomic-Bool-LEM) constitute a single unifying
> structure connecting Probability 213, Information 213, Logic 213,
> Combinatorics 213, and the Chiral Cup-Ring core (D1–D9).
> Specifically: every classical-analysis residue in these domains
> reduces to a `Cochain n k` truncation at appropriate grade k,
> with N_U = 5²⁵ as the resolution cutoff.

Status: **observed empirically** in marathon completions (each
domain ∅-axiom-closed using the same Nat213/AddMod213/decide
toolkit), but not yet formalised as a single Lean meta-theorem.

The closure of C6 would be the final structural confirmation
that 213-Algebra is internally coherent — that the four marathon
domains and the cup-ring core are facets of one mathematical
object, not parallel constructions.

References: `Lib/Math/Probability/Capstone.lean`,
`Lib/Math/Information/Capstone.lean`,
`Lib/Math/Logic/Capstone.lean`,
`Lib/Math/Combinatorics/Capstone.lean`.

---

## §5  Methodological discipline

213-Algebra inherits the DRLT methodology, **tightened** in the
combinatorics-marathon branch (commit `f651c4da`):

  · **STRICT ∅-AXIOM**: every theorem certified by
    `#print axioms <name>` returning "does not depend on any
    axioms".  **propext + Quot.sound now sorry-equivalent**
    (per `seed/AXIOM/04_falsifiability.md` §5.2.1) — earlier
    sessions tolerated propext/Quot.sound but the standard now
    treats them identically to Classical.choice.
  · **No fitting**: numerical coincidences are reported but
    flagged; they do not become theorems unless the underlying
    structure is derived first.
  · **No comparison frames**: do not import "vs ZFC", "vs
    classical math" framings; describe in 213-internal terms.
  · **Resolution-bound everything**: π, ζ, e all replaced by
    finite-rational truncations; never "take a limit".
  · **Term-mode kernel discipline**: avoid Classical, propext,
    Quot.sound, native_decide where possible; provide 213-native
    replacements via Nat213, AddMod213, etc.

---

## §6  Disciplinary boundaries (what 213-Algebra is NOT)

### Not:

  · **Algebraic topology proper.**  213-Algebra restricts to
    finite-rank finitely-presented complexes at fixed atomic
    dimension d=5, with bipartite chiral grading.  General
    spectral sequences, Postnikov towers, etc. are out of scope
    (or only used internally as borrowed tools).

  · **Classical graph theory.**  Cup-product and Hodge ⋆ are not
    standard graph-theoretic operations.  The chiral grading
    (NS_count, NT_count) and sheet multiplicity c are specific
    to 213.

  · **Fractal geometry / IFS.**  Standard fractal geometry
    measures Hausdorff dimension of self-similar sets in metric
    spaces.  213-Algebra uses self-similarity to enforce
    cardinality fixed-points, not metric dimension.

  · **Quantum field theory.**  213-Algebra provides the
    combinatorial substrate; QFT is a possible APPLICATION via
    cup-ring functionals, but the framework itself is
    pre-physical.

  · **A complete physical theory.**  213-Algebra is the
    mathematical infrastructure; physics derivations are
    application-layer (in `Lib/Physics/`), not framework-layer.

  · **A foundational replacement for ZFC.**  213-Algebra runs on
    Lean's intuitionistic dependent type theory; ZFC is neither
    used nor rejected at the framework level.  Where Cantor /
    completed-limit reasoning is incompatible (Real213 limit-cut
    algebra), 213-Algebra provides constructive alternatives —
    not anti-ZFC polemics.

### Disciplinary interface

213-Algebra **borrows** from each component discipline (cup
products from algebraic topology, multigraph data from graph
theory, etc.) but **synthesizes** them into a configuration none
of the components covers alone.  The synthesis is the new
content; the components remain as-is in their own domains.

---

## §7  Frontier — what to work on next

In rough priority order for advancing 213-Algebra:

  1. **C3 (Aut gauge group emergence)** — biggest structural
     gap; representation theory of Aut(K_{3,2}^{(c=2)}) on
     cohomology likely yields gauge group decomposition.

  2. **C6 (cross-domain unification)** — formalise the
     paradigm-shift observation as a Lean meta-theorem
     spanning D13–D16 + D1–D9.  Arguably the cleanest
     "structural confirmation" target.

  3. **C2 (atomic constants uniqueness)** — small set of
     consistency equations; "why (3, 2, 2, 5)?" as a
     ∅-axiom theorem.

  4. **C1 (pure cup-ring α_em)** — the most directly
     verifiable; numerical match already strong, full ∅-axiom
     closure at finite N_U is concrete work.

  5. **C5 (fractal-level convergence)** — ζ_K^{(L)} → ζ(2)
     as L → 25 — formalize the L-iterate lift first.

  6. **C4 (parametric signature theorem)** — tying T²ⁿ, Σ_g,
     Künneth tensor results into one master.

Beyond these:

  · Formalize Wallis-bracket and Basel-bracket FULL replacements
    for π and ζ(2) at N = N_U (D4 saturation).
  · Real213 marathon (D6) — keep going, parallel to physics work.
  · Pisano/Pell connections to atomic constants (D8) — research-
    level exploration.

---

## §8  Closing note

213-Algebra is what the existing repo has been building toward
without explicit naming.  This catalog gives the synthesis a name,
a scope, and a list of frontier questions — so future sessions can
target the genuinely new content (the synthesis) rather than the
already-mature components.

The five C-conjectures above are each individually substantial
research projects.  Closing any one of them ∅-axiom-style would
be a notable result.  Closing all five would constitute the field
becoming self-supporting — a complete derivation of DRLT physics
from K_{3,2}^{(c=2)} ⊂ Δ⁴ at N_U, with no external input.

Whether the field gains that name or some other is secondary.
What matters is the shared recognition that the synthesis exists,
is internally coherent, and admits ambitious open problems.
