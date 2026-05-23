# Akbulut Cork (exotic 4-manifold structures)

**Status**: Closed at H¹ level (44 PURE / 4 files) + H² extension
(42 PURE / 1 file).  Total: 86 PURE / 5 files / 1 umbrella.
H³ cork-twist effect listed as Open Frontier.

## Overview

The Akbulut–Curtis–Freedman–Hsiang–Stong cork theorem states that
exotic-structure differences on closed simply-connected 4-manifolds
all reduce to a single Z/2 involution (the **cork twist**) on a
contractible substructure (the **cork**).  213's 4-manifold
substrate is the K-deployment family on chartBase ≤ 5; the cork
theorem there has a fully discrete, ∅-axiom realisation.

The 213-native witness:

- **Contractible substructure**: K_{1,4}^{(c=1)} tree branch
  (`K14_cork`, `contractible_b1 = 0`).
- **Z/2 involution**: M_S01 transposition matrix on H¹(K_{3,2}^{(c=2)}),
  proved involutive at the matrix layer (`M_S01_squared_pointwise`).
- **Cork twist**: `corkTwist : Cork213 → Cork213` involution at the
  cork-data layer, alternating `twist_parity` between 0 and 1.
- **Signed exotic count**: `signedCorkTwistCount = +4`, the difference
  of M_S01 fix-counts across twist-even / twist-odd orbit classes —
  the 213-internal replacement for the FW-1 signed Donaldson count.

The cork-frame supersedes the FW-1 signed-Donaldson direction: the
"sign problem" of FW-1 becomes a Z/2 grading on Sym(3)-orbits,
discrete and `decide`-resolved.

## Lean source

- Umbrella: `lean/E213/Lib/Math/AkbulutCork.lean`
- Sub-tree (5 files, 86 PURE):
  - `Foundation.lean` (14) — `Cork213` structure; canonical instances
    `K11_cork`, `K31_cork`, `K14_cork`; well-formedness witnesses;
    bridge to parametric Bipartite cohomology
  - `Twist.lean` (12) — `corkTwist` Z/2 endomorphism; involution on
    each canonical instance; parity-alternation theorems;
    M_S01 correspondence at the matrix layer
  - `SignedOrbits.lean` (13) — per-orbit-type M_S01 fix-counts
    (4, 28, 0); `signedCorkTwistCount = +4` capstone
  - `CorkTheorem.lean` (5) — `cork_embedding_capstone` +
    `cork_uniqueness_capstone` + the 14-conjunct master
    `akbulut_cork_213_native`
  - `HigherTwist.lean` (42) — `Cork213_H2` extends `Cork213` with a
    `host_b2` field; `corkTwistH2` involution; Burnside on C²
    under M_S01 / M_S12 / ρ (fix counts 4 / 4 / 2; Sym(3) orbits = 4
    with sub-decomp (2, 0, 2, 0)); `M_S01_acts_trivially_on_H2`
    (every C² cochain has `M_S01(c) ⊕ c ∈ im δ¹`);
    `signedCorkTwistCount_H2 = +2`; composite
    `signedCorkTwistCount_H1_H2 = +6`
- ∅-axiom status: PURE (all 86 theorems)

## Why K_{1,4} and K_{3,2}^{(c=2)} together

At chartBase 5 (the resolution where forced (NS, NT) = (3, 2)
lives), two K-deployments coexist:

- K_{1,4}^{(c=1)} — tree branch, b_1 = 0, contractible at the
  1-skeleton level → serves as the cork
- K_{3,2}^{(c=2)} — forced critical deployment, b_1 = 8, hosts the
  M_S01 transposition acting on H¹

`chartBase_5_tree_and_critical_coexist` (in the parametric
Bipartite sub-tree) records the coexistence.  The cork is *embedded*
in the critical deployment via the chartBase coincidence; the cork
twist is the M_S01 action on the H¹ basis of the critical deployment,
viewed through the cork's twist-parity field.

## Signed orbit count — why +4

`SignedOrbits.lean` partitions the 60-element Sym(3) × { Cork213
configurations } space into orbits under M_S01:

- Singleton fixed orbits: 4 elements fixed
- Size-3 fixed orbits: 28 elements fixed
- Size-6 fixed orbits: 0 elements fixed

Total fixed by M_S01: 32.  Twist-even orbits (M_S01 acts trivially):
32 elements; twist-odd orbits (M_S01 acts non-trivially): 28
elements.  Signed count: 32 − 28 = **+4**.

This is the 213-internal exotic-structure invariant: it does not
require an external Donaldson polynomial, an external smooth
4-manifold category, or any non-decidable input.

## H² extension (closed)

The cork-twist Z/2 action lifts from H¹ to H² at the 2-skeleton
level via the face-permutation realization of M_S01 (faceSwap_S01:
face 0 fixed, faces 1 ↔ 2).  Key facts (`HigherTwist.lean`):

- C² = `Fin 3 → Bool` (8 cochains, 3 faces of K_{3,2}^{(c=2)})
- Burnside on C² under Sym(3): 4 orbits with sub-decomp (2, 0, 2, 0)
  — 2 singleton orbits = `(0,0,0)` and `(1,1,1) = ω`
- M_S01 acts as identity on H² = C² / im δ¹: every C² difference
  `M_S01(c) ⊕ c` has face-XOR sum 0, i.e., lies in `im δ¹`
- H² has 2 cohomology classes (0, ω), both M_S01-fixed
- `signedCorkTwistCount_H2 = +2`
- Composite H¹+H² signed count: +4 + +2 = +6

Structural reading: ω is the third trivial-irrep component
(alongside ω_00, ω_10, ω_01, ω_11 at H¹), confirming
`3·trivial ⊕ 3·standard` Sym(3) decomposition for H¹+H².  The
cork-twist's H² contribution is fully trivial — at this level
no new sign correction beyond H¹'s +4.

## Open frontier

The cork-twist effect closes at the H¹+H² level.  Two extensions
remain open:

- **H³ cork-twist (b_3)**: M_S01 action on H³ classes at the
  3-skeleton extension (`Filled3CellExtension`, single 3-cell σ³)
  and 4-skeleton extension (`Filled4CellExtension`, σ³ + σ⁴).
  At single-3-cell attaching the action is trivial (M_S01 fixes
  σ³ as a singleton); content emerges at multi-3-cell extensions.
- **Multi-cork structures**: iterated cork-twists on the K-deployment
  family, with cork-of-cork Z/2 actions and higher-order signed
  counts beyond `+4`.

## Connection

- `theory/math/cohomology/bipartite.md` — parametric V32Betti +
  K-deployment family (cork's chartBase ambient)
- `theory/math/cohomology/k32_higher_cohomology.md` —
  higher-cohomology of K_{3,2}^{(c=2)} (host of the cork-twist
  higher action, currently open)
- `theory/math/geometrization_conjecture.md` — KChartLensAbstract +
  K-deployment enumeration (provides the chartBase ≤ 5 scope)
