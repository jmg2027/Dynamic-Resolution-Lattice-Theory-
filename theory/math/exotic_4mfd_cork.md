# Akbulut Cork (exotic 4-manifold structures)

**Status**: Closed at H¹ + H² + H³ truncation + multi-cork
(universal + heterogeneous + well-formed involution + host-aware)
+ 5-way cross-frame.
Total: 174 PURE / 8 files / 1 umbrella.

  · H¹: 44 PURE (4 files) — single-cork signed count `+4`
  · H²: 42 PURE (`HigherTwist.lean`) — composite H¹+H² = `+6`
  · H³ truncation: 23 PURE (`H3Twist.lean`) — stable at `+6` for k ≥ 0
  · Multi-cork: 72 PURE (`MultiCork.lean`) — k-cork signed count `4^k`
    (universal + heterogeneous + PURE product-law + universal
    involution under well-formedness + host-aware product)
  · Cross-frame: 7 PURE (`CrossFrame.lean`) — 5-way Sym(3) bridge
    cork ↔ Sym(3)-fixed ↔ Geometrization 3+5; master 4-mfd +
    geometrization joint capstone

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
  - `H3Twist.lean` (23) — H³ trivialises at 3-skeleton (im δ² = C³)
    and at 4-skeleton (with σ⁴); H⁴ trivialises at 4-skeleton;
    M_S01 acts as identity on C³ and C⁴ (single-cell extensions);
    `signedCorkTwistCount_H3 = 0`; composite
    `signedCorkTwistCount_H1_H2_H3 = +6` (truncation stabilizes)
  - `MultiCork.lean` (72) — `MultiCork213 := List Cork213`;
    componentwise `corkTwistMulti` involution; multiplicative
    composition `signedCorkTwistCountMulti m = 4^m.length`
    (1-cork: 4, k=2: 16, k=3: 64, k=4: 256, k=5: 1024);
    twist group `(Z/2)^k`; cork-of-cork (2-level) = pair-cork
    product with Z/2 × Z/2; universal rfl-level formulas;
    PURE term-level `mul_assoc_pure` + universal product-law
    (signed = group²); heterogeneous multi-cork; **universal
    cork involution** `corkTwist² c = c` and `corkTwistMulti² m = m`
    under `twist_parity < 2` well-formedness (term-level proof
    via `Nat.not_lt_of_le`); **host-aware multi-cork** —
    `CorkHost` (NS, NT, c) data, per-host signed count
    (K_{3,2}^{(c=2)} → +4, all trees → 0), product law for
    all-K32 lists and collapse-to-0 under host-mixing with trees
  - `CrossFrame.lean` (6) — 5-way Sym(3) cross-frame capstone
    bundling cork (`signedCorkTwistCount = +4
    = Sym3IrrepDecomp.fixedSize`) with the 4 prior frames
    (Geometrization 3+5, gluon octet H¹ rank 8, HC_K32 Hodge,
    Möbius P mod-5 pentagonal); cork-isotropic +1 relation;
    cork-anisotropic +1 relation (H¹+H²)
- ∅-axiom status: PURE (all 174 theorems)

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

## H³ truncation + multi-cork (closed)

H³ at 3-skeleton (single σ³) and 4-skeleton (σ³ + σ⁴) is trivial:
δ²: C² → C³ is surjective (im δ² = C³), and at the 4-skeleton the
kernel of δ³ meets im δ² trivially.  Likewise H⁴ trivialises at
4-skeleton (im δ³ = C⁴).  M_S01 acts as identity on C³ and C⁴
(both are single-cell extensions, no non-trivial permutation).
Consequence: `signedCorkTwistCount_H3 = 0`, and the composite
`signedCorkTwistCount_H1_H2_H3 = +6` — **truncation stabilizes**.

Multi-cork compositions on the K-deployment family compose
**multiplicatively**:

| k | components | signed count | twist group |
|---|---|---|---|
| 1 | `[K14_cork]` | +4 | Z/2 (order 2) |
| 2 | `[K14_cork, K14_cork]` | +16 | (Z/2)² (order 4) |
| 3 | three K14_cork | +64 | (Z/2)³ (order 8) |
| k | k components | 4^k | (Z/2)^k |

Cork-of-cork (2-level nesting) reduces to a 2-cork product with
Z/2 × Z/2 acting on the joint H¹.

The multiplicative composition matches disjoint-union cohomology
behavior — Donaldson-type invariants of a disjoint union multiply
in standard 4-mfd gauge theory; the 213-internal `4^k` formula
reproduces this structurally.

## Open frontier

- **Universal multi-cork formula** by structural induction:
  `signedCorkTwistCountMulti m = 4^m.length` for arbitrary
  `m : MultiCork213` (current closes cover k ∈ {0, 1, 2, 3}).
- **Heterogeneous multi-cork**: compositions with distinct cork
  types (e.g., `[K14_cork, K31_cork]`), tracking how cork-type
  variation affects the signed contribution per component.

## Connection

- `theory/math/cohomology/bipartite.md` — parametric V32Betti +
  K-deployment family (cork's chartBase ambient)
- `theory/math/cohomology/k32_higher_cohomology.md` —
  higher-cohomology of K_{3,2}^{(c=2)} (host of the cork-twist
  higher action, currently open)
- `theory/math/geometrization_conjecture.md` — KChartLensAbstract +
  K-deployment enumeration (provides the chartBase ≤ 5 scope)
