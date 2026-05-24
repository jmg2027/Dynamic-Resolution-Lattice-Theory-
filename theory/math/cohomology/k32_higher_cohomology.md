# K_{3,2}^{(c=2)} higher cohomology

Math-side companion to `bipartite.md`: the cohomology of the
filled K_{3,2}^{(c=2)} bipartite multigraph at the 2/3/4-skeleton
truncations, with Steenrod-algebra structure, the cup_i ladder,
and the Steenrod-Whitehead bridge `cup_1(ω, ω) = δ²(ω)`.

Pure cohomology results.  Physical application to α_em residual
lives separately at `physics/alpha_em/precision_derivation.md`
C1 Step 6.

## The complex

`K_{3,2}^{(c=2)}` is the complete bipartite multigraph with NS = 3
S-vertices, NT = 2 T-vertices, c = 2 edge multiplicity per (S, T)
pair.  Vertex set has 5 elements; edge set has 12.  Simple 4-cycles:
3 (choose 2 of NS S-vertices, both T-vertices, c = 1 per pair).

Cell-complex truncations:

  | Level | C⁰ | C¹ | C² | C³ | C⁴ |
  |-------|----|----|----|----|----|
  | 1-skeleton | 5 | 12 | 0 | 0 | 0 |
  | 2-skeleton (full simple-cycle filling) | 5 | 12 | 3 | 0 | 0 |
  | 3-skeleton (one 3-cell σ³) | 5 | 12 | 3 | 1 | 0 |
  | 4-skeleton (σ³ + σ⁴) | 5 | 12 | 3 | 1 | 1 |

## Face dependence (the structural origin of b_2 = 1)

The 3 simple 4-cycle face boundaries are LINEARLY DEPENDENT over
F_2:

      Face_0 ⊕ Face_1 ⊕ Face_2 = 0

for every edge cochain σ ∈ C¹.  Proved by exhaustive
case-analysis in `Filled3CellCohomology.face_dependence`.

Consequence: `rank δ¹ = 2`, NOT 3.  At full simple-cycle filling
(k = 3 faces attached):

  · `dim ker δ¹ = 12 − 2 = 10`
  · `rank δ⁰ = 4` (5 vertices, 1 connected component)
  · `dim H¹ = 10 − 4 = 6` (matches `b_1 = 8 − k = 5` naively
    expected, BUT refined to 6 by face dependence)
  · `dim H² = 3 − 2 = 1` (the b_2 = 1 class)

The non-trivial 2-cocycle representative is the all-ones
face-vector:

      ω = (1, 1, 1) ∈ C²

## ω as the unique Sym(3)-invariant 2-cocycle

The Sym(3) symmetry permuting the 3 S-vertices acts on the 3 face
indices via the rule "S-vertex transposition (i ↔ j) ↦ face
permutation determined by which S-vertex is excluded".  Explicit
generators:

  · `S01 swap`: Face 0 fixed, Face 1 ↔ Face 2
  · `S12 swap`: Face 2 fixed, Face 0 ↔ Face 1
  · `S02 swap`: Face 1 fixed, Face 0 ↔ Face 2

These satisfy the Sym(3) Coxeter relation; `ω = (1, 1, 1)` is
invariant under all three (constant cochain × any permutation =
same cochain).  Per `phase2_omega_invariant_2cocycle`, ω is the
UNIQUE non-trivial Sym(3)-invariant 2-cocycle (since dim H² = 1
and the class is fixed).

The Sym(3) irrep decomposition at H¹ + H² is

      3·trivial ⊕ 3·standard

(extending the H¹-only `2·trivial ⊕ 3·standard`; the third trivial
irrep is ω).

## Truncation-collapse

Each `(k+1)`-skeleton extension trivialises the previous H^k.
Specifically, attaching the 3-cell σ³ with boundary `[face_0,
face_1, face_2]`:

  · `δ²(ω)(σ³) = ω(0) ⊕ ω(1) ⊕ ω(2) = 1 ⊕ 1 ⊕ 1 = 1 ≠ 0`
  · Hence ω ∉ ker δ², so [ω] = 0 in H²(3-skeleton).

Attaching the 4-cell σ⁴ with boundary `[σ³]`:

  · `δ³(c)(σ⁴) = c(σ³)`
  · ker δ³ = {c : c(σ³) = false} = {0} (since C³ is 1-dim)
  · H³ = ker δ³ / im δ² = 0 at the 4-skeleton

The pattern continues: each (k+1)-skeleton level extension
trivialises the H^k class generated at the previous level.  This
is a universal property of finite cell-complex truncation chains
where each level adds a single cell attaching all of the previous
top-level cocycles.

## Cup-product graduation: cup_i for i = 0, 1, 2

The cup-product family `cup_i : C^k × C^l → C^(k+l-i)` is
parameterised by the degree reduction `i`.  Specific instances
formalised:

  · `cup_0 = cup` (standard Alexander-Whitney; degree adds)
  · `cup_1` at base arities `(5, 1, 1)`, `(5, 1, 2)` (pointwise
    diagonal forms)
  · `face_cup_2 : C² × C² → C²` on K_{3,2}^{(c=2)} face cochains
    (pointwise Bool conjunction; `ω ⌣_2 ω = ω` idempotent)
  · `face_cup_1 : C² × C² → C³` (rotational interlocking face-pair
    sum)

The cup-i ladder at ω self-pairing:

  · ω ⌣_0 ω ∈ C⁴ (off-complex in 2-skeleton)
  · ω ⌣_1 ω ∈ C³ (lands at 3-skeleton C³)
  · ω ⌣_2 ω ∈ C² (back to face cochain, = ω idempotent)

The CUP-AXIOM-INTERNAL output degree for `cup_(k-1)(c, c)` where
`c ∈ C^k` is `k + l - i = 2k - (k - 1) = k + 1` — exactly one more
than the input cohomology degree.

## The Steenrod-Whitehead bridge: cup_1(ω, ω) = δ²(ω)

The marathon's structurally most striking identity:

      face_cup_1(ω, ω) = δ²(ω)

as 3-cochains on σ³.  Both sides evaluate:

  · LHS: ω(face_0) · ω(face_2) ⊕ ω(face_1) · ω(face_0)
         ⊕ ω(face_2) · ω(face_1) = 1 ⊕ 1 ⊕ 1 = 1
  · RHS: ω(face_0) ⊕ ω(face_1) ⊕ ω(face_2) = 1 ⊕ 1 ⊕ 1 = 1

Hence `Sq¹(ω) = δ²(ω)` at the H² ω class.

Structural reading: the Steenrod cup_1 self-pairing of a
cohomology class equals its coboundary at the next-level
attaching.  cup_(k-1) and δ^k are STRUCTURALLY indistinguishable
when applied to H^k classes.  This is the cohomology-algebra
fingerprint of Steenrod squares acting on the cup-i ladder.

## L²-pairing trace as expansion of square

For c : Fin 3 → Bool, the bilinear self-tensor trace

      bilinearSelfTrace(c) := Σ_{i, j ∈ Fin 3} boolToNat(c_i) · boolToNat(c_j)

equals the squared L¹-norm of the integer lift:

      bilinearSelfTrace(c) = (Σ_i boolToNat(c_i))² = faceCochainL1Sq(c)

Proved as a UNIVERSAL Nat identity over all 8 inhabitants of
`Fin 3 → Bool` by case-analysis (`SelfPairingTrace.bilinear_self_trace_eq_L1_sq`).
This is the expansion-of-square identity

      (x_0 + x_1 + x_2)² = Σ_{i, j} x_i · x_j

specialised to Bool-valued face cochains.

For ω = (1, 1, 1): trace(ω) = 1 + 1 + 1 = 3 = NS;
trace²(ω) = 9 = NS² = ‖ω‖².

## Steenrod squares Sq^i at H² ω

  · `Sq⁰(ω) := ω ⌣_2 ω = ω` (cup_2 idempotent, lands C²)
  · `Sq¹(ω) := ω ⌣_1 ω = δ²(ω) = (true)` on C³
  · `Sq²(ω) := ω ⌣_0 ω` lands in C⁴ = ∅ at 3-skeleton truncation
    (vacuously zero)

Max non-trivial Sq^i at H² ω: i = 1.  This is the Steenrod ladder
depth `k − 1 = 2 − 1 = 1` at H^k = H².

## Adem and Cartan at truncation

At the K_{3,2}^{(c=2)} 3-skeleton (C^k empty for k ≥ 4), every
Adem relation Sq^a·Sq^b becomes vacuously satisfied: both sides
land in empty C^(d + a + b) for d-degree input + a + b > 3.

Specific Adem instances proved at truncation:

  · `Sq¹·Sq¹ = 0` at C⁴ (vacuous)
  · `Sq²·Sq² = Sq³·Sq¹` at C⁶ (vacuous)
  · `Sq³·Sq² = Sq⁴·Sq¹ + Sq⁵` at C⁷ (vacuous)
  · Universal: any two truncated cochains at any k ≥ 4 are
    pointwise equal (`AdemUniversal.adem_vacuous_at_truncation`)

The Cartan formula `Sq¹(α ⌣_0 β) = Σ Sq^i(α) ⌣_0 Sq^j(β)`
similarly vanishes vacuously at C⁵ truncation
(`CartanAtTruncation.cartan_at_truncation_eq_pointwise`).

Non-vacuous Adem and Cartan require extending the complex to
higher skeletons where the operations land in non-trivial cochain
spaces.

## Max cohomology degree = top dim

Universal property of finite cell-complex truncation:

      For complex of top dim n, max non-trivial H^k = n.

At each truncation level, the maximum cohomology degree is exactly
the top cochain dimension.  Higher H^k vanish identically.
Formalised in `MaxAlphaPowerBound.max_alpha_power_at_*skeleton`
and `Filled4CellExtension.H3_dim_at_4_skeleton`.

## 5-skeleton extension (Massey landing-space audit)

`Filled5CellExtension.lean` adds a single 5-cell σ⁵ with attaching
boundary `[σ⁴]`, extending the pyramid tower σ³ → σ⁴ → σ⁵.
Establishes:

  · `δ⁴(c)(σ⁵) := c(σ⁴)` (pull-back of 4-cochain to σ⁵)
  · `H⁴ = 0` at 5-skeleton (ker δ⁴ = {0}; im δ³ = C⁴)
  · `H⁵ = 0` at 5-skeleton (no δ⁵; im δ⁴ = C⁵ since both
    Bool-valued 5-cochains are δ⁴-images)

★ **Massey-triple landing-space audit**: ⟨ω, ω, ω⟩ for ω ∈ H²
would land in `H^(2 + 2 + 2 - 1) = H⁵`.  At the 5-skeleton
extension, `H⁵ = 0` makes the Massey class VACUOUSLY trivial
regardless of cobounding-chain choice.

`Filled5CellMultiExtension.lean` (Phase 9) shipped a multi-cell
5-skeleton with `H⁵ ≅ ℤ/2 ≠ 0`, providing a non-vacuous landing
substrate for Massey.

`MasseyTripleOmega.lean` (Phase 12) computes Massey ⟨ω, ω, ω⟩
explicitly under the outermost-faces AW cup extension and finds
the class is ZERO at the chain level — the Massey representative
is the all-false 5-cochain = `δ⁴_multi(false-4cochain)`.

**Structural obstruction**: ω = (1, 1, 1) is the constant-true
face cochain.  Any face-pair evaluation gives `true`, so each
summand of `b ⌣ ω + ω ⌣ b` produces `(true, true)`; the xor
collapses to `(false, false)`.

So even with the non-vacuous H⁵ substrate, ⟨ω, ω, ω⟩ is
intrinsically trivial.  Non-vacuous Massey at K_{3,2}^{(c=2)}
requires either:

  · A different cohomology class than ω (but H² = ℤ/2 ⟨ω⟩ — ω
    is the unique non-zero H² class).
  · A different Massey triple shape (e.g., ⟨a, b, c⟩ at H¹
    classes landing in H²).
  · An asymmetric cup extension breaking the diagonal-image
    structure of `δ⁴_multi`.

## Sq² at the 4-skeleton — chain-level explicit

`Sq2At4Cell.lean` ships an explicit chain-level Sq² via a
defensible outermost-faces AW lift of cup_0 at the 4-cell:

      (α ⌣_0 β)(σ⁴) := α(face_0) ∧ β(face_2).

For ω = (1, 1, 1): Sq²(ω) = (true) at the chain level —
non-trivial as a cochain.  But Sq²(ω) = δ³(all-true 3-cochain),
so [Sq²(ω)] = 0 in `H⁴ = 0` at the 4-skeleton.

Steenrod ladder at ω now complete across i ∈ {0, 1, 2} at the
4-skeleton with explicit chain-level values:

  · Sq⁰(ω) = ω at C² (H² non-trivial)
  · Sq¹(ω) = δ²(ω) at C³ (H³ trivial at 3-skeleton)
  · Sq²(ω) = true at C⁴ via AW lift (H⁴ trivial at 4-skeleton)

Max non-trivial Sq^i CLASS at ω at the 4-skeleton: `i = 0`.

## Multi-cell 5-skeleton — non-vacuous H⁵ substrate

`Filled5CellMultiExtension.lean` breaks the pyramid collapse
from `Filled5CellExtension` with two 5-cells σ⁵_a, σ⁵_b both
with boundary [σ⁴]:

  · `C⁵ = Fin 2 → Bool`
  · `δ⁴_multi(c)(σ⁵_a) = δ⁴_multi(c)(σ⁵_b) = c(σ⁴)` (both
    cells receive the same value — image lies on the diagonal)
  · The off-diagonal cochain `(false, true)` is NOT in
    `im δ⁴_multi`: it has different values at the two 5-cells.
  · `H⁵ ≅ ℤ/2` — non-trivial cohomology.

This is the Massey-triple substrate: with `H⁵ ≠ 0`, Massey
`⟨ω, ω, ω⟩` can host a non-vacuous class.  Remaining content
for full Massey closure: explicit cobounding-chain construction
solving `ω ⌣ ω = δ b_i`, then `[b_1 ⌣ ω + ω ⌣ b_2]` mod
indeterminacy ideal `ω · H¹ + H¹ · ω`.

## Open frontier (pure cohomology)

  · **General Steenrod cup_i for arbitrary i ≥ 2** with the full
    Alexander-Whitney face-pair formula on simplicial cochain
    complexes (requires Adem-Wu basis formalisation).
  · **Non-vacuous Adem relations** at higher-skeleton extensions
    (extend complex so target degrees host non-trivial classes).
  · **Cartan formula non-vacuous** — same higher-skeleton
    requirement.
  · **Non-vacuous Massey ⟨ω, ω, ω⟩** — `Filled5CellMultiExtension`
    provides the non-vacuous H⁵ substrate.  Remaining content:
    explicit cobounding-chain construction + Massey-class
    computation modulo indeterminacy.
  · **General Steenrod algebra in 213-native Lean**: cup_i
    operations + Adem + Cartan + Steenrod squares as a unified
    typeclass framework.

## Cross-references

  · `theory/math/cohomology/bipartite.md` — parent overview chapter
    (b_0, b_1 of K_{3,2}^{(c=2)})
  · `theory/math/cohomology/cup.md` — standard cup product
  · `theory/math/cohomology/cup_ladder_graduation.md` — physics
    application bridge (α_em residual via cup-ladder graduation)
  · `lean/E213/Lib/Math/Cohomology/Bipartite/` — Lean source files
    (Filled3CellCohomology, Filled3CellExtension, Filled4CellExtension,
    Filled5CellExtension, FaceCupHigher, FaceCup1At3Cell,
    SelfPairingTrace, SteenrodSquaresAtOmega, CartanAtTruncation,
    AdemUniversal)

## Status

Pure cohomology results at K_{3,2}^{(c=2)} 2/3/4-skeleton truncations
formalised in Lean (∅-axiom PURE).  Steenrod-algebra structure
at truncation boundary fully closed.  General Steenrod algebra
(cup_i for arbitrary i, Adem-Wu basis, Cartan non-vacuous)
remains open continuation work — independent of any physics
application.
