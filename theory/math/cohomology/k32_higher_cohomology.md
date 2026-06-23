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

The structurally most striking identity:

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

## Adem at truncation (single instance)

At the K_{3,2}^{(c=2)} 3-skeleton (`C⁴` empty), the first Adem
relation is realised vacuously: `Sq¹·Sq¹ = 0` lands in
`C⁴ = ∅`, so both sides are pointwise equal
(`SteenrodSquaresAtOmega.Sq_1_squared_eq_zero`, over
`Sq_1_squared_target := Fin C4_dim → Bool` with `C4_dim = 0`).

A *universal* (∀ a,b,k) Adem/Cartan ladder — the higher relations
`Sq²·Sq² = Sq³·Sq¹`, the Cartan formula
`Sq¹(α ⌣₀ β) = Σ Sqⁱ(α) ⌣₀ Sqʲ(β)`, and their non-vacuous forms
at higher skeletons — is **not formalised** (it would need the
complex extended so the target degrees host non-trivial classes,
plus the Adem–Wu basis).  See "Open frontier" below.

## Max cohomology degree = top dim

Universal property of finite cell-complex truncation:

      For complex of top dim n, max non-trivial H^k = n.

At each truncation level, the maximum cohomology degree is exactly
the top cochain dimension.  Higher H^k vanish identically.
Formalised in `MaxAlphaPowerBound.max_alpha_power_at_*skeleton`
and `Filled4CellExtension.H3_dim_at_4_skeleton`.

## Open frontier (unformalized)

Live agenda + entry points: `research-notes/frontiers/cohomology_higher_structure.md`.

The directions below are **not** in Lean — no `MasseyTripleH1Witness`,
`MasseyTripleOmega`, `Filled5CellExtension`,
`Filled5CellMultiExtension`, `Sq2At4Cell`, `AdemUniversal`,
`CartanAtTruncation`, or any `V33*` / `K_{3,3}` module exists in the
repository.  They are recorded here as the next continuation work, not
as proved results:

  · **Higher Steenrod cup_i for arbitrary i ≥ 2** with the full
    Alexander-Whitney face-pair formula (needs the Adem–Wu basis).
  · **Universal Adem / non-vacuous Cartan** at higher-skeleton
    extensions (extend the complex so target degrees host non-trivial
    classes).  Only the single vacuous instance `Sq¹·Sq¹ = 0` is
    formalised (above).
  · **Sq² at the 4-skeleton** as an explicit chain-level operation
    (currently `Sq²(ω)` is only the vacuous `C⁴ = ∅` reading inside
    `SteenrodSquaresAtOmega`).
  · **5-skeleton extension** and a non-vacuous `H⁵` substrate.
  · **Massey products** — both the `H¹`-triple `⟨h1,h3,h4⟩` via an
    opposite-edge cup and the `H²`-triple `⟨ω,ω,ω⟩` landing-space
    audit — together with the topological model
    `K_{3,2}^{(c=2)} ≃ S² ∨ (∨₆ S¹)`.
  · **K_{3,3}^{(c=2)} secondary cohomology** (`b₂ = 5`,
    multi-dimensional Massey output) and its `c`-counter behaviour.
  · **General 213-native Steenrod algebra**: cup_i + Adem + Cartan +
    Steenrod squares as a unified framework.

## Cross-references

  · `theory/math/cohomology/bipartite.md` — parent overview chapter
    (b_0, b_1 of K_{3,2}^{(c=2)})
  · `theory/math/cohomology/cup.md` — standard cup product
  · `theory/math/cohomology/cup_ladder_graduation.md` — physics
    application bridge (α_em residual via cup-ladder graduation)
  · `lean/E213/Lib/Math/Cohomology/Bipartite/` — Lean source files
    (Filled3CellCohomology, Filled3CellExtension, Filled4CellExtension,
    FaceCupHigher, FaceCup1At3Cell, SelfPairingTrace,
    SteenrodSquaresAtOmega)

## Status

Pure cohomology results at K_{3,2}^{(c=2)} 2/3/4-skeleton truncations
formalised in Lean (∅-axiom PURE): face dependence (`b_1 = 6`,
`b_2 = 1`), ω as the Sym(3)-invariant 2-cocycle, the cup_1/cup_2 face
ladder, the Steenrod–Whitehead bridge `cup_1(ω,ω) = δ²(ω)`, the
L²-trace square identity, and the `Sq⁰/Sq¹` ladder at ω with the single
vacuous `Sq¹·Sq¹ = 0`.  Everything above under "Open frontier" —
universal Adem/Cartan, explicit Sq², 5-skeletons, Massey products, and
K_{3,3} — is **unformalized continuation work**.
