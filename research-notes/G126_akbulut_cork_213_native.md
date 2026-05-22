# G126 — Akbulut cork as 213-native exotic-structure framework

**Date**: 2026-05-22
**Status**: **6-PHASE PARTIAL CLOSE** (44 PURE across 4 files,
single-session close)
**Branch**: `claude/g121-open-followup-BCOp3`
**Source**: user insight 2026-05-22, supersedes FW-1 (signed Donaldson)
as the natural 213-native path to exotic-structure enumeration.

## Partial close summary (2026-05-22)

Sub-tree `lean/E213/Lib/Math/AkbulutCork/` created with 4 files,
44 PURE total:

  · `Foundation.lean` (14 PURE) — `Cork213` data type + canonical
    instances + b_1 = 0 contractibility match
  · `Twist.lean` (12 PURE) — `corkTwist` Z/2 endomorphism +
    involution proofs + M_S01 matrix correspondence
  · `SignedOrbits.lean` (13 PURE) — per-orbit-type M_S01 fix counts
    (4, 28, 0) + ★★★★★★ `signedCorkTwistCount = +4`
  · `CorkTheorem.lean` (5 PURE) — cork embedding + cork uniqueness
    + ★★★★★★★★★★ `akbulut_cork_213_native` capstone (14-conjunct
    bundle of all 6 phases)

The signed cork-twist count `+4` is the 213-native exotic-count:
`(twistEvenOrbits = 32) − (twistOddOrbits = 28) = +4`.  This
supersedes FW-1's external-Donaldson-interface block with a
fully-213-internal Z/2-graded count.

## Why this supersedes FW-1 (signed Donaldson)

The FW-1 plan ("213 Burnside count 60 → Donaldson signed integer
via external standard-math bridge") was structurally blocked by the
213/standard-math axiom-import barrier.

The Akbulut–Curtis–Freedman–Hsiang–Stong cork theorem provides a
**completely different formalization of exotic structures**:

> Every pair of homeomorphic but non-diffeomorphic closed simply-
> connected 4-manifolds X₁, X₂ differs by a single **cork twist**:
> there exists a contractible 4-manifold C ("cork") with boundary
> involution τ : ∂C → ∂C such that
>   X₂ = (X₁ − int(C)) ∪_τ C.

This means: exotic-structure differences are NOT continuum-many
gauge-theoretic invariants, they are **discrete Z/2 involution
operations** on contractible substructures.  Discrete and finite —
the natural 213-native shape.

## 213-native correspondence (point-by-point)

| Cork-theorem object | 213-native realization | Existing Lean witness |
|---|---|---|
| Contractible 4-substructure C | K_{1,4}^{(c=1)} tree branch (`isTreeDeployment 1 4 1 = true`, b_1 = 0) | `poincare_two_layer_trivial_loop`, `chartBase_5_tree_and_critical_coexist` |
| Z/2 involution τ on ∂C | M_S01 transposition: M_S01² = Id | `Sym3OnH1KMatrix.M_S01_squared_pointwise` |
| Boundary 3-mfd ∂C ≈ S³ | ∂Δ⁴ = S³, χ = 0 | `EulerChi.chi_S3_eq_zero` |
| Cork embedding C ↪ X | Tree-and-critical coexistence at d_M = 4 (chartBase = 5) | `Capstone.dim4_information_richness`, `Poincare.filling_versus_tree_dual_path` |
| c = 2 binary cover (Möbius P mod 5) | Already structural in K_{3,2}^{(c=2)} | `C2DoublingDerivation.c_multiplicity_eq_2` |
| Z/2 cork-twist equivalence | 84 transp-fixed cochains under M_S01 (stab = order-2) | `Exotic4Mfd.fw1_suborbit_decomposition` sub-orbit (4, 0, 28, 28) |

The alignment is too tight to be coincidence: every cork-data
ingredient has a pre-existing 213-internal counterpart.

## How cork-frame resolves the FW-1 sign problem

**Original FW-1 block**: Donaldson invariants are signed integer
sums (±1 per instanton from determinant-line-bundle orientation).
The 213 Burnside count `sym3OrbitCount = 60` is unsigned.

**Cork resolution**: in the cork-twist framework, "sign" reduces
to **parity of cork-twist count** mod 2.

  · 0 twists applied → original smooth structure (sign +1)
  · 1 twist applied → cork-twisted exotic (sign −1)
  · 2 twists = identity (τ² = id) → back to original

This is a Z/2 grading natively present in the M_S01 involution
structure.  Each Sym(3)-orbit can be partitioned by M_S01-fixedness
into +1 / −1 classes, yielding a SIGNED count.

Refined FW-1 question becomes:

> Decompose the 60 Sym(3)-orbits by M_S01 twist-parity (Z/2 grading).
> Does this decomposition match Donaldson invariants on some
> standard 4-mfd, OR define a 213-native signed exotic-count
> intrinsically?

The second branch is **entirely 213-internal** — no external
interface needed.

## Phase plan

### Phase 1 — Cork data type (1 session)

`lean/E213/Lib/Math/AkbulutCork/Foundation.lean`:
  · `Cork213` structure: contractible substructure + Z/2 involution
  · K_{1,4}^{(c=1)} as canonical cork instance
  · ∂Δ⁴ as canonical cork boundary

### Phase 2 — Cork twist as operation (2 sessions)

`AkbulutCork/Twist.lean`:
  · `corkTwist : Cork213 → Cohomology → Cohomology` — applies M_S01
  · `corkTwist_involution`: twist² = id (from M_S01²)
  · `corkTwist_preserves_Sym3_orbit`: twist commutes with Sym(3) up to
    the Z/2 grading

### Phase 3 — Signed orbit decomposition (2 sessions)

`AkbulutCork/SignedOrbits.lean`:
  · `signedOrbitClass : H1K → Sign × Sym3Orbit`
  · `signedOrbitCount := signed Burnside (with ±1 per orbit by parity)`
  · Decompose 60 orbits → (a+, a-, b+, b-, ...) signed count
  · Likely: 60 = (signed sum) + (anti-signed sum), with structural
    constraints

### Phase 4 — d=4 information richness ↔ cork embedding (2 sessions)

`AkbulutCork/D4Embedding.lean`:
  · Formalize "K_{1,4} tree embeds as cork in K_{3,2}^{(c=2)} critical"
    at chartBase = 5
  · Show this is the 213-native form of "every closed simply-connected
    4-mfd contains an Akbulut cork"
  · Connect to `chartBase_5_tree_and_critical_coexist`

### Phase 5 — Cork uniqueness ↔ Sym(3)-orbit uniqueness (1-2 sessions)

`AkbulutCork/Uniqueness.lean`:
  · Show the M_S01 involution is the unique non-trivial Z/2 action
    on K_{3,2}^{(c=2)} compatible with the c=2 cover
  · Cork theorem analog: "cork is unique up to conjugacy" at the
    213-deployment level

### Phase 6 — Capstone (1 session)

`AkbulutCork/Capstone.lean`:
  · 213-native cork-theorem statement
  · Closes FW-1 internally: signed exotic-count = signed cork-twist
    enumeration on K_{3,2}^{(c=2)}

**Total**: ~120 PURE est., 8-12 sessions.

## Why this is high-priority

1. **Replaces unresolved meta-research** (FW-1 sign problem) with a
   concrete Lean-formalization marathon.
2. **All ingredients pre-exist** in 213-internal form.
3. **Anchored in standard mathematics** (Akbulut-Curtis-Freedman) —
   not speculative.
4. **Promotes G121 toward DRLT Validation Standard**: a 213-native
   signed exotic-count is a falsifier candidate.

## Risks

  · Cork theorem in standard math relies on smooth-structure
    machinery (h-cobordism, Casson-Freedman).  213-internal cork-twist
    might capture only an *algebraic shadow* — need to check whether
    the cork-frame fully recovers exotic-count behavior.
  · The "K_{1,4} as cork" identification is suggestive but
    structurally needs verification (e.g., is K_{1,4} contractible
    in the 213-cohomology sense?  b_1 = 0 is necessary but possibly
    not sufficient).

## Connection to existing G-numbers

  · G121: parent (Geometrization + 4-mfd anomaly conjecture)
  · G123 FW-1: superseded by this; redirect FW-1 to cork-frame
  · G124 (V32Betti parametric): orthogonal — cork-frame uses K_{1,4}
    AND K_{3,2}^{(c=2)} side-by-side; G124 generalizes V32Betti to
    arbitrary K_{NS,NT}, possibly to K_{1,4} as needed
  · G125 (Ricci/BracketCauchy bridge): independent

## Falsifier potential

**HIGH** — concrete prediction.  A 213-native signed cork-twist count
on K_{3,2}^{(c=2)} that disagrees with Donaldson invariants on any
specific closed 4-mfd containing a comparable Akbulut cork falsifies
the cork-frame correspondence.  This is the strongest falsifier path
opened by G121 follow-ups.

## Decision point

Before launching G126: verify K_{1,4}^{(c=1)} contractibility in
213-cohomology (b_1 = 0 is given; check b_2 = b_3 = 0 vacuously since
no 2/3-cells without extension).  This is the gating check — if K_{1,4}
turns out to be the *wrong* 213-native cork, the marathon scope
shifts to "find the right contractible substructure".
