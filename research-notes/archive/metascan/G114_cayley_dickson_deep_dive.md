# G114 — CayleyDickson Tier-2 deep dive (629 decls — algebraic-integer tower)

**Date**: 2026-05-22  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Predecessor**: G108-G113 (Real213/Analysis, FluxMVT,
Cohomology, HodgeConjecture, DyadicFSM).  
**Context**: CayleyDickson is the algebraic-integer tower
hosting **6-theorem's algebraic side**: ZOmega^× = 6 = NS·NT.

---

## §1.  Scale + distribution

**629 decls** in 4 sub-areas:

| Sub-area | decls | Role |
|----------|------:|------|
| **Integer**   | **443** | Integer rings: ZI, ZSqrt, ZSqrt2, ZOmega, Hurwitz213 + Domains + Conjugation |
| Tower         | 174 | CD tower abstract structure (Order4Monopoly, AlgebraTower, F2CDTower, UniversalInduction) |
| Misc          |   8 | QuadIdentities, R5Vacuity |
| Lipschitz     |   4 | Lipschitz quaternion specialisations |

**Integer dominates** (70 %) — concrete algebraic-integer rings.
Tower (28 %) — abstract CD doubling machinery.

---

## §2.  The CD tower (structural drop ladder)

```
                  Layer 0: ℤ (Lean Int)
                       ↓ CDDouble
                  Layer 1: ZI = ℤ[i] (Gaussian)
                  R2 (commutativity) holds
                       ↓ CDDouble
                  Layer 2: Lipschitz quaternions
                  R2 drops (commutativity LOST)
                       ↓ CDDouble
                  Layer 3: Octonions / Hurwitz213
                  R3 (associativity) drops
                       ↓ CDDouble  
                  Layer 4: Sedenions
                  R4 (alternative property) drops
                       ↓ CDDouble  
                  Layer 5: Pathions
                  R5 (zero-divisor closure) drops
                       ↓
                  Layer 6+: Trigintaduonion, ...
                  Successive structural collapses
```

Each layer **provably loses a property** of the previous.
This makes CayleyDickson a **systematic negation generator**
(G100 finding: 21/135 falsifiers — 16 % — live here).

### Alternative integer rings (codomain witnesses)

```
ZI         — ℤ[i] (Gaussian)               (D = 1)
ZSqrt2     — ℤ[√-2]                        (D = 2)
ZSqrt D    — ℤ[√-D] parametric             (any D > 0)
ZOmega     — ℤ[ω] Eisenstein               (cross-term norm)
Hurwitz213 — Hurwitz integers              (quaternion lattice)
```

Each is a **`ConjugationCodomain` instance** — concrete witness
that the 3-tier codomain spec (`CommBinaryCodomain` +
`NonVanishingCodomain` + `ConjugationCodomain`) does NOT pin
the codomain to ℂ.  Counterexamples to "R1–R4 force ℂ"
claim.

---

## §3.  Heavy proof clusters

### Cluster I — ZOmega (Eisenstein integer arithmetic)

  · `Integer.ZOmega.normSq_mul`: **697,955 nodes** — heaviest
    single proof in entire E213 corpus (G103).  Eisenstein
    norm multiplicativity.
  · `Integer.ZOmega.normSq_eq_zero_iff`: 233,014 nodes — norm
    vanishing iff zero.
  · `Integer.ZOmega.conj_mul`: 108,265 nodes — conjugation
    distributes over multiplication.
  · `Integer.ZOmega.normSq_nonneg`: 103,505 nodes — norm
    non-negative.

**Total ZOmega cluster: ~1.14 M Expr nodes** — about 60% of
CayleyDickson's heavy proof mass.

These are the **6-theorem's algebraic foundation** (parallel
branch's `d83e9af1` diophantine completeness):
  · `ZOmega_units_exact_six` — `|ZOmega^×| = 6` (양방향
    ∅-axiom).
  · Mapped to `NS · NT = 6` via Eisenstein structure.

### Cluster II — QuadIdentities (Misc)

  · `Misc.QuadIdentities.int_quad_diophantus_sqrt2`: 85,969
  · `Misc.QuadIdentities.int_quad_diophantus_sqrt`: 69,857
  · `Misc.QuadIdentities.int_quad_diophantus`: 52,141

Brahmagupta-Fibonacci / Diophantus identities for integer
quadratic forms.  Foundational for `ZOmega.normSq_mul`.

### Cluster III — Tower CDDouble Lipschitz quaternions

  · `Tower.CDDouble.Lipschitz.conj_mul_anti`: 22,267 nodes
  · `Tower.CDDouble.Lipschitz.normSq_neg`: 17,490 nodes

Quaternion arithmetic at the tower's level 2 (post-doubling
from ZI).

### Cluster IV — ZSqrtProduct + ZI

  · `Integer.ZSqrtProduct.zSqrtProdLens_R4`: 10,983 nodes
  · `Integer.ZSqrtProduct.zSqrtProdLens_R3_fails`: 10,872
    nodes — **falsifier** for R3 at ZSqrt product level
  · `Integer.ZI.neg_mul`: 10,749 nodes

---

## §4.  Byte-identical groups (17 multi-share groups)

### Cross-ring identity templates

**4 byte-identical `*.ext` decls** (461 nodes):
  · `Integer.ZOmega.ext`
  · `Integer.ZI.ZI.ext`
  · `Integer.ZSqrt2.Z2.ext`
  · `Tower.CDDouble.Lipschitz.ext`

**4 byte-identical `*.mk.injEq` decls** (625 nodes) — auto-
generated extensionality (likely artifact, NOT abstraction
candidate).

**3 byte-identical `conj_ne_id` decls** (506 nodes):
  · `Integer.ZOmega.conj_ne_id`
  · `Integer.ZI.conj_ne_id`
  · `Integer.ZSqrt2.Z2.conj_ne_id`

**3 byte-identical `assoc_*_*_*` Lipschitz decls** (301 nodes):
  · `Tower.CDDouble.Lipschitz.assoc_J_I_J`
  · `Tower.CDDouble.Lipschitz.assoc_I_I_J`
  · `Tower.CDDouble.Lipschitz.assoc_I_J_I`

**2 byte-identical `instRing213._cstage1` decls** (491 nodes):
  · `Tower.CDDouble.Lipschitz.instRing213._cstage1`
  · `Integer.ZI.ZI.instRing213._cstage1`

**2 pairs**:
  · `Integer.ZI.ZI.sub_im` ≡ `sub_re` (1227 nodes)
  · `Integer.Hurwitz213.mul._cstage1` ≡ `mul._cstage2` (274)

---

## §5.  Action items from G114

### CD-1 — Ring extensionality `*.ext` template (4 sites)

`ZOmega.ext`, `ZI.ext`, `ZSqrt2.ext`, `Lipschitz.ext` are
byte-identical (461 nodes each).  All four prove
"extensionality at the structure level".

**Effort**: short marathon (~1 hour).  Generic
`Ring213.ext_via_components` template across the 4 rings.

### CD-2 — Conjugation `conj_ne_id` template (3 sites)

`ZOmega.conj_ne_id`, `ZI.conj_ne_id`, `ZSqrt2.conj_ne_id`
byte-identical (506 nodes).  Falsifier: "conjugation is not
identity" at all rings.

**Effort**: short.  Generic
`ConjugationCodomain.conj_ne_id_universal`.

### CD-3 — Lipschitz `assoc_*` template (3 sites)

`assoc_J_I_J`, `assoc_I_I_J`, `assoc_I_J_I` byte-identical
(301 nodes) — three triple-product associativity checks.

**Effort**: short.  May suggest more general `assoc_basis_pattern`.

### CD-4 — `Ring213` instance auto-derivation

`Lipschitz.instRing213._cstage1` ≡ `ZI.ZI.instRing213._cstage1`
(491 nodes) — Lean-generated typeclass infrastructure.  Likely
already typeclass-factored.  Mostly artifact.

### CD-5 — ZSqrtProduct falsifier R3_fails

`zSqrtProdLens_R3_fails` is a **named falsifier** (G100
falsifier catalog member?  not directly in G100's 135 but
similar pattern).  ZSqrt product fails the R3 (associativity)
axiom — concrete counterexample.

Effort: investigation if more `*_R*_fails` exist (catalog
candidate).

---

## §6.  Research questions

### CD-RES1 — Codomain witnessing — full count

How many distinct `ConjugationCodomain` instances exist?
Currently: ZI, ZSqrt D (parametric ∀D), ZOmega, Hurwitz,
Lipschitz, CDDouble derived.  Each is a witness counterexample
to "R1-R4 force ℂ".

**Question**: is there a `Codomain_Catalog` listing all known
instances?  Worth a catalog file.

**Effort**: 1 hour (catalog).

### CD-RES2 — Tower fixed-point structure

`Tower/TowerFixedPoint.lean` claims fixed-point structure for
the CD tower.  **Question**: what does "fixed point" mean
here?  Is it a tower-level result (some level stays the same
under doubling)?

**Effort**: 1 session investigation.

### CD-RES3 — Order4 Monopoly

`Levels/CayleyOrder4Monopoly.lean` +
`SedenionOrder4Monopoly.lean` +
`Tower/Order4Monopoly_L{4,5,6}T.lean` — 5 files claim "Order4
Monopoly".

**Question**: what theorem is this?  Likely "no order-4
substructure beyond CDDouble".  Investigation needed.

**Effort**: 1-2 sessions.

### CD-RES4 — ZOmega units → atomicity bridge

`ZOmegaUnits.lean` proves `|ZOmega^×| = 6 = NS · NT`.  This is
the 6-theorem's algebraic anchor.  **Question**: is the bridge
NS·NT → ZOmega units formalised as a direct theorem?  Or
indirect via the 6-theorem master?

**Effort**: 1 session checking the bridge tightness.

### CD-RES5 — F2CDTower (over ℤ/2)

`Tower/F2CDTower.lean` — CD tower over F_2 (= ℤ/2 = Bool).
**Question**: how does CD doubling specialise to F_2?  Does
it produce the same property-loss ladder?

**Effort**: 1-2 sessions.

---

## §7.  Significance for the meta-scan tree

### What G114 confirms

  · **6-theorem algebraic foundation**: ZOmega cluster at
    1.14M Expr nodes is the algebraic side of the 6-theorem.
    Parallel branch's diophantine completeness work
    (`d83e9af1`) lives here.
  · **Systematic negation factory**: CayleyDickson contributes
    16 % of all falsifiers (G100).  Each layer drops a
    property → each property loss is a decide-witnessed
    falsifier.
  · **Multiple codomain witnesses**: ZI, ZSqrt D, ZOmega,
    Hurwitz, Lipschitz — all `ConjugationCodomain` instances.
    Multiple distinct codomains satisfying the 3-tier spec
    (counterexamples to "R1-R4 force ℂ").

### What G114 newly surfaces

  · **CD-1 ring extensionality template** (4 sites byte-identical)
  · **CD-2 conjugation non-identity template** (3 sites)
  · **CD-3 Lipschitz associativity template** (3 sites)
  · **Order4 Monopoly** (CD-RES3) as an unexplored claim across
    5 files

### What's still unexplored after G114

  · **Lib.Physics subtrees** (Atomic, Hadron, Cosmology,
    Symmetry, etc.) — 875 decls.
  · **PatternCatalog** (943 decls) — Tier-1 patterns?
  · **Doctrinal capstones**: Bishop comparison (G115),
    Pattern #10-#17 → LESSONS_LEARNED.

---

## §8.  Updated executor priority (G108-G114 consolidated)

1. **L1 LeibnizAlgLift marathon** (biggest single mass —
   6-layer overdetermined, ~6.6 M chars)
2. **G113 FSM-1 pellFSMmod parametric** (457 sites, broadest)
3. **G111 COH-1+COH-2+COH-3 batch** (~90K nodes)
4. **G114 CD-1+CD-2+CD-3 small template batch** (~2K nodes,
   short)
5. **G112 HC-1 capstone-template investigation**
6. **G110 FLUX-1 forward/backward**
7. **G113 FSM-3 pisano predictor**
8. **G108 REAL-1 + REAL-2 Cut iff**
9. **G114 CD-RES1 Codomain catalog** (~1h)
10. **G108 CutSumOne C template**
11. **G113 FSM-2 fibFSMmod** (145 sites)
12. **G112 HC-2 per-surface HodgeIndex**
13. **G115+ Bishop / Lib.Physics / PatternCatalog deep dives**

---

## §9.  Artifacts

  · This document: `research-notes/G114_cayley_dickson_deep_dive.md`
  · Source: G102 callgraph + G103 shape + Lean source inspection.

Next candidates:
  · **G115 Lib.Physics deep dive** (Atomic / Hadron / Cosmology
    / Symmetry / ... 875 decls)
  · **G116 PatternCatalog** (943 decls — Tier-1 pattern
    framework)
  · **G117 Bishop comparison** (doctrinal, REAL-RES6)

Or doctrinal:
  · **LESSONS_LEARNED.md formal Pattern #10-#17 additions**
  · **TH-2 Raw-derivation three levels standalone doc** (G107
    §10.3)
  · **CDI catalog** (G109 §6) — already done as
    `catalogs/cross-domain-identifications.md`.
