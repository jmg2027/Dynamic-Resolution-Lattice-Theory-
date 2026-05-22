# G111 — Cohomology Tier-2 deep dive (1,216 decls)

**Date**: 2026-05-22  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Predecessor**: G108 (Real213/Analysis), G110 (FluxMVT), G109
(CDI scan).  
**Companion**: G94 §1/§7 (CutSumOne + LeibnizAlgLift surfaces),
G106 (L1 6-layer agreement).

Continuation of the Tier-2 subtree systematic coverage.  After
G108 (Real213/Analysis) and G110 (FluxMVT), this is the next
largest unanalysed area.

---

## §1.  Scale + decl distribution

**1,216 decls in call graph**, partitioned across 11 sub-areas
+ 1 capstone:

| Sub-area | decls | Role |
|----------|------:|------|
| Surfaces           | 565 | CW models of Kähler manifolds (T², T²×T², ℙ², ℙ¹×ℙ¹, T²ⁿ) |
| Examples           | 156 | K5, SimplexBasis, EulerClosed, BettiKernel, DiamondAudit, etc. |
| Cochain            |  73 | Carrier type + V5/V5_1/V5_2 decomposition |
| Bridge             |  71 | Interfaces (AlphaEM, ClosureExtension, CutLog, etc.) |
| Universal          |  68 | Hodge universal pattern theorems (Prop52/53) |
| CupAW              |  62 | Alexander-Whitney cup + L1 LeibnizAlgLift family |
| Bipartite          |  57 | K_{NS,NT}^{(c)} bipartite cohomology |
| Hodge              |  54 | Hodge structure (Star, Prop52/53, Involution) |
| Delta              |  51 | Boundary operator δ |
| Fractal            |  31 | K_25 fractal levels (G109 CDI-8) |
| Cup                |  27 | Lex-projection cup (G85 rename) + universal Leibniz |
| Capstone           |   1 | top-level capstone |

**Marker touches**:

| Marker | hits | % |
|--------|-----:|--:|
| `binom`    | **313** | 25.7 |
| `Cochain`  | 132 | 10.9 |
| `delta`    | 81  | 6.7 |
| `Bool.xor` | 71  | 5.8 |
| `cupAW`    | 38  | 3.1 |
| `kSubset`  | 38  | 3.1 |
| `subsetIdx`| 27  | 2.2 |
| `hodgeStar`| 25  | 2.1 |
| `cup` (lex)| 24  | 2.0 |
| **Raw atom** | **0** | **0** |
| **Lens.view** | **0** | **0** |

**Critical observation**: **0 Raw, 0 Lens.view** direct touches
across 1,216 Cohomology decls.  Operates entirely on Cochain +
binom + Bool.xor — the most encapsulated Tier-2 subtree.
`Cochain n k := Fin (binom n k) → Bool` is the ground; all
operations live on top.

---

## §2.  Architecture — 4-layer pyramid + Bridge

```
                   Layer A: Cochain carrier
                   Cochain n k := Fin (binom n k) → Bool
                   add = pointwise XOR
                                ↓
                   Layer B: Operations
            ┌───────────┬───────────┬───────────┐
            ▼           ▼           ▼           ▼
          Delta      CupAW         Cup        Hodge
          (∂ bnd)   (AW form)  (lex-proj)   (* dual)
                                ↓
                   Layer C: Examples (concrete witnesses)
            K5  SimplexBasis  BettiKernel  EulerClosed  ...
                                ↓
                   Layer D: Surfaces (Kähler CW models)
            T2Minimal  T2Squared  P2Minimal  P1Squared  T2nBetti
                                ↓
                        Layer E: Capstone
                                
   Layer F (orthogonal): Bridge — interfaces to other subtrees
   AlphaEM / ClosureExtension / CutLog / Real213Bridge /
   Paper1Chiral / TrivialCases / XorPairCombine (G93 §C2 closed)
```

### Layer A — Cochain (73 decls)

```lean
def Cochain (n k : Nat) : Type := Fin (binom n k) → Bool

def Cochain.add {n k} (σ τ : Cochain n k) : Cochain n k :=
  fun i => xor (σ i) (τ i)
```

ℤ/2 = Bool with XOR.  Coefficient (-1) is identity in ℤ/2 (no
signs needed → all proofs operate on Bool functions).  Plus
decomposition lemmas V5_2Decomp / V5_1DecompR (the `bz5_2` /
`bz5_1` cochain decompositions used by L1).

### Layer B — Operations

#### Delta (51 decls) — boundary `∂ : Cᵏ → Cᵏ⁺¹`

`delta n k σ i = XOR over (k+1)-subsets containing i` —
combinatorial coboundary on simplicial complex.

  · `delta_add` — linearity (51 decl includes many add-related)
  · `delta_pointwise_eq` — pointwise equality propagation
  · `subsetIdx`, `kSubset` — supporting bijection machinery

#### CupAW (62 decls) — Alexander-Whitney cup `⌣ᴬᵂ`

Standard simplicial cup product.  Heaviest sub-area by mass.
Contains:

  · `cupAW` definition (Core)
  · `LeibnizAlgLift` 5-decl family (the L1 ★ family from G106)
  · `Leibniz{21,22}Final.h_components_{α,β}` 4-decl L2 family
  · `Bilinear.cupAW_add_left/right` (113K nodes each)
  · `Pointwise.cupAW_pointwise_eq` (68K nodes)
  · `Leibniz4Mixed`, `LeibnizScaling`

#### Cup (27 decls) — lex-projection cup

**The G85 rename**: original "cup" was AW-misnamed; this is
now the lex-projection cup with its own native Leibniz rule
+ boundary-endpoint correction.  Files:

  · `Core` (cup, cupList)
  · `LeibnizLex` / `LeibnizLexSelfRef` / `LeibnizLex21` /
    `LeibnizLexStructural` / `LeibnizLexListLevel` /
    `LeibnizUniversal`
  · `SubsetIdxRoundtrip` / `SubsetIdxRoundtripGeneral`
  · `FinBridge` / `FinBridgeGeneral` / `KSubsetStructural`
    (parallel branch's ∀(n, k, l) cup-unfold capstone)

#### Hodge (54 decls) — Hodge structure

  · `Star.hodgeStar` — Hodge dual operator
  · `Prop52/53` — Hodge propositions at bidegrees (5,2) and (5,3)
  · `Prop54` — bidegree (5,4) Hodge involution
  · `InvolutionCapstone`

### Layer C — Examples (156 decls)

Concrete cochain examples:
  · `K5.b1_K5` (G109 CDI-2 bridge — 5-way)
  · `SimplexBasis` (kSubset enumeration)
  · `EulerClosed` (Euler characteristic closure)
  · `BettiKernel` (Betti number computations)
  · `DiamondAudit` (Hodge diamond falsifier — G109 CDI-7)
  · `DiamondShape`
  · `EncodingBijection` / `EncodingBijection52`
  · `TopologyCompare`
  · `WhyDimFive` (motivation for d=5)

### Layer D — Surfaces (565 decls, biggest sub-area)

CW-model construction of low-dim Kähler manifolds:

| Surface | dim | cells | h^{p,q} | Signature |
|---------|----:|-------|---------|-----------|
| T² (T2Minimal) | 1 (ℂ) | 1+2+1=4 | h^{1,1}=1 | (1, 1) |
| T²×T² (T2Squared) | 2 (ℂ) | 1+4+6+4+1=16 | Künneth | (3, 3) |
| ℙ² (P2Minimal) | 2 (ℂ) | 1+1+1=3 | h^{2,0}=0, h^{1,1}=1 | (1, 0) |
| ℙ¹×ℙ¹ (P1Squared) | 2 (ℂ) | 1+2+1=4 | h^{1,1}=2 | (2, 0) |
| T²ⁿ (T2nBetti) | n (ℂ) | Künneth recursion | general | recursive |

Each surface provides a **non-vacuous witness** for Hodge
Index / Hard Lefschetz / Hodge-Riemann theorems (G10 Phase 2
follow-up).  ℤ/2 cohomology is vacuous for the original
statements; surfaces add structure to make them substantive.

### Layer E — Capstone (1 decl)

Top-level Cohomology capstone bundling key results.

### Layer F — Bridge (71 decls, orthogonal)

Interfaces to other subtrees:
  · `AlphaEMBridge` — α_em derivation via Cohomology
  · `ClosureExtension` (G109 CDI-7 partner)
  · `CutExpFiniteTruncation` / `CutLog` — to Real213/Analysis
  · `LeibnizFinding` — the G86 finding doc anchor
  · `Paper1Chiral` — physics paper bridge
  · `PredicateAsCochain` — bridge predicates → Cochain
  · `Real213Bridge` — Cochain ↔ Cut bridge
  · `TrivialCases` — degenerate edge cases
  · `XorPairCombine` (G93 §C2 closed — foldr_xor_proj)

---

## §3.  Heavy proof clusters

### Cluster I — L1 LeibnizAlgLift (already 6-layer G106)

  · 4 byte-identical siblings × 628,271 Expr nodes each =
    **2,513,084 nodes** = **20.7 % of Cohomology total mass**.
  · L1 alone is 1/5 of Cohomology by elaborated Expr.
  · Plus LeibnizAlgLift21 (5th cousin, 160,321 nodes,
    single-factor variant).
  · Plus L2 h_components_{α,β} × Leibniz{21,22}Final (22,355 +
    18,097 byte-identical pairs).

**Net L1+L2 mass**: ~2.7M nodes, ~22 % of Cohomology total.

### Cluster II — CupAW.Bilinear (cupAW_add_left/right + Pointwise.cupAW_pointwise_eq)

  · `cupAW_add_left`: 113,393 nodes
  · `cupAW_add_right`: 114,353 nodes
  · `cupAW_pointwise_eq`: 68,521 nodes
  · **Total ~296K nodes** — bilinearity + pointwise-equality
    infrastructure that L1 relies on.

### Cluster III — Universal.Prop52/53.pattern_eq_at (byte-identical pair)

  · `Universal.Prop52.pattern_eq_at`: 53,481 nodes
  · `Universal.Prop53.pattern_eq_at`: 53,481 nodes
  · **Byte-identical pair** — bidegree (5,2) and (5,3)
    universal pattern theorems share elaborated form.

**Abstraction candidate COH-1** (parallel to L1/L2):
parametric `universal_pattern_eq_at {bidegree : Nat × Nat} ...`
absorbs Prop52/Prop53.

### Cluster IV — Hodge.Prop family (4-way group)

  · `Hodge.Prop.hodge_sq_prop_5_1`: 8,409 nodes
  · `Hodge.Prop52.hodge_sq_prop_5_2`: 8,409 nodes
  · `Hodge.Prop53.hodge_involution_capstone_5_3`: 8,409 nodes
  · `Hodge.Prop54.hodge_involution_capstone_5_4`: 8,409 nodes

**4 byte-identical decls** at 8,409 nodes each — Hodge square
properties + involution capstones across bidegrees (5,1),
(5,2), (5,3), (5,4).

**Abstraction candidate COH-2**: parametric
`hodge_capstone_5_k {k : Fin 5} ...` absorbs 4 siblings.
~25K Expr nodes reduction.

### Cluster V — Surfaces Künneth recursion

  · `Surfaces.T2nBetti.T2n_betti_kunneth_recursion`: 23,863 nodes
  · Plus T2Squared 4-cell × 16-cell decomposition proofs.

Largest Surfaces-side proof.

---

## §4.  Byte-identical group inventory (79 multi-share groups)

Top groups (paired with L1/L2 from G106 context):

| Group | Size | Members |
|-------|-----:|---------|
| L1 α pair | 628,271 × 2 | LeibnizAlgLift21Alpha + 22Alpha |
| L1 β pair | 628,271 × 2 | LeibnizAlgLift + LeibnizAlgLift22 |
| ★ Universal Prop52/53 | 53,481 × 2 | Prop52.pattern_eq_at + Prop53.pattern_eq_at |
| h_components_α pair | 22,355 × 2 | Leibniz{21,22}Final.h_components_α |
| h_components_β pair | 18,097 × 2 | Leibniz{21,22}Final.h_components_β |
| Leibniz pattern 4_2 / 5_1_1 | 8,669 × 2 | Leibniz4Mixed + Leibniz |
| ★ Hodge Prop quartet | 8,409 × 4 | Prop.hodge_sq + Prop52 + Prop53 + Prop54 |
| dsq_zero Prop52/53 pair | 4,649 × 2 | Universal dsq_zero |

★ = newly surfaced abstraction candidates (this G111).

---

## §5.  Cross-domain identifications (G109 cross-ref)

Cohomology decls participate in **most** of G109's named CDIs:

  · **CDI-1**: `b₁(K_{NS,NT}) = NS² - 1 = inv_α_em` —
    `Cohomology.Bipartite.V32Betti.b1_eq_NS_sq_minus_1` member.
  · **CDI-2**: 5-way bridge —
    `Cohomology.Examples.K5.b1_K5` member.
  · **CDI-3**: 4-way —
    `Cohomology.Fractal.V25.b1_K25` member.
  · **CDI-6**: Mersenne — `Cohomology.Bridge.ClosureExtension.chi_N_pattern` partner.
  · **CDI-7**: Hubble — `Cohomology.Examples.DiamondAudit.diamond_audit_falsifier_coupling` member.
  · **CDI-8**: Fractal levels — 4 decls in `Cohomology.Fractal.Level.{level1,2,3,4}`.
  · **CDI-12**: Cup-unit identity — `Cohomology.Cup.Core.cup_all_true_5_1_at_edge0` member (with HodgeConjecture).

**Cohomology is the math-side anchor for ~70 % of G109's
math↔physics CDIs.**  This is consistent with Cohomology being
the framework's connection between abstract algebra (Hodge,
cup, Betti) and physics (gauge groups, gluon octet, color
confinement).

---

## §6.  Two-cup architecture (G85 disclosure)

Cohomology contains **two distinct cup products**:

### CupAW — Alexander-Whitney (62 decls)

```lean
def cupAW {n k l : Nat} (α : Cochain n k) (β : Cochain n l)
    : Cochain n (k+l)
```

Standard simplicial AW form.  k+l output via:
  · (k+1) + (l+1)-vertex τ with shared middle vertex
  · α evaluated on front k+1, β on back l+1

### Cup — Lex-projection (27 decls)

```lean
def cup {n k l : Nat} (α : Cochain n k) (β : Cochain n l)
    : Cochain n (k+l)
-- (α ⌣ β)(τ) = α(τ.take k) · β(τ.drop k)
```

For sorted (k+l)-subset τ: pick the single sorted partition
(front k vertices, back l vertices) and multiply.

### Why two?

`G85_cup_delta_lens_mismatch.md` documents: the original "cup"
was misnamed AW in early DRLT.  Self-correction (per
CLAUDE.md §8) led to:

  · Rename original cup → `cup` (lex-projection) with its own
    native Leibniz + boundary-endpoint correction.
  · Build CupAW separately for the proper AW form.
  · Both serve roles: AW is the textbook cup; lex-projection
    is what 213's symbolic combinatorics actually computes.

**Both** generalise to ∀(n, k, l) — parallel branch's
`FinBridgeGeneral` (Cup) + LeibnizLexListLevel (Cup lex).
CupAW's Leibniz lives in the L1 family.

This is a **deep doctrinal point**: DRLT distinguishes between
the categorically-natural cup (AW) and the operationally-direct
cup (lex-projection).  Both exist, both proven PURE, both with
their own Leibniz forms.

**Pattern candidate #17 — "Multiple Lens choices for same
categorical concept"**: when a categorical concept (cup
product, derivative, integral) admits multiple framework-
internal realisations (AW vs lex-projection; classical
derivative vs flux density), DRLT formalises ALL of them as
distinct Lens choices rather than picking one canonical form.

This generalises G108's AsLensOutput doctrine (Real213's
multiple Cut combine choices) and G110's localDivergence
(flux-density derivative).

---

## §7.  Abstraction candidates from G111

### COH-1 — Universal Prop52/53 pattern_eq_at pair
**Size**: 53,481 × 2 = 106K Expr nodes  
**Status**: byte-identical pair surfaced in §3 Cluster III.  
**Effort**: short marathon.  
**Net**: ~50K nodes retired.

### COH-2 — Hodge Prop 5_k quartet
**Size**: 8,409 × 4 = 33,636 Expr nodes  
**Status**: 4 byte-identical decls (k ∈ {1, 2, 3, 4}).  
**Effort**: short marathon.  
**Net**: ~25K nodes retired.

### COH-3 — Leibniz4Mixed + Leibniz pattern pair
**Size**: 8,669 × 2 = 17K nodes  
**Status**: cross-file byte-identical (Leibniz4Mixed
`leibniz_pattern_4_1_2` ≡ Leibniz `leibniz_pattern_5_1_1`).
Suggests parametric pattern across bidegrees.  
**Effort**: short marathon.

### COH-4 — Surfaces base-vertex cell pattern
**Size**: not measured precisely.  
**Status**: T2Minimal / T2Squared / P2Minimal / P1Squared all
construct CW cells via similar Cell0/Cell1/Cell2/Cell3 type-
defs.  Per-cell `mk.injEq`, `mk.sizeOf_spec` are auto-generated
(artifact).  But hand-written cup-pairing / signature proofs
likely follow a template across surfaces.  
**Effort**: investigation needed.

### COH-5 — Universal `dsq_zero` Prop52/53 pair
**Size**: 4,649 × 2 = 9K nodes  
**Status**: byte-identical pair (`δ² = 0` at bidegrees (5,2)
and (5,3)).  Likely parametric over bidegree.

---

## §8.  Research questions surfaced from G111

### COH-RES1 — Cup vs CupAW formal equivalence

Both cup products are defined; both have ∀(n, k, l) general
forms.  **Question**: at what specific cochains do they
agree?  At what do they differ?  A formal
`cup_equals_cupAW_iff` theorem characterising the agreement
locus would close the G85 doctrine.

Estimated effort: 2-3 sessions.

### COH-RES2 — Surfaces zoo extension

Currently: T2Minimal, T2Squared, P2Minimal, P1Squared,
T2nBetti.  Missing:
  · K3 surface (complex dim 2, h^{2,0}=1)
  · Hirzebruch surfaces F_n
  · Enriques surface
  · General toric surface

**Question**: can the CW-model methodology of Surfaces extend
to these?  Each would witness Hodge Index / Hard Lefschetz
non-vacuously.

Estimated effort: 5-10 sessions (one surface = ~1-2 sessions).

### COH-RES3 — Hodge Conjecture connection

`HodgeConjecture/` (961 decls) sits ON TOP of Cohomology.
**Question**: what proofs in HodgeConjecture reduce directly
to Cohomology theorems?  A reverse-dependency analysis from
Cohomology → HodgeConjecture would clarify the bridge.

Estimated effort: 2-3 sessions (similar to G111 itself but
for HodgeConjecture).

### COH-RES4 — Bipartite + Fractal physics bridge

`Bipartite/` and `Fractal/` contain the K_{NS,NT} + K_5 + K_25
cohomology that feeds G109's math↔physics bridges (CDI-1
through CDI-3).  **Question**: can the bridge be formalised as
a single `cohomology_to_physics_atomic_chain` lemma threading
all CDIs?

Estimated effort: 3-5 sessions.  Output would be a doctrinal
capstone tying Cohomology to Physics via atomicity.

### COH-RES5 — Two-cup choice doctrine formalisation

Extend Pattern #17 (Multiple Lens choices) into a formal
framework: `LensChoice α := { realisations : List α ; valid :
∀ r ∈ realisations, r is framework-internal }`.  Cup, derivative,
integral all become Lens choices.  Would tie G85 + G108 +
G110 doctrines.

Estimated effort: 3-5 sessions.

---

## §9.  Significance for the meta-scan tree

### What G111 confirms

  · **Encapsulation pattern**: 1,216 decls, 0 Raw, 0 Lens.view
    direct touch.  Cohomology operates entirely on Cochain +
    binom + Bool.xor.  G104 (γ) operational-gap maximally
    realised.
  · **L1 dominance quantified**: L1+L2 = ~22 % of Cohomology
    mass.  G106's 6-layer overdetermined finding is the
    dominant single feature of Cohomology.
  · **Cross-domain bridge math-side anchor**: ~70 % of G109's
    math↔physics CDIs anchor in Cohomology.  Cohomology IS the
    connector between abstract Hodge theory and physics
    constants.

### What G111 newly surfaces

  · **5+ new abstraction candidates** (COH-1 through COH-5,
    plus dsq_zero pair).
  · **2 new byte-identical pair patterns** (Universal Prop52/53,
    Hodge Prop 5_k quartet) parallel to L1/L2.
  · **Two-cup doctrine (G85)** as a deeper instance of
    Pattern #17 — "multiple Lens choices for same categorical
    concept".

### What's still unexplored

  · `HodgeConjecture/` (961 decls) — same magnitude as
    Cohomology, sits ON TOP of it.  Next natural G112 target.
  · `DyadicFSM/` (1,272 decls) — biggest Tier-3 subtree
    (Pattern #2 dominant).
  · `CayleyDickson/` (629 decls) — algebraic-integer tower
    leading to ZOmega^× = 6.

---

## §10.  Updated executor priority

Per G108 §13 + G109 §7 + G110 §11 + G111 §9:

1. **L1 LeibnizAlgLift marathon** (G106 6-layer, biggest mass)
2. **G111 COH-1 + COH-2 + COH-3** (combined ~90K nodes)
3. **G111 §6 two-cup doctrine** formalisation (COH-RES5)
4. **G110 FLUX-1** forward/backward parametric
5. **G108 REAL-1 + REAL-2** Cut iff consolidation
6. **G108 CutSumOne C** template (§3 candidate)
7. **G112 HodgeConjecture deep dive** (1-2 sessions)
8. **G113 DyadicFSM deep dive** (1-2 sessions)
9. **G114 CayleyDickson deep dive** (1-2 sessions)
10. **G115 Bishop comparison** (REAL-RES6, doctrinal, 3-5 sessions)

If only one is picked: **L1 marathon** retires the largest
single mass; **G111 COH-1+COH-2+COH-3** is the cleanest
mechanical batch.

---

## §11.  Artifacts

  · This document: `research-notes/G111_cohomology_deep_dive.md`
  · Source: G102 callgraph + G103 shape + Lean source
    inspection.
  · No new tools; analysis fits existing infrastructure.

This continues the systematic Tier-2 coverage after G108
(Real213/Analysis), G110 (FluxMVT).  Next: HodgeConjecture
(G112) or DyadicFSM (G113).
