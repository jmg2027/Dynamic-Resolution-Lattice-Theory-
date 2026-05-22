# Session Handoff — 2026-05-22

## Branch

`main` — integrated cup-catalog ∀d closure (`Cup/IterErase.lean`)
and G125 Aurifeuillean campaign on the same merge cycle.

## Recently closed (this branch)

| Campaign | Status | Promoted to |
|---|---|---|
| **G120 N_U re-derivation** (7 phases) | COMPLETE | `seed/RESOLUTION_LIMIT_SPEC.md` §2 rewrite + `theory/INDEX.md` vocabulary + cascade across `theory/math/*`, `theory/physics/*`, `seed/AXIOM/*` |
| **G119 marathon** (Pisano-period for Pell, universal in `p` via FLT + F_{p²} + Frobenius) | TERMINAL CLOSURE | `theory/math/dyadic_fsm.md` (101 files), `theory/math/modular_arithmetic.md` (13 files) |
| **G121 R1 Geometrization** (8 geometries via Möbius P + mod-k Lenses) | R1 CLOSED | `theory/math/geometrization_conjecture.md` |
| **3-tier discipline + theory/ promotion campaign** | COMPLETE (90 chapters) | `theory/INDEX.md` |
| **Branch merge `claude/lean4-ast-patterns-g1gWN`** | DONE | G122 (Real213-p-adic) starter brought in; collision-renamed from G120 |
| **Full repo audit** | CLEAN | 0 sorry / 0 Mathlib / 0 native_decide; build clean.  Latest scan: **1145 PURE / 0 real DIRTY / 56 sealed-DIRTY-by-design (1201 total)**.  DRLT mathematical content (Lib/Math/*, Lib/Physics/*, Theory/*) is fully PURE.  The 56 sealed theorems sit in 7 `Lens.*` modules across three structural categories: (a) Prop-as-distinguishing thesis (propext), (b) Lens funext-by-design (Quot.sound), (c) JoinEquiv quotient-representative selection (Classical.choice).  Per `STRICT_ZERO_AXIOM.md` §"Sealed-by-design categories".  G120 framing regression fixed (`6599f889`) |

Closure logs preserved in git history; the live state is the Lean
source + theory chapters.  Don't read the per-Part marathon logs that
used to live here — they recorded transitional state of G119 and
G120 phase-by-phase.

## Open work

### A. Cup-Leibniz general ∀(n, k, l) — G86 **CLOSED 2026-05-22**
Fin-level ∀(n, k, l) twisted Leibniz proven strict PURE in
`lean/E213/Lib/Math/Cohomology/Cup/LeibnizFinGeneral.lean` as
`fin_level_leibniz_general`, plus the **pure Fin-index form**
`fin_level_leibniz_pure_form` (no list-level wrappers in
conclusion) in `Cup/LeibnizFinPureForm.lean`.  Built atop 6
new PURE files: `KSubsetEraseIdx`, `FaceIdxGeneral`, `CupOnList`,
`RangeFoldXor`, `DeltaUnfoldGeneral`, `LeibnizFinPureForm`.
Includes a self-referential restatement and four Δ⁴ bidegree
corollaries (1,1)/(2,1)/(1,2)/(2,2).  Source / closure notes:
`research-notes/G86_self_referential_lex_cup_leibniz.md`.

### A.next. G125 Lens-recipe cup catalog — **CLOSED 2026-05-22**
4 new PURE Lean files / 64+ strict-PURE theorems.

  · `Cup/LeibnizMirror.lean` — `cupRev`, `cupRev_eq_cup_swapped`,
    `list_level_leibniz_mirror`.
  · `Cup/LeibnizSym.lean` — `cupSymList`,
    `list_level_leibniz_sym` (doubled correction).
  · `Cup/LeibnizCatalog.lean` — `Recipe` inductive,
    `catalog_dispatch` capstone (3 recipes → δ-closure).
  · `Cup/SelfRefDepth.lean` (51 PURE) — `selfRefIter`, 6-channel
    catalog at d = 5, universal closed form
    `totalCupChannels d = binom (d-1) 2`, codim stratification
    `6 = NS + NT + 1`, 325-pair indicator basis uniqueness
    contracts (falsifiability), dual factorisation at d = 5
    `30 = cup·d = Λ-sum`.
  · `Cup/SelfRefDepthExtended.lean` (8 PURE, this branch) —
    d ∈ {6, 7, 8} channel counts + 5 d=6 endpoint pair firings.

**Zero-parameter physical bridges**:
  · `30 = cup-channels · d = NS · NT · d = 1/α_2 leading integer`.
  · codim-1 channel count `= 3 = NS = α_GUT coefficient` in
    `1/α_2 = 30 - 1/2 + 3·α_GUT`.
  · d = 5 unique: `cup·d = 2^d - 2` only at d = 5.

Theory promotion: `theory/math/cohomology/cup.md` self-reference
section.  Research note: `research-notes/G125_lens_recipe_cup_catalog.md`.

### A.next.open. Cup catalog further extensions (Tier-1)

| Item | Status / Notes |
|---|---|
| ~~Mirror catalog uniqueness~~ | **OBSOLETE** — symmetric to original under swap, no new content |
| **Structural ∀d codim correspondence** | **CLOSED** (`Cup/IterErase.lean` 7 PURE).  `endpoint_pair_firing_characterisation` is the universal structural theorem; d=5 catalog + d=6 spot checks are now corollaries.  Proof: iterErase + cupList factorisation, no decide |
| K_{3,2}^{(c=2)} 8-channel projection | Bridge cup-channels (6 on Δ⁴) ↔ K_{3,2} cohomology (8 channels = gluon DOF) via vertex assignment NS=3, NT=2 |
| 1/α_em decomposition derivation | `1/α_em = 60·ζ(2) + 30 + 25/3 + α_GUT/4 + α_GUT/45` — can cup catalog derive 60, 25/3? |
| Sub-direction E: cup-atomic subalgebra | Translation-invariant cochains (correction trivial) |
| Sub-direction F: p-adic cup ring | Needs G122 progress |

### B. G107 §4 action-items registry — CLOSED (archived 2026-05-22)

Every item in the 24-entry registry has a final disposition:

  · **Executed in Lean this branch** (six): L3 Pisano `obtain`,
    L4 LDD bilateral helpers, L5 CDDouble `by decide`, F
    `sigmaList`, E `DescentBase` parametric √N descent,
    REAL-1 / REAL-2 `bool_or_ladder_iff_with_pack` composer.
  · **Substantively done at audit** (four): L1 4-sibling Leibniz
    collapse, C CutSumOne 3-component template, G110 FLUX-1
    parametric, G111 COH-1/2/3 universal templates.
  · **Structurally infeasible per G118 verdict** (five): CD-1
    (ext = 2-line `cases u; cases v; congr`), CD-2 (`conj_ne_id`
    per-instance witness irreducible), CD-3 (Lipschitz `assoc_*`
    are `by decide` with no body), PHYS-1 (FractalLevelZeta master
    theorems are `refine ⟨...⟩ <;> decide` — already maximally
    compact), PHYS-2 (bracket-containment is `by decide` on Nat —
    the `decide` IS the proof).
  · **Folded into G86** (one): L1 `(n, k, l)`-fully-general
    Leibniz lift requires V5_2Decomp generalisation, joining the
    self-referential Cup-Leibniz open in §A.
  · **Narrative-complete / Lean-infeasible** (one): G117 Bishop
    comparison.  `seed/CLOSED_FORM_SPEC.md` §"Bishop subsumption"
    + `theory/math/analysis/minimal_root.md` + `Real213/Core/
    AsLensOutput.lean` discharge the doctrinal claim.  Formal
    equivalence would require importing an external Bishop API,
    which sits outside the ∅-axiom contract per CLOSED_FORM_SPEC
    §"Why the bridge is principled, not a gap".

Closure index: `research-notes/archive/metascan/INDEX.md`
(per-note disposition); narrative: `theory/meta/scanner_suite.md`
§"Open frontier".

### B+. G123 N_U-family theory — ALL PHASES CLOSED + PROMOTED

Successor to G120.  G120 demoted `N_U` to `configCount 2` and
opened the **level** `n` as a parametric axis; G123 promotes the
natural 2-parameter extension `configCountD d n := d^(d^n)` to a
canonical Lean family, while recording the three-pillar
structural forcing of `d = 5` (PairForcing / Atomicity.Five, C2a
cohomology-loss, C2b adjoint-product identity) at the physics
lens.

**Closed this branch (Phases 1-4 + 7)**:
  · Phase 1-2: `configCountD (d n : Nat) : Nat := d^(d^n)` lives in
    `Lib/Math/Cohomology/Fractal/ConfigCount.lean`.  `configCount`
    demoted to `abbrev configCountD 5 n`.  Concrete table at
    `n = 2` for `d ∈ {2, 3, 5, 7}`.  Clean recursion
    `configCountD_succ : configCountD d (n+1) = (configCountD d n)^d`
    with 213-native `pow_add_pure` / `pow_mul_pure` helpers
    (no `rw [Nat.pow_mul]` which brought `propext`).
  · Phase 3: `configCountD_pos`, `configCountD_mono_n`,
    `configCountD_mono_d`, `configCountD_diagonal`.  Three
    additional 213-native power helpers (`pow_le_pow_base`,
    `pow_le_succ`, `pow_le_pow_exp`) added inline; mono_d uses
    a 3-step chain through `d^(e^n)` (base monotonicity →
    exponent monotonicity → base monotonicity).
  · Phase 4: additive physics-layer hooks added to
    `Physics/Foundations/NResolutionFromFractal.lean`
    (`n_resolution_candidateD`, `n_resolution_candidate_eq`,
    `n_resolution_candidateD_table`) and
    `Physics/Foundations/FractalLensCardinality.lean`
    (`K_b_sq_coloring_count_eq` — `rfl` bridge,
    `K25_coloring_count_eq_configCountD`).  No migration of
    consumer literals.
  · Phase 5: full modular-reduction story in
    `Lib/Math/Cohomology/Fractal/ConfigCountModular.lean`.
    - Concrete `decide`-checked table for
      `configCountD 5 n % p` at `p ∈ {2, 3, 7, 11, 13}`,
      `n ∈ {0, 1, 2}` + cross-base level-2 sample at `p = 7`.
    - **Parametric Fermat-style reduction**:
      `pow_mod_period_pure (a p : Nat) (h_flt : a^(p-1) % p
                          = 1 % p) (k : Nat)
        : a^k % p = a^(k % (p-1)) % p`
      proved 213-native using `pow_add_pure`, `pow_mul_pure`,
      `mul_mod_pure`, `div_add_mod`.
    - Corollary on the family:
      `configCountD_mod_pure d p h_flt n
        : configCountD d n % p = d^((d^n) % (p-1)) % p`.
    - FLT smokes at `(d, p) ∈ {(5, 3), (5, 7), (5, 11), (5, 13)}`,
      composed via `UniversalFLT.universal_flt_main` and
      `prime_gcd_*` (with a new private `prime_gcd_13` and
      `flt_5_3` discharged by `decide` because
      `universal_flt_main` requires `a < p`, which fails for
      `(a, p) = (5, 3)`).
    - **Parametric per-prime reductions**:
      - `configCountD_5_mod_3_param`, `configCountD_5_mod_7`,
        `configCountD_5_mod_11`, `configCountD_5_mod_13` —
        all of the form `configCountD 5 n % p =
          5^((5^n) % (p-1)) % p`.
    - **Period-2 capstones** at `(5, 7)` and `(5, 13)`:
        `configCountD_5_mod_7_period_2`,
        `configCountD_5_mod_13_period_2`.
        General helper `pow_add_two_mod_pure` abstracts the
        order-2 step (`a^2 % b = 1 → a^(n+2) % b = a^n % b`).
    - **Closed-form parametric constants**:
        `configCountD_5_mod_2 n : configCountD 5 n % 2 = 1`
        `configCountD_5_mod_3 n : configCountD 5 n % 3 = 2`
        `configCountD_5_mod_5 n : configCountD 5 n % 5 = 0`
        (the last by induction on `n` via `configCountD_succ`).
    - **Even/odd closed-form lookup**:
        `configCountD_5_mod_7_table n :
          configCountD 5 (2n) % 7 = 5
          ∧ configCountD 5 (2n+1) % 7 = 3`.
    - **★★★ Modular-structure capstone**:
      `configCountD_5_modular_structure n` bundles the mod-2,
      mod-3, mod-5 constants and the mod-7, mod-13 period-2
      identities into a single statement at the physics base.
    - The previously-private `pow_add_pure` /
      `pow_mul_pure` helpers in
      `Lib/Math/Cohomology/Fractal/ConfigCount.lean` were
      promoted to `theorem` (no longer `private`) so the
      parametric reduction can reuse them.
  · Phase 6: `lake build` clean end-to-end;
    `scan_axioms.py` PURE on every new theorem (17 / 0 on
    ConfigCount; 9 / 0 on NResolutionFromFractal; 7 / 0 on
    FractalLensCardinality).
  · Phase 7: docstring + catalog update — `Fractal.lean` index,
    `seed/RESOLUTION_LIMIT_SPEC.md` §2,
    `catalogs/atomic-integers.md` ConfigCount-family section,
    `theory/math/cohomology/fractal.md` expanded from stub.

**Still open (downstream — out of N_U-family scope)**:
  · Structural derivation of the Gram self-energy term in
    `AlphaEM/Augmented.lean:134-141` (the 4 ppm structural gap
    of `1/α_em`).  Out of scope for N_U-family work; logged as
    the principal physics-layer open problem.
  · Eventual-periodicity capstone: building on
    `configCountD_mod_pure` and the per-prime smokes (e.g.
    `configCountD_5_mod_7`), one can articulate
    `n ↦ configCountD d n % p` is eventually periodic with
    period dividing `ord_{p-1}(d)`.  The arithmetic is
    available; the structural-period statement is a small
    additive marathon.

**Repo-wide audit**: 598 PURE / 0 DIRTY (post-all-phases scan,
including the modular-structure capstone).  `lake build` clean.

**Promotion**: chapter `theory/math/cohomology/fractal.md`
expanded from stub to full chapter following the
`theory/PROMOTION_CRITERIA.md` template.  H1-H4 verified
(79 PURE / 0 DIRTY across all 5 Fractal sub-modules; lake build
clean; Cohomology/Fractal listed in `lean/E213/ARCHITECTURE.md`;
catalogue entries in `catalogs/atomic-integers.md`).  S1-S3
verified (categorical closure; downstream-ready with two
physics-layer bridges already wired; research-note closure with
`G120_n_u_rederivation_plan.md` and `G123_n_u_family_theory.md`
moved to `research-notes/archive/`).

**Anchor commit (Phase 1-4)**: `224f417f` —
`Lib/Math/Cohomology/Fractal/ConfigCount: 2-parameter family +
physics bridges`.

**Plan reference**:
`research-notes/archive/G123_n_u_family_theory.md` — original
7-phase plan + open questions registry (archived after
promotion).

### B+++. G125 Aurifeuillean handle on N_U+1 — ALL PHASES CLOSED + PROMOTED

Successor to G124 §1.3 / §6.1 — promoted from "Most directly
DRLT-relevant" research direction to a formal Lean campaign on
this branch (`claude/n-u-followup-campaign-3PnDm`).

**Headline result**: the prime `521 = Φ_10(5) = N(29 + 8√5)` is
the **unique Aurifeuillean cyclotomic factor** of the family
`5^(5^n) + 1`, **n-uniform across all n ≥ 1**.  Lean PURE proof
via clean induction; no FLT, no period reduction, no Carmichael.

**Hunter-catalogue bridge (Phase 3)**: the Aurifeuillean norm
pair `(29, 8)` decomposes into Hunter primitives at the
physics-selected base:

```
521 = (d² + NT²)² − d · (NT³)²
    = N((d² + NT²) + NT³ · √d)   in ℤ[√d]
```

with `29 = d² + NT² = NT^d − NS = d² + d − 1` (three
independent atomic readings) and `8 = NT³` already in catalog.

**Lean** (14 PURE / 0 DIRTY across two files):
  · `Lib/Math/Cohomology/Fractal/ConfigCountAurifeuillean.lean`
    (10 theorems): norm representation, Hunter-bridge, cyclotomic
    `Φ_10(5) = 521`, seed `5^5 + 1 = 6·521`, concrete divisibility
    at `n ∈ {1, 2, 3}`, and the `aurifeuillean_fingerprint_n_u`
    capstone at the physics slice.
  · `Lib/Math/Cohomology/Fractal/ConfigCountAurifeuilleanParam.lean`
    (5 theorems): parametric `∀m, (configCount (m+1) + 1) % 521 = 0`
    via induction on `m` with auxiliary `pow_mod_base` and two
    decidable seeds (`5^5 % 521 = 520`, `520^5 % 521 = 520`).

**Catalog update**: `catalogs/atomic-integers.md` now registers
`521` under "Large integers (100+)" with the norm form, Aurifeuillean
reading, three atomic readings of 29, and Lean cross-references.
Added to "Atomic primes" list.

**Structural significance** (research-note §10):
  · §10.1 **Scale-free anchor**: 521 is preserved across every
    fractal level `n ≥ 1`; provides a complete mod-521 shadow of
    the entire `5^(5^n) + 1` sequence independent of
    sampling-regime explosion.
  · §10.2 **ℤ[√5] algebraically forced**: `Φ_10` irreducible
    over ℤ but splits in ℤ[√5] — same algebraic substrate as
    `φ = (1+√5)/2` (Mobius213.lean), Pell-Fibonacci over `F_{p²}`
    (modular_arithmetic.md), dyadic FSM (dyadic_fsm.md).
  · §10.3 **Last discrete Galois split before tetration**:
    `(29, 8) = (d² + NT², NT³)` is the cleanest discrete
    algebraic signature at the bottom of the hyper-exponential
    tower, before cyclotomic indices exit to higher-degree
    fields at `Φ_{50}, Φ_{250}, …`.

**Phases**: 1 ✓ (concrete + norm) / 2 ✓ (parametric ∀n) / 3 ✓
(Hunter bridge) / 4 ✓ (catalog) / 5 ✓ (theory promotion via
`theory/math/cohomology/aurifeuillean.md`).  H1-H4 and S1-S3 all
met per `theory/PROMOTION_CRITERIA.md`.  Research note archived
to `research-notes/archive/G125_aurifeuillean_n_u.md`.

**Q1 + Q4 combined closure**: the Hunter-Aurifeuillean
correspondence is uniquely **localised to the minimal index
`m = 1`** (= `Φ_10(5) = 521`).  At the next Aurifeuillean
cyclotomic factor `Φ_90(5) = 60081451169922001` (a 17-digit
prime), the canonical pair `(L, M) = (850554441, 364242064)`
has **no Hunter expressibility** (smallest |M| after unit
reduction = `(5^12 + 1)/2 = 122070313`, a generic algebraic
integer).  This negative-but-informative result confirms the
"last discrete Galois split before tetration" reading of §10.3:
Hunter signature persists only at the bottom of the cyclotomic
tower.  Lean: `aurifeuillean_phi_90_at_5` encodes
`850554441² = 5 · 364242064² + 60081451169922001` as a PURE
decidable identity.

**Anchor commits (this branch)**:
  · `b819b628` — Phase 1: concrete instances + norm
  · `6eb41176` — Phase 2: parametric ∀ n ≥ 1
  · `66633261` — Phase 3: Hunter bridge + structural §10

**Still open (Q2, Q3, Q5 — deferred, not on critical path)**:
  · Q2: `Φ_250(5)` factorisation structure (non-Aurifeuillean
    but possibly admits other field-extension splits).
  · Q3: `5^(5^n) − 1` family — Aurifeuillean analysis at the
    `−1` side via different cyclotomic indices.
  · Q5: `521 mod {2,3,5,7,11,13}` resonance with the G123
    modular fingerprint — numerically no obvious pattern.

### B++. G124 N_U-family cross-field connections — OPEN SURVEY

Cross-field follow-up to G123's promoted chapter.  Multi-agent
survey (4 parallel research agents: number theory, universal
algebra + logic, CA + complexity, category + type theory) of
how `configCountD d n := d^(d^n)` connects to established
mathematical fields outside DRLT.

**Source**:
`research-notes/G124_n_u_family_cross_field_connections.md`
(522 lines, 10 sections).

**Headline result — seven-reading convergence at `(d, n) = (5, 2)`**:
the integer `5^25` is simultaneously
  · `5^(5²)` (number theory, Aurifeuillean handle on `5^25 + 1`)
  · arity-2 component of `Pol([5])` maximal clone (Łukasiewicz
    `L_5` functionally complete since 5 is prime)
  · `dim_{F_5} F_5[x, y] / (x⁵ − x, y⁵ − y)` — function ring of
    affine plane `A²_{F_5}` (algebraic-geometric identity)
  · CA rule-space size for 2-input 5-state automata (sampling
    regime between full enumeration and Game-of-Life scale)
  · `|Hom_Set([5]², [5])| = |[5]^([5]²)|` (CCC exponential)
  · STLC `b² → b` inhabitant count over `|b| = 5` (gateway
    between elementary and non-elementary βη decidability,
    Statman 1979)
  · DRLT count-Lens output at K_{3,2}^{(c=2)} → K_{25} fractal
    closure
All seven derivations are independent.  Their numerical
agreement is forced, not arranged — strongest 213-internal
evidence that the slice `(5, 2)` is structurally selected.

**Concrete research directions catalogued (G124 §6)**:
  1. Aurifeuillean factor reading of `5^(5^n) + 1` — does the
     split match atomic-cofactor structure in the Hunter
     `{NS, NT, d, c}` catalogue?
  2. Finite-field affine-plane sub-ideal correspondence —
     does the bipartite K_{3,2}^{(c=2)} substrate map to a
     specific ideal of `F_5[x, y] / (x⁵ − x, y⁵ − y)`?
  3. Łukasiewicz `L_5` as the DRLT lens language reformulation.
  4. Iterated Carmichael chain extension to `p ∈ {17, 19, 23,
     29, 31, …}` — verify period-2 dominance vs new patterns.
  5. Tetration-depth-3 categorical invariant `F(5, 5) = 5^3125`
     as potential 5-adic depth-3 truncation.
  6. Sheffer-function fraction of `F(5, 2)` (Słupecki density).
  7. Reversible-CA fraction `25! / 5^25` characterisation.
  8. **Base-5 Wieferich prime search** — primes `p` with
     `p² | 5^(p-1) − 1`.  Obstructs higher-power lifts; no
     published list at base 5.
  9. MCSP correspondence — does the Hunter catalogue
     correspond to "small-MCSP" compressible functions?
 10. Quantum-CA lift of the count-Lens to unitaries on
     `(ℂ⁵)^⊗²`.

**Open frontier surveyed (G124 §7)**: Fermat primes beyond
`F_4` (1640); Dedekind closed form `M(n)` (1897); clone-lattice
structure for `d ≥ 3` (uncountable per Yanov–Muchnik);
explicit circuit lower-bound gap (Shannon `Ω(2^n/n)` random vs
`(3 + 1/86) n` explicit); CA universality decidability (Kari);
MCSP intermediate status; bounded-tetration categorical
models.

**Status**: research-note Tier-1 (volatile scratchpad).  None
of §6's directions on the immediate critical path; several
are cheap empirical extensions of the closed N_U-family
infrastructure if a future session greenlights one.

**Anchor commit**: `fc10585d` —
`research-notes/G124: N_U family cross-field connection
survey`.

### C. Doc work remaining (low priority)
- **CLAUDE.md size** — 228 / 220 target.  Compress at next major
  addition (current overflow is post-G120 + tier discipline + failure
  modes catalog growth).
- **TH-1 / TH-4** doc work routed earlier into
  `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-1 and §TH-4 (partial).

## Next campaign: G122 — Real213-p-adic (PREPARED, ready to begin)

(Renumbered on merge: originally proposed as G120 on the
`claude/lean4-ast-patterns-g1gWN` branch.  G120 was already used
for the N_U re-derivation campaign and G121 for the Geometrization
closure, so the p-adic campaign takes G122.)

The G119 modular arithmetic library (Bezout, FLT, F_{p²},
Frobenius) is the foundational substrate for a **∅-axiom
construction of the p-adic integers** `ℤ_p`.

### Resources prepared

- **`research-notes/G122_real213_padic_research_direction.md`** —
  comprehensive 6-phase research direction (6-10 sessions est.).
- **`lean/E213/Lib/Math/Padic/Foundation.lean`** — Phase 1 starter
  with `ZpDigit`, `ZpSeq`, truncation skeleton + roadmap comments.
  7 PURE, builds clean.

### Why this is the natural next campaign

- Current FSM framework is **2-adic-flavored** (dyadic bit-streams).
- `ResolutionLimit` uses `N_U = configCount 2 = 5²⁵` — base-5
  finite-resolution.
- Real213-p-adic generalises the resolution lattice base 2 → base p.
- No known ∅-axiom p-adic construction exists.  Mathlib's `Padic`
  brings Cauchy + Classical + propext.

### Reuse from G119

| G119 component | G122 usage |
|---|---|
| `add_mod_gen`, `mul_mod_pure` | Digit-by-digit arithmetic |
| `modBezout`, `modInverseFromBezout` | Hensel-lifted inverse |
| `universal_flt_main` | Teichmüller / Frobenius |
| `universal_freshman_dream` | p-adic Frobenius automorphism |
| F_{p²} machinery (FP2Sqrt5) | Quadratic extensions over ℤ_p |
| `phiFP2_pow_p_eq_frob` | Teichmüller lifts in F_{p²} |

All reused infrastructure is PURE.

### Phase outline

1. Phase 1: ZpDigit + ZpSeq foundation (1-2 sessions) — STARTED
2. Phase 2: Arithmetic (`Zp.add`, `Zp.mul`, `Zp.neg`) (1-2 sessions)
3. Phase 3: p-adic norm + valuation (1 session)
4. Phase 4: Hensel lifting + inverses (2 sessions)
5. Phase 5: ℚ_p localisation (1 session)
6. Phase 6: DRLT integration (1-2 sessions)

### Anchor target (5-adic, DRLT alignment)

Since DRLT uses `N_U = 5²⁵`, the **5-adic Real213** is especially
relevant.  Phase 6 anchor:

```lean
theorem nU_lifts_to_Z5_canonically :
    ∀ n ≤ 25, (canonical_5adic_NU).trunc n = ... := ...
```

Concrete bridge from finite-resolution DRLT lattice to (potentially)
infinite-precision 5-adic.  Whether infinite is operationally
meaningful in DRLT is itself a research question.

### Next-session start instructions

1. Read `research-notes/G122_real213_padic_research_direction.md`.
2. Open `lean/E213/Lib/Math/Padic/Foundation.lean`.
3. Implement Phase 1 TODOs:
   - `ZpSeq.trunc_lt_p_pow`
   - `ZpSeq.eq_mod_pn_iff_trunc`
   - `ZpSeq.digits_of_nat` embedding
   - Per-prime smokes at `p ∈ {2, 3, 5, 7}`.
4. Then proceed to Phase 2: new file `Arith.lean`.

## Anchor docs (next session)

| Doc | Purpose |
|---|---|
| `seed/AXIOM/05_no_exterior.md` §5 | Boot sequence — re-read every session start |
| `research-notes/G29_residue.md` | Clean foundational text |
| `theory/INDEX.md` | Book map (90 chapters) |
| `theory/PROMOTION_CRITERIA.md` | H1-H4 + S1-S3 gates |
| `lean/E213/ARCHITECTURE.md` | Layer spec (4 ring + Meta) |
| `lean/E213/docs/PROMOTION_PATTERNS.md` | Three promotion patterns |
| `STRICT_ZERO_AXIOM.md` | PURE catalog |
| `seed/META_SCAN_ARCHETYPES.md` | 11 scanner archetypes |
| `research-notes/archive/metascan/INDEX.md` | Closed action-items registry + per-note disposition |
| `research-notes/G122_real213_padic_research_direction.md` | Next campaign |
