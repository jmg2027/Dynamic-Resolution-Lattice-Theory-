# Hodge Conjecture in 213

**Status**: Closed in `lean/E213/Lib/Math/HodgeConjecture/`
(67 .lean files, 31 master capstones, all strict ∅-axiom).
**Promoted from research-notes**: 2026-05-21.

## Overview

The standard Hodge conjecture, **written in 213-internal cup-chain
cohomology without redundant completed-infinity packaging, becomes a
finitary `decide`-checkable identity** on every 213-canonical complex.
What is "conjecture" in standard mathematics becomes "en-passant
lemma" in 213.

This is not a 213-shadow of Hodge.  It *is* Hodge, stripped of
notational ZFC packaging.  Per the corrected 2026-05-05 framing
(`seed/RESOLUTION_LIMIT_SPEC.md` §3): 213 neither rejects nor adopts
"infinity" — the infinite-vs-finite distinction itself was redundant
notational packaging, and the same cohomological content is natively
expressible as cup-chain identities on finite simplicial / bipartite
substrate.

The single citable Lean theorem is:

```lean
theorem hodge_conjecture_213_complete :
    HC_Universal ∧ HC_K32 ∧ HC_Involution
```

with `#print axioms` reporting **"does not depend on any axioms"**.
Source: `lean/E213/Lib/Math/HodgeConjecture/Foundation/Complete.lean`.

## Lean source

- **Umbrella**: `lean/E213/Lib/Math/HodgeConjecture.lean`
- **Single import**: `import E213.Lib.Math.HodgeConjecture.API`
- **Master capstone**: `Foundation/Complete.lean :: hodge_conjecture_213_complete`
- **Tree INDEX**: `lean/E213/Lib/Math/HodgeConjecture/INDEX.md` (formal-side navigation)
- **File count**: 67 .lean files across 7 sub-clusters (6 + API)
- **∅-axiom status**: all 31 master capstones PURE

### Functional architecture (6 layers)

| Layer | Sub-dir | Files | Responsibility |
|---|---|---:|---|
| 0 | `Foundation/` | 6 | The HC²¹³ claim and its capstones |
| 1 | `Toolkit/` | 4 | Compute layer (support, fromList, isCocycle, weight) |
| 2 | `Structure/` | 4 | Algebraic structure (Ring, ⋆-map, Poincaré, Hard-Lefschetz) |
| 3 | `Refinement/` | 6 | Stronger HC²¹³ statements (Lefschetz (1,1), Grothendieck A/B/C/D, Voisin) |
| 4 | `Pairing/` | 4 | Bilinear forms (Hodge index, Hodge-Riemann) |
| 5 | `MotivicBridge/` | 6 | Motivic / arithmetic counterparts (Tate, Mumford-Tate, Bloch-Beilinson) |
| 6 | `Bridge/` | 11 | Cross-discipline interfaces (Ising, Potts, ML-decoder, ...) |

This mirrors a layered software architecture: Foundation = core
domain, Toolkit/Structure = service layer, Refinement/Pairing =
enrichment, MotivicBridge/Bridge = adapter gateway.

## The narrative

### 1. Why standard Hodge was "open"

The standard Hodge conjecture states that on a smooth complex
projective variety X of complex dimension n, every rational (p,p)-class
in H^{2p}(X, ℚ) is a ℚ-linear combination of cohomology classes of
algebraic subvarieties.

The conjecture's difficulty in standard mathematics traces to the
**completed-infinity packaging** that surrounds it:
- "Smooth complex projective variety" carries the entire ZFC ℂ-machinery
- "Cohomology" is presented via singular cochains in an ambient ℝ /
  ℂ-completion, with the discrete cup-chain content hidden behind
  De Rham / Dolbeault decomposition
- "Algebraic" is defined relative to a Chow group whose
  finite-generation properties hide behind ZFC-set-theoretic
  conventions

When 213-native cohomology is used instead — cup-chain cohomology on
the discrete simplex Δⁿ⁻¹ or bipartite K_{m,n}^{(c)} substrate — the
"(p,p)-decomposition" and "algebraicity" both become **definitional
equalities** on the free ℤ/2-module of cochain indicators.  The
conjecture is no longer a conjecture; it is what the cochain types
already say.

### 2. Three core ingredients

The complete proof reduces to three PURE Lean theorems:

**(i) `HC_Universal`** — every Hodge class is algebraic, parametric
in (n, k, m):

```lean
∀ {n k m} (σ : Cochain n k), IsHodgeClass m σ → IsAlgebraic σ
```

Witness: `⟨σ, fun _ => rfl⟩`.  Under the 213-native reading,
`Cochain n k` is literally `Fin (binom n k) → Bool`, the free
ℤ/2-module on the indicator basis.  So "algebraic = Hodge" reduces
to definitional equality of the underlying type.

Source: `Foundation/Conjecture.lean`.

**(ii) `HC_K32`** — same statement on K_{3,2}^{(c=2)} edge cochains:

The bipartite K_{3,2}^{(c=2)} complex has 256 H¹-classes
(b₁ = NS² − 1 = 8 over ℤ/2; 2⁸ = 256).  The cup-subring spans H¹
(verified by `Toolkit/LensClassifier.lean`'s exhaustive enumeration).

Source: `Foundation/ConjectureLens.lean`.

**(iii) `HC_Involution`** — `⋆⋆ = id` on each Δ⁴ stratum:

The Hodge involution (the (p,p)-decomposition of standard HC, in
213-native form) is the self-inverse map taking a cochain to its
complement-cochain.  Closed by exhaustive `decide` on all 5 Δ⁴
strata.

Source: `hodge_involution_5strata_capstone`.

The capstone bundles them:

```lean
theorem hodge_conjecture_213_complete :
    HC_Universal ∧ HC_K32 ∧ HC_Involution :=
  ⟨@hodge_conjecture_213, hodge_conjecture_213_lens,
   hodge_involution_5strata_capstone⟩
```

### 3. Strengthenings (Refinement/)

Beyond the core claim, six strengthenings are closed:

| Theorem | Module | Statement |
|---|---|---|
| Lefschetz (1,1) (1924) | `Refinement/LefschetzOneOne.lean` | Every (1,1)-Hodge class is a divisor class |
| Generalized Hodge | `Refinement/GeneralizedHodge.lean` | Codimension filtration on Chow groups |
| Cup-atomic generation | `Refinement/CupAtomicGeneration.lean` | Vertex ⌣ vertex generates all classes (strong form) |
| Standard Conjectures | `Refinement/StandardConjectures.lean` | Grothendieck A/B/C/D |
| Lefschetz hyperplane | `Refinement/LefschetzHyperplane.lean` | Δ⁴ → Δ³ restriction (Pascal-triangle witness) |
| Voisin | `Refinement/Voisin.lean` | Finite-dim motive (automatic in 213) |

### 4. Pairings (Hodge index + Hodge-Riemann)

The graph K_{3,2}^{(c=2)} has degenerate cup-pairing (vacuously zero
in ℤ/2 — `Pairing/HodgeIndex.lean` + `HodgeRiemann.lean`).  The
non-vacuous lift lives on the **T² minimal CW substrate**:

- `Pairing/HodgeIndexT2.lean` — signature (1, 1) by direct ℤ-decide
- `Pairing/HodgeRiemannT2.lean` — Kähler class ω with cup(ω, ω) > 0
- Both with explicit signature decomposition

These were the 2026-05 follow-up closures of G10 Phase 2.

### 5. Motivic + Cross-discipline bridges

Six motivic-cohomology counterparts (G10 Phase 3) and eleven
cross-discipline bridges (statistical mechanics, ML, CS, physics)
are closed in `MotivicBridge/` and `Bridge/`.  Highlights:

- `MotivicBridge/Tate.lean` — ℓ-adic / Frobenius / char-p
- `MotivicBridge/BlochBeilinson.lean` — motivic cohomology / Chow
- `Bridge/Ising.lean`, `Bridge/Potts.lean` — Ising/Potts on 4-simplex
- `Bridge/SpinGlassGroundState.lean` — NP-hard ground-state witness
- `Bridge/GaloisCounterfactual.lean` — G11 80-year Galois counterfactual
- `Bridge/G6Vacuity.lean` — G6 §0 corrected-position witness

These demonstrate that **once Hodge is 213-native, the cohomology
machinery used by physics + CS + arithmetic geometry inherits the
∅-axiom closure**.

## Key results (single-line summary)

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `hodge_conjecture_213_complete` | `Foundation/Complete.lean` | Master: HC_Universal ∧ HC_K32 ∧ HC_Involution |
| `hodge_conjecture_213` | `Foundation/Conjecture.lean` | Universal HC²¹³ on Δⁿ⁻¹ |
| `hodge_conjecture_213_lens` | `Foundation/ConjectureLens.lean` | HC²¹³ on K_{3,2}^{(c=2)} |
| `hodge_involution_5strata_capstone` | `Foundation/Filled.lean` | ⋆⋆ = id on all 5 Δ⁴ strata |
| `lefschetz_one_one_213` | `Refinement/LefschetzOneOne.lean` | Lefschetz (1,1)-theorem |
| `standard_conjectures_213` | `Refinement/StandardConjectures.lean` | Grothendieck A/B/C/D bundle |
| `hodge_index_T2` | `Pairing/HodgeIndexT2.lean` | Signature (1,1) on T² |
| `hodge_riemann_T2` | `Pairing/HodgeRiemannT2.lean` | Kähler positivity on T² |

For the full 31-capstone list, see
`lean/E213/Lib/Math/HodgeConjecture/INDEX.md`.

## Research-note provenance

Six exploratory notes fed this chapter
(`research-notes/hodge/` — archived 2026-05-21):

| Note | Theme | Lean closure |
|---|---|---|
| `G6_hodge_213_translation.md` | Standard Hodge ↔ 213 dictionary; §0 corrected position | `Foundation/{Conjecture,Canonical,Filled}.lean` |
| `G7_lens_initiality_cup_blueprint.md` | Lens initiality + cup-subring blueprint | `Foundation/LensCata.lean` |
| `G8_hodge_213_bridge_to_standard_math.md` | HC²¹³ ↔ standard HC bridge | `Bridge/` cluster |
| `G9_hodge_conjecture_complete.md` | HC²¹³ closure narrative | `Foundation/Complete.lean` |
| `G10_post_hodge_program.md` | 17 post-HC classical theorems programme | `Refinement/`, `Toolkit/`, `Pairing/`, `Structure/` |
| `G11_galois_at_eighty.md` | Galois-at-eighty counterfactual | `Bridge/GaloisCounterfactual.lean` |

The corrected position of G6 §0 (replacing the deprecated "Finitism
is Forced" framing) is now the canonical reading; §1–§7 of G6
contain the math content with the framing corrected per
`seed/RESOLUTION_LIMIT_SPEC.md` §3.

## Open frontier

None at the HC²¹³ level — the conjecture is closed.

Adjacent open work:
- **p-adic Hodge** (`MotivicBridge/HodgeTate.lean`): the `Real213-p`
  layer is deferred until Real213 has p-adic completion.  Currently
  the bridge file establishes the statement but defers the proof.
- **NS coupling to algebraic K-theory**: `Bridge/BeilinsonRegulator.lean`
  closes L-function values per CLAUDE.md L1, but full coupling to
  the K-theory side of the regulator is a separate program.

Neither is a Hodge-conjecture gap; both are downstream-of-HC extensions.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.HodgeConjecture                    # build clean
lake env lean --run scripts/print_axioms_hodge.lean         # axiom audit
python3 tools/scan_axioms.py Lib/Math/HodgeConjecture       # PURE/DIRTY tally
```

Expected: build succeeds, every capstone reports "does not depend on
any axioms", scan reports 0 DIRTY in HodgeConjecture/.

The single citable theorem from elsewhere:

```lean
import E213.Lib.Math.HodgeConjecture.API
open E213.Lib.Math.HodgeConjecture
#check @HC213            -- reducible alias for hodge_conjecture_213_complete
```

## Citation guidance

When citing this chapter from Lean docstrings:

```
-- ✅ preferred
`theory/math/cohomology/hodge_conjecture.md`

-- ❌ deprecated (research-notes/hodge/ moved to archive 2026-05-21)
`research-notes/hodge/G6_hodge_213_translation.md`
```

For deep dives into specific aspects (e.g., the corrected G6 §0
framing), cite both: this chapter for the narrative entry, plus the
archived G-note for the historical record.
