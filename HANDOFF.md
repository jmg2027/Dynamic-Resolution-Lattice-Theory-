# Session Handoff — 2026-06-28

## Branch
`claude/handoff-continuation-dqjw6i` — merged to `main` at session end (a merge-prep marathon).
Full `lake build E213` clean (484 modules).  ∅-axiom standard: every theorem this session is **PURE**
(`#print axioms → "does not depend on any axioms"`; 0 sorry / 0 external axiom / 0 native_decide /
0 Classical / 0 Mathlib / **0 propext**).

## Headline — CUBIC RECIPROCITY is complete (both cases, ∅-axiom)

The split case of the cubic reciprocity law was assembled and is PURE, closing the whole arc:

**`EisensteinCubicReciprocitySplit.split_cubic_reciprocity`** — for two distinct primary Eisenstein
primes `J = jacobiSum p m x` (norm `p`) and `J₂ = jacobiSum pr m₂ x₂` (norm `pr`), both `≡ 1 (mod 3)`,
the cubic residue symbols are equal: `(J/J₂)₃ = (J₂/J)₃` (i.e. `A = S` for `J^{m₂} ≡ A (mod d₂)`,
`J₂^{m} ≡ S (mod d)`).  `split_cubic_reciprocity_symbol` is the self-contained form: one common `μ₃`
value `V` is simultaneously both symbols.

Together with the inert `EisensteinCubicReciprocity.cubic_reciprocity_law` (`(π/q)₃ = χ(q)` for rational
`q ≡ 2 mod 3`), **both cases of cubic reciprocity are now formalized ∅-axiom**.  A deep-research survey
found **no proof-assistant formalization of cubic reciprocity anywhere** (Mathlib has only Jacobi/Gauss
infrastructure + quadratic reciprocity) — this is novel.

## What Was Done This Session

### 1. The split synthesis — 9 PURE bricks (B2h–B2r)
- **B2h** relaxed the split arc from `pr < p` to `pr ≠ p / ¬ p ∣ q` (so relations A and B can coexist).
- **B2i** `split_conj_residue_relation_B` — relation B (the same arc, primes swapped, mod `d`).
- **B2j/B2k** `split_residue_symbol_exists{,_B}` — both residue symbols are μ₃-valued.
- **B2l** `EisensteinMu3Lift.mu3_eq_of_modEq_pi` — a μ₃ congruence mod an Eisenstein prime of norm `>3`
  is an equality (distinct μ₃ differ by a norm-3 element).
- **B2m** `EisensteinConjModEq.conj_modEq` — the honest conjugate law `A≡B (mod d) ⟹ conj A≡conj B
  (mod conj d)` (conjugation flips the modulus; corrects the source's garbled `χ_π(ᾱ)=conj χ_π(α)`).
- **B2n** `mu3_reciprocity_algebra` — the finite closer `C=conj E·A² ∧ E=conj C·S² ⟹ A=S` (`3⁴`-`decide`).
- **B2o** `EisensteinCharNormSplit.chiOmega_eq_eisChar_gen` — `χ_ω = χ_d` for any unit `¬ p ∣ t`.
- **B2p** `char_norm_mult` — `χ_{d₂}(p) ≡ J^{m₂}·(conj J)^{m₂} (mod d₂)`.
- **B2q/B2r** the capstone `split_cubic_reciprocity` + the self-contained symbol form.

### 2. Promoted to `theory/` (the closed arc)
- New chapter **`theory/math/numbertheory/cubic_reciprocity.md`** — both cases, ∅-axiom, full synthesis
  narrative (incl. the corrected conjugate law) + key-results table.
- Foundations chapter `cubic_residue_and_jacobi_sum.md` — its "Open frontier" (the law) repointed to the
  new chapter.  `theory/math/INDEX.md` numbertheory listing updated.

### 3. `/process` — tier discipline
- Sink rule re-audited → **0 violations** (decoupled 3 permanent-tier citations of the frontier notes).
- Archived the closed notes to `research-notes/archive/cubic_reciprocity/`; `frontiers/INDEX.md` marks the
  topic CLOSED; `higher_reciprocity_roadmap.md` Phase B marked complete with the residual extensions
  recorded as the live open frontier; promotion ledger row #118.

### 4. Cross-domain insights + essay
- `cubic_reciprocity_crossdomain.md` — 3 new Phase-B shared-engine links to the main corpus (μ₃ separation
  ↔ count-Lens distinguishability; `conj_modEq` ↔ Cayley–Dickson/Hodge involution; `mu3_reciprocity_algebra`
  ↔ Zolotarev's finite-group reciprocity).
- New essay **`theory/essays/synthesis/conjugation_flips_the_modulus.md`** (ledger #119).

### 5. Merge-prep audits (all green)
`/org-audit` (corpus clean for this footprint), `/purity-check` (✅ PURE), `/ready-to-merge`
(0 layer violations, full build clean, 0 sink leaks, ahead-only) — **READY TO MERGE**.

## Current Precision Results
No physics constants changed this session (pure-mathematics arc).  See `catalogs/physics-constants.md`
for the standing precision table.

## Open Problems (Priority Order)

### 1. Cubic reciprocity — residual extensions
Supplementary laws (the units `ω`, `1−ω`), a single statement uniting the inert + split cases, and
deriving the explicit primary/coprimality/`¬p∣pr` hypotheses of `split_cubic_reciprocity` from primality
alone.  Frontier note: `research-notes/frontiers/higher_reciprocity_roadmap.md` ("Open (cubic residue)").

### 2. Higher reciprocity (quartic)
The `μ₄` law over `ℤ[i]` (disc −4), reusing the now-proven cubic scaffold.  A general `muK_eq_of_modEq`
(value group `μ_k` separated by any modulus coprime to its difference-set discriminant) and a general
"symmetric pair of `μ_k` relations ⟹ equal symbols" closer would serve both cubic and quartic at once.
Frontier note: `research-notes/frontiers/higher_reciprocity_roadmap.md`.

### 3. Cross-domain unifications (refactor targets, not gaps)
The shared-engine convergences in `research-notes/frontiers/cubic_reciprocity_crossdomain.md`: one
convolution algebra (`R[C_p]` ↔ generating functions), one Frobenius crux (`prime_dvd_binom` serving
p-adic/cubic/prime-counting), one `μ_k` separation lemma, the involution-descends-iff-modulus-stable
dichotomy.  Each is a unification target, none is a Lean theorem yet.

## Unresolved from This Session
None — the split synthesis closed cleanly.  The only mid-course correction was discovering the source
REU note's "conjugate law" is garbled (an intra-field automorphism claim that would trivialize the
character of the norm); the honest inter-modulus flip `conj_modEq` is what the capstone uses.

## Next
Quartic reciprocity over `ℤ[i]` (the cubic scaffold transfers), or the cubic supplementary laws — both
scoped in `higher_reciprocity_roadmap.md`.  Alternatively, harvest the cross-domain refactor targets
(one `μ_k` separation lemma; one Frobenius-from-binomial-vanishing lemma).

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: `theory/math/numbertheory/cubic_reciprocity.md` ← the closed cubic
  reciprocity law (ledger #118); essay `conjugation_flips_the_modulus.md` (#119).
- **Promotion candidates**: none outstanding for this branch (the arc is fully promoted).
- **Active scratchpad**: `frontiers/higher_reciprocity_roadmap.md` + `cubic_reciprocity_crossdomain.md`
  stay live (residual extensions + cross-domain board).

## File Map
```
NEW (Lean, all PURE):
  lean/.../CayleyDickson/Integer/EisensteinCubicReciprocitySplit.lean ← the split capstone + helpers
  lean/.../CayleyDickson/Integer/EisensteinConjModEq.lean             ← conj_modEq (conjugate law)
  lean/.../CayleyDickson/Integer/EisensteinCubicCharFpGen.lean        ← chiOmega_*_gen (any-unit relaxation)
NEW (theory):
  theory/math/numbertheory/cubic_reciprocity.md                      ← the law chapter (both cases)
  theory/essays/synthesis/conjugation_flips_the_modulus.md           ← essay
MODIFIED (Lean):
  lean/.../Integer/EisensteinMu3Lift.lean                            ← + mu3_eq_of_modEq_pi
  lean/.../Integer/EisensteinCharNormSplit.lean                      ← + chiOmega_eq_eisChar_gen
  lean/.../Integer/EisensteinSplitResidueSymbol.lean                 ← relaxed to pr≠p; + symbol_exists
  lean/.../Integer/EisensteinSplitReciprocity.lean / EisensteinConvGaussReindex.lean ← pr<p → pr≠p/¬p∣q
  lean/E213/Lib/Math/Algebra/CayleyDickson.lean                      ← aggregator imports
ARCHIVED:
  research-notes/archive/cubic_reciprocity/{cubic_reciprocity_law,cubic_reciprocity_synthesis_from_IR}.md
```
