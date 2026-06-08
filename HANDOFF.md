# Session Handoff — 2026-06-08 (CKM CP / spiral-axis bridges + apex-modulus deep-dive)

## Branch
`claude/ckm-cp-spiral-axis-UTW8U` — **13 commits ahead of `origin/main`, all pushed, READY TO
MERGE**.  Forced `rm -rf .lake/build && lake build E213` ✓ clean (307/307); `layer_audit` 0
violations / 1881 files; `kernel_regress` 45/45 0-axiom; purity 71 pure / 0 dirty across the 7
touched modules.  Full merge marathon run (merge main → `/process` → promote → cross-domain note →
`/essay` → `/org-audit` → `/purity-check` → `/ready-to-merge` → this handoff).

## What Was Done This Session

Theme: closing the two open bridges between **main's CKM CP-phase arc** and **the branch's
spiral-axis / Casoratian work** (one object `ℤ[i]^×=C₄`), then a multi-agent deep-dive on **why the
apex modulus is `1/φ²`**.

### 1. Floor rotation = Hodge `⋆` — the morphism (6 PURE ✓)
`lean/E213/Lib/Math/Cohomology/Hodge/GaussianHodgeBridge.lean`.  `gaussianToStar : ℤ[i] → ℤ[J]`,
`⟨a,b⟩ ↦ [[a,−b],[b,a]]`, proven injective + multiplicative (`gaussianToStar_mul` — the Gaussian
product IS the `2×2` matrix product).  Carries `i↦J`, floor generator `−i↦⋆³`; pushing the
`ℤ[i]`-convergent cross-determinant through `φ` turns one floor step into one Hodge step
(`crossDet_image_rotates`).  Capstone `gaussian_floor_is_hodge_star`.  (Link 1 of the crossdomain note.)

### 2. Companion/Casoratian sign IS a permutation sign (12 PURE ✓)
`Linalg213/CyclicShiftSign.lean` (10) + `Analysis/Cauchy/CasoratianPermSign.lean` (4, incl. the +2
middle-readout).  The `(m+1)`-cycle one-line `cycShift m = [1,…,m,0]` has `inversions = m`, so
`psign(cycShift m) = altSign m` (the companion-determinant sign); certified a genuine permutation of
`[0,…,m]` (`cycShift_perm_iota`, via a rotation `LPerm`).  Capstones: `companion_det_is_perm_sign`
(`det(companion a (m+1)) = psign(cycShift m)·a 0`) and `companion_det_eq_permMatrix_det`
(`= det(permMatrix(cycShift m))·a 0` — the middle readout, literal).  A **fourth** instance of
"permutation under three readouts".  (Link 2.)

### 3. Order-6 axis rung is NOT a complex structure (8 PURE ✓)
`Cohomology/Hodge/EisensteinNoComplexStructure.lean`.  The Eisenstein companion `Ω=[[0,−1],[1,−1]]`
has `Ω²=−Ω−I ≠ −I`, `Ω³=I`; `ℤ[Ω]≅ℤ[ω]` (`omegaToStar_mul`, via `ring_intZ`).  Since `⋆²=−1` fails
at order 6, the Hodge `⋆` selects disc `−4` over disc `−3` (`hodge_selects_disc_neg_four`) — cashes
out the i-point essay's selection claim.

### 4. cp_phase item (a): exact `ℤ[i]` CKM unitarity (15 PURE ✓)
`Physics/Mixing/CKMExactUnitarity.lean`.  Pythagorean-triple mixing angles `(3,4,5)/(5,12,13)/
(8,15,17)` scaled by `D=5·13·17=1105` make every CKM entry a Gaussian integer, so the rust
`ckm_cp_phase` check becomes a kernel-checked theorem: `ckm_unitary` (`M·M†=D²·I`),
`ckm_apex_pure_imaginary` (`M_ub=−425·i`, `δ=90°`), `ckm_cp_maximal` (Jarlskog `≠0`).  Float-free.

### 5. Apex-modulus deep-dive: why exactly `1/φ²` (multi-agent + 2 new theorems, 22 PURE total)
Four-agent investigation (repo archaeology / geometry / live data / theory), recorded in
`research-notes/frontiers/ckm_rho_eta_apex.md`.  Net: **the value is structurally forced**, and two
findings became ∅-axiom theorems in `Mobius213/Px/FibonacciAtomicLock.lean`:
- `apex_modulus_is_designed_square` (#4) — the apex MODULUS is `1/φ²` (two Fibonacci steps), not
  `1/φ` (one): `det Q=−1` (signed) → `det Q²=+1` (de-signed); a modulus is sign-free, so it must be
  the squared, positive eigenvalue.
- `disc_eq_atomic_sum_selects_shape` (#2) — `disc=NS²−4=NS+NT=d` is a **selection** not an accident:
  under `NT≥1` and `NT<NS`, the equation `ns²−4=ns+nt` has the unique solution `(3,2)`.
Conclusions: the primitive form is `R_u=(NS−√d)/2` (the contracting eigenvalue of the axiom-encoding
matrix `M=[[2,1],[1,1]]`); the golden structure is the **radius**, not the angle
(`arccos(1/φ²)=67.5°` is non-golden); live data (`R_u=0.3812±0.009`, `+0.08σ`) is consistent with
exact `1/φ²` but cannot distinguish it from convergents `8/21,13/34,21/55`.  Corrected a repo
imprecision: `1/φ²` is the **eigenvalue**, not the Möbius convergence rate (`P′(φ)=1/φ⁴`).  Essay
promoted: `theory/essays/synthesis/the_apex_modulus_as_self_reference_contraction.md`.

### 6. Marathon hygiene
`/process` (decoupled 4 sink-rule citations, refreshed frontier INDEX), promotion (archived the
fully-closed `casoratian_axis_cp_crossdomain` note → `research-notes/archive/`, log row 36),
cross-domain note (`selfref_matrix_crossdomain.md`), essay (log row 37), `/org-audit` (narrative
hygiene), `/purity-check` + `/ready-to-merge` (clean, READY).

## Current Precision Results (0 free parameters)
**No physics-constant table changes.**  The CKM CP-phase content is unchanged in value; this session
added the *exact `ℤ[i]` unitarity* confirmation (`CKMExactUnitarity`, item a) and the *structural*
forcing of `R_u=1/φ²` (eigenvalue + de-signing + selection).  See `catalogs/physics-constants.md` +
`theory/physics/cp_phase.md` for the standing DRLT table (α_em 0.09 ppb, δ=90° forced, R_u=1/φ²).

## Open Problems (Priority Order)

### 1. The `det=1` ↔ base-normalization arrow (why apex modulus = `λ₋`)
The value `R_u=(NS−√d)/2=1/φ²` is forced; the standing premise is the *identification* — why the
physical apex modulus IS the contracting eigenvalue.  Candidate route: `M` is unimodular
(`det=1` ⟹ `λ₊λ₋=1`); the unitarity-triangle base-normalization (one leg ≡ 1 carries `λ₊`) forces
the apex onto `λ₋`.  Build: express the CKM in `M`'s eigenbasis, show the 1–3 sector inherits `λ₋`.
Frontier: `research-notes/frontiers/ckm_rho_eta_apex.md` (finding #5) + `selfref_matrix_crossdomain.md`.

### 2. The `α=90°` right-triangle prediction `ρ̄=1/φ⁴≈0.146` (falsifier to watch)
Separate from the radius claim: `α=90°` (from the proven Hodge `C₄`) forces `ρ̄=R_u²=1/φ⁴`, in
`−1.6σ` tension with observed `ρ̄≈0.159` (the `O(λ²)` Wolfenstein correction does NOT cure it).
Keep decoupled from the radius; test as ρ̄ precision improves.
Frontier: `research-notes/frontiers/ckm_rho_eta_apex.md`.

### 3. New cross-domain buildables (selfref_matrix_crossdomain)
(a) a `theory/` note "unimodularity as the shared engine" (`det M=1` apex reciprocity ↔
`det(AB)=det A·det B` across Casoratian / CKM-unitarity / Legendre); (b) the companion-cycle reading
of the apex; (c) the two eigen-fields of `d=5` (`R_u∈ℚ(√5)` disc+5 vs `i∈ℚ(√−4)` disc−4).
Frontier: `research-notes/frontiers/selfref_matrix_crossdomain.md`.

### 4. cp_phase generation-Yukawa explicit construction (classical-shaped)
The CP value `90°` is forced and item (a) (numerical unitarity) is now ∅-axiom; the explicit
`5̄⊕10` generation Yukawa from first principles stays open.
Frontier: `research-notes/frontiers/cp_yukawa_from_scratch.md`.

### 5. π continued-fraction non-holonomicity (classical open)
Unchanged.  Frontier: `research-notes/frontiers/pi_nonholonomicity/`.

## Unresolved from This Session
No dead ends.  Purity traps navigated (worth remembering):
- **`by_contra` is unavailable + Classical-tainted** — use constructive `Nat.lt_or_ge` case-splits.
- **Core Nat lemmas `Nat.add_mul`, `Nat.mul_assoc`, `Nat.add_right_cancel` leak `propext`** — use
  `E213.Meta.Nat.PureNat.{add_mul, add_left_cancel}` + bound-and-case instead (probe with
  `lake env lean` + `#print axioms` before trusting a core Nat lemma in a strict-pure proof).
- The data cannot distinguish `1/φ²` from its Fibonacci convergents (~20× tighter `σ_Ru` needed).

## Next
Highest-value: **(1)** build the `det=1`↔base-normalization arrow (closes "why apex=`λ₋`", the one
remaining premise behind `R_u=1/φ²`), or **(3a)** the "unimodularity as shared engine" note, or a
fresh field marathon (`blueprints/`).

## Three-tier state (per CLAUDE.md "Three-tier discipline")
- **Promotions this session**: essay `theory/essays/synthesis/the_apex_modulus_as_self_reference_
  contraction.md` (log row 37); archived `casoratian_axis_cp_crossdomain` → `research-notes/archive/`
  (log row 36); the_i_point + three_readouts essays + cp_phase.md updated in place.
- **Promotion candidates**: none outstanding (this session's theorems extend already-closed topics
  whose chapters/essays were updated).
- **Active scratchpad**: `research-notes/frontiers/{ckm_rho_eta_apex, selfref_matrix_crossdomain,
  cp_yukawa_from_scratch, pi_nonholonomicity}`.

## File Map
```
lean/E213/Lib/Math/Cohomology/Hodge/GaussianHodgeBridge.lean         ← NEW: φ:ℤ[i]→ℤ[J], floor rot = Hodge ⋆ (6 PURE)
lean/E213/Lib/Math/Cohomology/Hodge/EisensteinNoComplexStructure.lean ← NEW: order-6 ≠ complex structure (8 PURE)
lean/E213/Lib/Math/Algebra/Linalg213/CyclicShiftSign.lean            ← NEW: cycShift, psign=altSign (10 PURE)
lean/E213/Lib/Math/Analysis/Cauchy/CasoratianPermSign.lean           ← NEW: companion sign = perm sign = permMatrix det (4 PURE)
lean/E213/Lib/Physics/Mixing/CKMExactUnitarity.lean                  ← NEW: exact ℤ[i] CKM unitarity, item a (15 PURE)
lean/E213/Lib/Math/Algebra/Mobius213/Px/FibonacciAtomicLock.lean     ← +de-signing (#4) + selection (#2) theorems (21 PURE)
lean/E213/Lib/Physics/Mixing/JarlskogApex.lean                      ← docstring: eigenvalue (not convergence rate) fix
lean/E213/Lib/{Cohomology/Hodge,Algebra/Linalg213,Analysis/Cauchy,Physics/Mixing}.lean ← aggregator imports
theory/essays/synthesis/the_apex_modulus_as_self_reference_contraction.md ← NEW essay (why 1/φ²)
theory/essays/synthesis/{the_i_point_of_the_spiral_axis,the_permutation_under_three_readouts}.md ← updated (bridges built)
theory/physics/cp_phase.md                                           ← item (a) closed in Lean
research-notes/frontiers/ckm_rho_eta_apex.md                         ← multi-agent deep-dive (findings #1-7)
research-notes/frontiers/selfref_matrix_crossdomain.md               ← NEW cross-domain note
research-notes/archive/casoratian_axis_cp_crossdomain.md             ← archived (both links closed)
research-notes/promotion_essay_log.md                                ← rows 36/37
```
