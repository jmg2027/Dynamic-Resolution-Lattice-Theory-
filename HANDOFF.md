# Session Handoff — 2026-06-26 (continuation)

## Branch
`claude/handoff-continuation-dqjw6i` — ahead of origin (push at session end).
Full `lake build E213` clean.  ∅-axiom standard: every theorem this session is **PURE** (`#print axioms` → "does not depend on any axioms").  Purity-check: 0 sorry / 0
external axiom / 0 native_decide / 0 Classical / 0 Mathlib.

## What Was Done This Session

Continued the cubic-reciprocity Phase B (Open Problem 1 from the prior handoff): **the cubic Gauss-sum
Frobenius congruence `g(χ)^{⋆q}(k) ≡ χ(q)·χ̄(k) (mod q)` is now COMPLETE** — assembled and the `t↦tq%p`
reindex closed.  Five new ∅-axiom theorems (+ helpers), all building cleanly:

### 1. B2e.9 — the Frobenius congruence, first half
`EisensteinConvGaussFrobenius.gauss_pow_modEq` (PURE):
`g(χ)^{⋆q}(k) ≡ Σ_{t<p} χ(t)^q · e_{(t·q)%p}(k) (mod ofInt q)` for prime `q`, `k<p`.  Assembles three
closed pieces, **no new machinery**: `gauss_eq_sum_basis` under `convPow_congr` (rewrite
`g = Σ_t χ(t)·e_t` inside the `⋆`-power) → `convPow_sum_modEq_prime` (push the `q`-th `⋆`-power through
the finite sum) → `scaledBasisPow_eq` (evaluate each term `(χ(t)·e_t)^{⋆q} = χ(t)^q·e_{tq%p}`).

### 2. B2e.10a — the μ₃ character-power Frobenius
`EisensteinCubicCharPow.chiOmega_pow_q` (**PURE**): `χ_ω(t)^q = conj χ_ω(t)` for `q ≡ 2 (mod 3)`.
Case analysis on the four character values `{0,1,ω,ω²}`: `0^q=0` (`q≥1`), `1^q=1`, `ω^q=ω^{q%3}=ω²`,
`(ω²)^q=ω^q·ω^q=ω`; `conj z = z²` on `μ₃` (`conj_chiOmega_eq_sq`) packages it as `χ^q = χ̄`.  Helpers
`pow_one_base`, `pow_zero_pos`.

### 3. B2e.10b — the Frobenius congruence up to reindex
`EisensteinConvGaussFrobenius.gauss_pow_modEq_conj` (PURE):
`g(χ)^{⋆q}(k) ≡ Σ_{t<p} χ̄(t) · e_{(t·q)%p}(k) (mod ofInt q)` for prime `q ≡ 2 (mod 3)`, `k<p`.
Combines #1 and #2 termwise (`sum_congr` rewriting `χ(t)^q ↦ conj χ(t)`).

### 4. B2e.11 — the `t↦tq%p` reindex, closing the Frobenius congruence
`EisensteinConvGaussReindex` (PURE).  Key: the basis vectors `e_{(tq)%p}` are **indicators**, so at a
fixed coefficient `k` the sum collapses to the single surviving term — no permutation-sum machinery.
- `gauss_conj_reindex_collapse`: `Σ_t χ̄(t)·e_{(tq)%p}(k) = χ̄((q⁻¹·k)%p)` (existence by `aInv_spec`
  /`reindex_idx`, uniqueness by `cancel_unit`, extracted via `sum_single`).
- `gauss_pow_modEq_reindexed` (collapse): `g(χ)^{⋆q}(k) ≡ χ̄((q⁻¹·k)%p) (mod q)`.
- `char_conj_reindex_split`: `χ̄((q⁻¹·k)%p) = χ(q)·χ̄(k)` (`chiOmega_mul` + `conj_mul` +
  `χ(q⁻¹)=conj χ(q)`; helper `chiOmega_one`).
- **`gauss_pow_modEq_factored`** (closed): **`g(χ)^{⋆q}(k) ≡ χ(q)·χ̄(k) (mod q)`** for prime
  `q ≡ 2 (mod 3)`, unit mod `p`, unit coefficient `0<k<p` — the classical Frobenius congruence of the
  cubic Gauss sum (coefficient-wise `g(χ)^{⋆q} ≡ χ(q)·g(χ̄)`).

### 5. Toolkit toward the reciprocity-law assembly (step 3)
- `EisensteinConvCongruence` (**all PURE**): the mod-`M` congruence `ModEq` propagates through `⋆`
  (`conv_modEq_left`/`conv_modEq_right`, via `sumRange_modEq`) and through `⋆`-powers (`convPow_modEq`).
  The bridge that carries the Frobenius congruence (`mod q`) into products with the cube `g³=p·J`
  (`gauss_cube`) and the norm `g⋆ḡ=Yfun` (`gauss_conj_norm`) — both `⋆`-identities.
- `gauss_pow_modEq_factored_all`: the Frobenius congruence as a full group-ring congruence (every
  coefficient `k<p`, `k=0` both-sides-zero) — the form the law consumes.
- `charConj_eq_gaussConj_reflect`: `conj χ(k) = gaussConj((p−k)%p)` — bridges the Frobenius RHS `g(χ̄)`
  (character-conjugate) to the norm factor `gaussConj` (ring-conjugate), differing by the reflection
  `k↦(p−k)%p` (`refl_idx`, an involution).
- `EisensteinGaussCube.gaussConj_eq_charConj`: `gaussConj(k) = conj χ(k)` — the **exact** identity
  (since `χ(−1)=1`, `m=(p−1)/3` even): the ring-conjugate `gaussConj` *is* `g(χ̄)`.
- `gauss_pow_succ_modEq` then `gauss_pow_succ_modEq_Yfun`: **`g(χ)^{⋆(q+1)}(k) ≡ χ(q)·Yfun(k) (mod q)`**
  — the Frobenius congruence pushed to `q+1` and the norm RHS evaluated (`gaussConj_eq_charConj` +
  `conv_comm` + `gauss_conj_norm`).  The **Frobenius side** of the `g^{⋆N}`-comparison, closed form.
- `gauss_convPow3`: **`g(χ)^{⋆3}(k) = J·Yfun(k)`** — `gauss_cube` rephrased in `convPow` form
  (`convPow_succ`/`convOne_left`/`conv_congr`/`conv_comm`).  The **cube side**, same `convPow`/`Yfun`
  frame as the Frobenius side.

## Current Precision Results
No new physics constants (pure-math arc — cubic / Eisenstein reciprocity).  Physics table in
`catalogs/physics-constants.md` unchanged.

## Open Problems (Priority Order)

### 1. The cubic reciprocity law `(π/π')₃ = (π'/π)₃` itself — now the on-path target
The **Gauss-sum Frobenius congruence is COMPLETE** (B2e.11, `gauss_pow_modEq_factored`).  The law's
proof now assembles two evaluations of `g(χ)^{⋆q}` (for a second rational prime `q ≡ 2 mod 3`):
- **Frobenius side:** `g(χ)^{⋆q}(k) ≡ χ(q)·χ̄(k) (mod q)` (`gauss_pow_modEq_factored`).
- **Cube side:** `g(χ)³ = p·J` (`EisensteinGaussCube.gauss_cube`, B1) iterated — `g^{⋆q} = g·(g³)^{(q−1)/3}`
  needs `q ≡ 1 mod 3` for an integer exponent, OR work with `g^{⋆q}` via `g·g^{q−1}` and the norm
  `g·ḡ = p`.  Classical route (Ireland–Rosen ch. 9): relate `g(χ)^q` to `g(χ̄)` and use `g(χ)g(χ̄)=±p`
  to extract the μ₃ comparison, the primary normalisation `jacobi_primary` (`J=π`) killing the unit
  ambiguity, yielding `(π/π')₃ = (π'/π)₃`.
**Next bricks** (toolkit now in place — `EisensteinConvCongruence`, `gauss_pow_modEq_factored_all`,
`charConj_eq_gaussConj_reflect`): (a) push the Frobenius congruence through `⋆ g` via `conv_modEq_left`
to get `g(χ)^{⋆(q+1)} ≡ χ(q)·(g(χ̄)⋆g) (mod q)`, then use the reflection bridge + `gauss_conj_norm`
(`g⋆gaussConj=Yfun`) to evaluate the RHS; (b) the μ₃-value extraction comparing `χ(q)` (Frobenius) with
the cube-side residue symbol; (c) assemble using `jacobi_primary`.  Frontier note:
`research-notes/frontiers/cubic_reciprocity_law.md` (roadmap `higher_reciprocity_roadmap.md`).

### 2. (refactor) one `Frobenius-from-interior-binomial-vanishing` lemma
The cubic, p-adic (Teichmüller), and prime-counting Frobenius uses are corollaries of
`prime_dvd_binom` + a binomial theorem over the respective carrier — not yet one Lean lemma.
Frontier note: `research-notes/frontiers/cubic_reciprocity_crossdomain.md`.

## Unresolved from This Session
None.  Open Problem 1 from the prior handoff (the Gauss-sum Frobenius congruence) was **fully closed**
this session — the `t↦tq%p` reindex turned out to need *no* permutation-sum machinery (the basis
indicators collapse the sum to a single term at each coefficient).

## Next
The cubic reciprocity law itself (Open Problem 1 above).  **Both sides of the `g^{⋆N}`-comparison are
now in the same `convPow`/`Yfun` frame**: Frobenius `g^{⋆(q+1)} ≡ χ(q)·Yfun (mod q)`
(`gauss_pow_succ_modEq_Yfun`) and cube `g^{⋆3} = J·Yfun` (`gauss_convPow3`).  Last leg: the **μ₃
comparison** — combine the two (the shared `Yfun` factor, `Yfun⋆Yfun = p·Yfun`) to relate `χ(q)` and
`J=π` mod `q`, then `jacobi_primary` + the second prime's primary normalisation give `(π/π')₃=(π'/π)₃`.
Reference: Ireland–Rosen ch. 9.

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: none (Phase B still open; promotes with the reciprocity law).  The
  Gauss-sum Frobenius congruence is closed but the *law* (its consumer) is the promotable unit.
- **Promotion candidates**: none outstanding for this arc.
- **Active scratchpad**: `research-notes/frontiers/{cubic_reciprocity_law, higher_reciprocity_roadmap,
  cubic_reciprocity_crossdomain}.md` (B2e.9–B2e.11 recorded in `cubic_reciprocity_law.md`).

## File Map
```
NEW (Lean):
  lean/.../CayleyDickson/Integer/EisensteinConvGaussFrobenius.lean   ← B2e.9 + B2e.10b (gauss Frobenius)
  lean/.../CayleyDickson/Integer/EisensteinCubicCharPow.lean         ← B2e.10a (χ(t)^q = χ̄(t), PURE)
  lean/.../CayleyDickson/Integer/EisensteinConvGaussReindex.lean     ← B2e.11 reindex + factored_all + reflect
  lean/.../CayleyDickson/Integer/EisensteinConvCongruence.lean       ← ModEq-respects-⋆ toolkit (PURE)
MODIFIED:
  lean/E213/Lib/Math/Algebra/CayleyDickson.lean                     ← aggregator imports (4 new)
  research-notes/frontiers/cubic_reciprocity_law.md                 ← B2e.9–B2e.11 + law-toolkit rows
```
