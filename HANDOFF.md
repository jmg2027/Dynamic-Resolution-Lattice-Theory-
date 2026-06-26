# Session Handoff — 2026-06-26 (continuation)

## Branch
`claude/handoff-continuation-dqjw6i` — ahead of origin (push at session end).
Full `lake build E213` clean.  ∅-axiom standard: PURE where stated, the rest carry **only** `propext`
(Lean-4 kernel base, allowed-not-target per `STRICT_ZERO_AXIOM.md`).  Purity-check: 0 sorry / 0
external axiom / 0 native_decide / 0 Classical / 0 Mathlib.

## What Was Done This Session

Continued the cubic-reciprocity Phase B (Open Problem 1 from the prior handoff): **the Gauss-sum
Frobenius congruence `g(χ)^{⋆q} ≡ … (mod q)` — assembled to one step short of closed form** (the
`t↦tq%p` reindex).  Three new ∅-axiom theorems, all building cleanly:

### 1. B2e.9 — the Frobenius congruence, first half
`EisensteinConvGaussFrobenius.gauss_pow_modEq` (propext):
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
`EisensteinConvGaussFrobenius.gauss_pow_modEq_conj` (propext):
`g(χ)^{⋆q}(k) ≡ Σ_{t<p} χ̄(t) · e_{(t·q)%p}(k) (mod ofInt q)` for prime `q ≡ 2 (mod 3)`, `k<p`.
Combines #1 and #2 termwise (`sum_congr` rewriting `χ(t)^q ↦ conj χ(t)`).  This is the Frobenius
congruence **up to the `t↦tq%p` reindex** — the only step that remains.

## Current Precision Results
No new physics constants (pure-math arc — cubic / Eisenstein reciprocity).  Physics table in
`catalogs/physics-constants.md` unchanged.

## Open Problems (Priority Order)

### 1. B2e.11 — the `t↦tq%p` reindex (closes the Frobenius congruence)
From `gauss_pow_modEq_conj`: `g(χ)^{⋆q} ≡ Σ_t χ̄(t)·e_{tq%p} (mod q)`.  `q` is invertible mod `p`
(distinct primes), so `t↦(tq)%p` is a permutation of `[0,p)`.  Reindex `Σ_t χ̄(t)·e_{tq%p} =
Σ_s χ̄((s·q⁻¹)%p)·e_s`; then `χ̄((s q⁻¹)%p) = χ̄(s)·χ̄(q⁻¹)` (multiplicativity `chiOmega_mul`,
**already built**) factors out `χ̄(q⁻¹) = χ(q)`, collapsing into **`χ(q)·g(χ̄)`** — the honest closed
form `g(χ)^{⋆q} ≡ χ(q)·g(χ̄) (mod q)` (note `χ^q = χ̄`, so `g(χ^q)=g(χ̄)`; this is the accurate RHS,
refining the prior handoff's aspirational "χ̄(q)·g(χ)").
**Pieces available:** `aInv` (modular inverse), `LPerm`, the `totativeList_inv_lperm` pattern
(`EisensteinInvPerm`).  **Needs building:** (a) `totativeList_mul_lperm` — `t↦(t·q)%p` permutes the
totatives (the "permutation-sum reindex under `t↦a·t`" flagged in `chiOmega_mul`/`mu3_sum_zero`
docstrings; likely parallels the orthogonality sum-zero machinery in `EisensteinCharSumZero`);
(b) a **`sumRange`↔`listSum`-over-`totativeList` bridge** — the Gauss sum here is `sumRange … p`
(the `t=0` term has coefficient `χ̄(0)=0`, so it drops), but the permutation machinery is `listSum`
over `totativeList`; (c) `sumRange`/`listSum` permutation-reindex invariance for `ZOmega`.

### 2. The cubic reciprocity law `(π/π')₃ = (π'/π)₃` itself
After the Frobenius congruence: compute `g^N` two ways (`g³=p·J` from B1; Frobenius from B2e) and
compare μ₃ values using the primary normalisation (`jacobi_primary`).  Frontier note:
`research-notes/frontiers/cubic_reciprocity_law.md` (roadmap `higher_reciprocity_roadmap.md`).

### 3. (refactor) one `Frobenius-from-interior-binomial-vanishing` lemma
The cubic, p-adic (Teichmüller), and prime-counting Frobenius uses are corollaries of
`prime_dvd_binom` + a binomial theorem over the respective carrier — not yet one Lean lemma.
Frontier note: `research-notes/frontiers/cubic_reciprocity_crossdomain.md`.

## Unresolved from This Session
None attempted-and-failed.  The reindex (B2e.11) was scoped but deferred — it is a self-contained
combinatorial sub-problem (multiplication permutes totatives + a `sumRange`↔`listSum` bridge), not a
dead end.

## Next
Build B2e.11 (Open Problem 1): `totativeList_mul_lperm` (multiplication-by-`q` permutes totatives),
the `sumRange`↔`listSum`/`totativeList` bridge, and the `ZOmega` permutation-reindex, then assemble
`g(χ)^{⋆q} ≡ χ(q)·g(χ̄) (mod q)` — the closed Frobenius congruence.

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: none (Phase B still open; promotes with the reciprocity law).
- **Promotion candidates**: none outstanding for this arc.
- **Active scratchpad**: `research-notes/frontiers/{cubic_reciprocity_law, higher_reciprocity_roadmap,
  cubic_reciprocity_crossdomain}.md` (B2e.9 / B2e.10a / B2e.10b recorded in `cubic_reciprocity_law.md`).

## File Map
```
NEW (Lean):
  lean/.../CayleyDickson/Integer/EisensteinConvGaussFrobenius.lean   ← B2e.9 + B2e.10b (gauss Frobenius)
  lean/.../CayleyDickson/Integer/EisensteinCubicCharPow.lean         ← B2e.10a (χ(t)^q = χ̄(t), PURE)
MODIFIED:
  lean/E213/Lib/Math/Algebra/CayleyDickson.lean                     ← aggregator imports (2 new)
  research-notes/frontiers/cubic_reciprocity_law.md                 ← B2e.9 / B2e.10a / B2e.10b rows
```
