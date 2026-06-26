# Session Handoff — 2026-06-26

## Branch
`claude/transport-campaign-progress-dafaoa` — ahead of origin (push pending at session end).
Full `lake build E213` clean.  ∅-axiom standard: PURE where stated, the rest carry **only** `propext`
(Lean-4 kernel base, allowed-not-target per `STRICT_ZERO_AXIOM.md`).  Purity-check: 0 sorry / 0
external axiom / 0 native_decide / 0 Classical / 0 Mathlib.

## What Was Done This Session

### 1. Phase A cubic reciprocity — promoted to `theory/`
`N(J)=p` (`EisensteinJacobiNormLaw.jacobi_norm`, PURE) + the cubic residue symbol + primary
normalisation `J=π` were promoted to a mirror chapter
`theory/math/numbertheory/cubic_residue_and_jacobi_sum.md` (catalogued in
`catalogs/derivation-breadth.md`; ledger row 116).  The reciprocity *law* stays the chapter's Open
frontier (Phase B), so the frontier note remains active — S3-permitted.

### 2. Phase B — the cubic reciprocity law's Frobenius engine (the bulk of the Lean work)
Built coefficient-wise in the free group ring `R[C_p]` (`R=ℤ[ω]`, convolution `⋆`; equality is
coefficient-wise — function equality would need the forbidden `funext`/`Quot.sound`):
- **B0** `EisensteinCubicSymbolRational.cubic_symbol_rational_iff` — ℤ[ω] symbol on a rational integer
  ⟺ rational cubic residue.
- **B1** `EisensteinGaussCube.gauss_cube` — `g(χ)³ = p·J` (group ring, **PURE**).
- **B2a** `NumberTheory.BinomPrime.prime_dvd_binom` — `q ∣ binom q t` for `0<t<q` (**PURE**), via the
  absorption identity `succ_mul_binom`.  The Frobenius crux.
- **B2b** `EisensteinBinomial.add_pow` — the binomial theorem in `ℤ[ω]`.
- **B2c** `EisensteinFreshman.add_pow_modEq_prime` — freshman's dream `(a+b)^q ≡ a^q+b^q (mod q)`.
- **B2d** `EisensteinFreshman.sum_pow_modEq_prime` — `ℤ[ω]` multinomial dream.
- **B2e** the group-ring convolution Frobenius:
  - `EisensteinConvPow` — `delta=e_0`, `convPow`, `convOne_left/right`, `conv_zero_left/right`,
    `conv_sumRange_left`, `convProd_mul_{f,g}`, `conv_scalar_right`, `convPow_scalar`,
    `convPow_congr` (mostly PURE).
  - `EisensteinConvBinomial.convPow_add_pow` — the convolution binomial theorem.
  - `EisensteinConvFreshman.convPow_add_pow_modEq_prime` + `convPow_sum_modEq_prime` — convolution
    binary + multinomial freshman's dreams.
  - `EisensteinConvBasis.basis_conv` (`e_a⋆e_b=e_{(a+b)%p}`, PURE) + `basisPow_eq`
    (`e_t^{⋆q}=e_{tq%p}`) + `scaledBasisPow_eq` (`(c·e_t)^{⋆q}=c^q·e_{tq%p}`) + `gauss_eq_sum_basis`
    (`g=Σ_t χ(t)·e_t`, PURE).

### 3. Marathon hygiene (process / org-audit / cross-domain / essay)
- **process**: decoupled 17 `lean/` docstrings from frontier-note citations (sink rule → 0
  violations); registered the cubic-reciprocity frontier in `frontiers/INDEX.md`.
- **org-audit**: stripped session-phase tags ("Phase A1..B2e.5", "route b", "THE GOAL", "before M14
  Phase B2/B3") from ~37 permanent-tier docstrings → current-state-only.
- **cross-domain**: `research-notes/frontiers/cubic_reciprocity_crossdomain.md` — 5 shared-engine
  links to main (one convolution algebra; one Frobenius crux `prime_dvd_binom` serving p-adic, cubic,
  prime-counting; `N(J)=p` = disc −3 two-squares analogue; cubic = discrete-log-mod-3 ladder).
- **essay**: `theory/essays/synthesis/the_frobenius_is_interior_count_collapse.md` (ledger row 117).

## Current Precision Results
No new physics constants this session (pure-math arc — cubic / Eisenstein reciprocity).  The headline
∅-axiom result is `N(J)=p` (`jacobi_norm`, **PURE**); the physics table in
`catalogs/physics-constants.md` is unchanged.

## Open Problems (Priority Order)

### 1. Assemble the Frobenius congruence `g(χ)^{⋆q} ≡ χ̄(q)·g(χ) (mod q)`
All pieces are built; remaining is the chain:
- `gauss_eq_sum_basis` under `convPow_congr` → `convPow_sum_modEq_prime` → `scaledBasisPow_eq` gives
  `g^{⋆q}(k) ≡ Σ_t χ(t)^q·e_{tq%p}(k) (mod q)`.
- **`χ(t)^q = χ̄(t)`** for `q ≡ 2 (mod 3)` (μ₃: `χ^q = χ^{q%3} = χ² = χ̄`) — the number-theory step.
- the `t ↦ tq%p` reindex of `[0,p)` (a permutation) to fold `Σ_t χ̄(t)·e_{tq%p}` into `χ̄(q)·g`.
Frontier note: `research-notes/frontiers/cubic_reciprocity_law.md` (roadmap
`higher_reciprocity_roadmap.md`); registered in `frontiers/INDEX.md`.

### 2. The cubic reciprocity law `(π/π')₃ = (π'/π)₃` itself
After the Frobenius congruence: compute `g^N` two ways (`g³=p·J` from B1; Frobenius from B2e) and
compare μ₃ values using the primary normalisation (`jacobi_primary`).  Same frontier note.

### 3. (refactor) one `Frobenius-from-interior-binomial-vanishing` lemma
The cubic, p-adic (Teichmüller), and prime-counting Frobenius uses are corollaries of
`prime_dvd_binom` + a binomial theorem over the respective carrier — not yet one Lean lemma.
Frontier note: `research-notes/frontiers/cubic_reciprocity_crossdomain.md`.

## Unresolved from This Session
None attempted-and-failed.  The group-ring Frobenius required re-proving the binomial / freshman
machinery for convolution coefficient-wise (the `ℤ[ω]` versions are not reusable on `R[C_p]` because
of the no-funext rule); this was completed (B2e.1–B2e.8), not a dead end.

## Next
Build `χ(t)^q = χ̄(t)` (μ₃ character power for `q ≡ 2 mod 3`), then the `t ↦ tq%p` reindex, then
chain to `g(χ)^{⋆q} ≡ χ̄(q)·g(χ) (mod q)` — Open Problem 1.

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: `theory/math/numbertheory/cubic_residue_and_jacobi_sum.md` ← the closed
  Phase-A cubic Lean sub-tree (frontier note kept active — open Phase B).
- **Promotion candidates**: none outstanding for this arc (Phase B is open; promotes with the law).
- **Active scratchpad**: `research-notes/frontiers/{cubic_reciprocity_law, higher_reciprocity_roadmap,
  cubic_reciprocity_crossdomain}.md`.

## File Map
```
NEW (Lean):
  lean/E213/Lib/Math/NumberTheory/BinomPrime.lean                          ← q ∣ binom q t (PURE)
  lean/.../CayleyDickson/Integer/EisensteinCubicSymbolRational.lean        ← B0
  lean/.../CayleyDickson/Integer/EisensteinGaussCube.lean                  ← g³=pJ (PURE)
  lean/.../CayleyDickson/Integer/EisensteinBinomial.lean                   ← ℤ[ω] binomial theorem
  lean/.../CayleyDickson/Integer/EisensteinFreshman.lean                   ← ℤ[ω] freshman + multinomial
  lean/.../CayleyDickson/Integer/EisensteinConvPow.lean                    ← convPow + linearity + scalar
  lean/.../CayleyDickson/Integer/EisensteinConvBinomial.lean               ← convolution binomial theorem
  lean/.../CayleyDickson/Integer/EisensteinConvFreshman.lean               ← convolution freshman + multinomial
  lean/.../CayleyDickson/Integer/EisensteinConvBasis.lean                  ← e_a⋆e_b, e_t^{⋆q}, gauss=Σχe
NEW (narrative):
  theory/math/numbertheory/cubic_residue_and_jacobi_sum.md                 ← promotion chapter
  theory/essays/synthesis/the_frobenius_is_interior_count_collapse.md      ← essay
  research-notes/frontiers/cubic_reciprocity_{law,crossdomain}.md          ← frontier + cross-domain
MODIFIED:
  lean/E213/Lib/Math/Algebra/CayleyDickson.lean, Lib/Math.lean             ← aggregator imports
  ~37 lean/ docstrings                                                     ← phase-tag de-narration
  catalogs/derivation-breadth.md, research-notes/frontiers/INDEX.md        ← cubic-reciprocity rows
  theory/{INDEX,essays/INDEX}.md, research-notes/promotion_essay_log.md    ← essay/chapter registration
```
