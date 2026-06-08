# `Cohomology/Hodge/` — Hodge star + Δ⁴ involution

Hodge star operator + ⋆⋆ = id involution structural propositions
on the 213 cohomology complex.

## Files (11)

### Hodge / Delta core
  - `Star.lean`              — Hodge `⋆` operator (cochain level)
  - `Delta.lean`              — codifferential `δ* = ⋆δ⋆`
  - `Involution.lean`         — involution machinery
  - `InvolutionTemplate.lean` — COH-2 pointwise template
                                 `hodge_involution_pointwise_5`
                                 used by every Δ⁴ stratum lift

### Prop-level lifts
  - `InvolutionLifts.lean`    — `⋆⋆ = id` Prop-lifts at all five
                                 Δ⁴ strata `(5, 0)` … `(5, 4)`
                                 plus the all-strata bundle
                                 `hodge_involution_5strata_capstone`.
                                 Named theorems for downstream
                                 consumers: `hodge_sq_prop_5_1`,
                                 `hodge_sq_prop_5_2`, and
                                 `hodge_involution_capstone_5_<k>`
                                 for `k = 0, 1, 2, 3, 4`.
  - `InvolutionCapstone.lean` — re-exports the all-strata bundle
                                 under the historical name for
                                 backward compatibility.

### Signed star / CP `C₄ = ℤ[i]`
  - `SignedStarC4.lean`       — the **signed** ⋆ on the `(Λ¹,Λ³)` pair
                                 of `Δ⁴`: `J=[[0,−1],[1,0]]`, `⋆²=−I`,
                                 `⋆⁴=I`, `ℤ[J]≅ℤ[i]` (the CP `i`).
  - `SignedStarFull.lean`     — signed ⋆ across all grade pairs.
  - `HodgeRiemannJ.lean`      — Hodge–Riemann positivity for `J`.
  - `GaussianHodgeBridge.lean`— the morphism `φ:ℤ[i]→ℤ[J]` (injective
                                 multiplicative hom): the spiral-axis
                                 **floor rotation** (`μ=−i`,
                                 `GaussianCrossDet`) IS the Hodge `⋆`,
                                 one `C₄=ℤ[i]^×`.  `crossDet_image_rotates`,
                                 `gaussian_floor_is_hodge_star`.
  - `EisensteinNoComplexStructure.lean`
                               — the order-6 axis rung is NOT a complex
                                 structure: `Ω=[[0,−1],[1,−1]]`, `Ω²=−Ω−I≠−I`,
                                 `Ω³=I`; `ℤ[Ω]≅ℤ[ω]` (`omegaToStar_mul`).  Since
                                 `⋆²=−1` fails at order 6, the Hodge `⋆` selects
                                 disc `−4` over `−3` (`hodge_selects_disc_neg_four`).

## Where to add new evidence

  - New stratum or refined identity → `InvolutionLifts.lean`
    (add a §<N> section using `hodge_involution_pointwise_5`
    template + 3 private `decide`-lemmas + 5-line capstone)
  - Hodge-star refinement      → `Star*` / `Star<refinement>.lean`
  - Codifferential extension   → `Delta*` / `Involution*`

## Companion clusters

  - `Cohomology/Cup/`        — strict cup product (Δ-related)
  - `Cohomology/CupAW/`      — Alexander-Whitney cup
  - `HodgeConjecture/Pairing/` — HIT + HR pairings
