import E213.Lib.Math.CayleyDickson.Tower.MetaTowerLoopSpine
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaUnits
import E213.Lib.Math.CayleyDickson.Integer.Hurwitz213

/-!
# Seed unit-group governance of the meta-CD-tower

The column/branch structure of the meta-Cayley–Dickson tower is governed
by the **seed's root-of-unity group** `μ` (the unit group of the base
order).  The four formalised bases realise the classification:

| seed | `μ` | `\|μ\|` | density `\|μ\|/2` | branch |
|---|---|---|---|---|
| `ℤ[√-2]` | `μ₂ = {±1}` | 2 | 1 | dyadic |
| `ℤ[i]`   | `μ₄`        | 4 | 2 | dyadic |
| `ℤ[ω]`   | `μ₆`        | 6 | 3 | Eisenstein |
| Hurwitz  | `2T`        | 24| (rank 2) | Eisenstein-containing |

Two readings, both decidable shadows of standard facts:

  * **Density** is `|μ|/2 = |μ/{±1}|` — per-level unit count `= (|μ|/2)·dim`
    (densities 1, 2, 3 for the rank-1 seeds).  This is a *corollary of the
    doubled-basis construction* — the basis loop doubles with `dim`, so
    its size is the seed count read back out — not independent evidence;
    the contentful invariant is the branch.  That `ℤ[i]` (`μ₄`) and `ℤ[ω]`
    (`μ₆`) are the *only* imaginary quadratic orders with `μ ≠ {±1}` is the
    classical Dirichlet trichotomy, **cited not formalized** — here it
    appears only as the three finite seed counts `2, 4, 6`.

  * **Branch** is the *odd torsion* of `μ`: dyadic when `3 ∤ |μ|` (the
    `μ₂`, `μ₄` columns carry only 2-power torsion); Eisenstein when
    `3 ∣ |μ|` (the `μ₆` column carries order-3 and order-6 units).  The
    Hurwitz binary-tetrahedral seed `2T` contains `μ₆` (`ω ∈ 2T`), so its
    torsion menu contains the Eisenstein menu as its abelian core, with
    the non-abelian quaternionic completion on top (rank-2 lift).

The densest rank-1 seed `ℤ[ω]` has `|μ| = 6 = NS · NT`, the product of the
two atomic counts.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.SeedUnitGovernance

open E213.Lib.Math.CayleyDickson.Tower.MetaTowerLoopSpine
open E213.Lib.Math.CayleyDickson.Levels.Cayley
open E213.Lib.Math.CayleyDickson.ZSqrtMinus2
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaOct
open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Integer.Hurwitz213
open E213.Lib.Math.CayleyDickson.Levels.Sedenion
open E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Lib.Physics.Simplex.Counts

/-- ★ **Seed unit-group sizes `|μ| ∈ {2, 4, 6}` (+ 24 for the rank-2
    Hurwitz seed).**  The three rank-1 (imaginary quadratic) seeds realise
    the Dirichlet trichotomy `μ₂ / μ₄ / μ₆`; `ℤ[i]` and `ℤ[ω]` are the two
    with extra units.  Density `c = |μ|/2 ∈ {1, 2, 3}`. -/
theorem seed_unit_trichotomy :
    z2_base_units.length = 2      -- ℤ[√-2] : μ₂  (density 1)
    ∧ ZIUnits.length = 4          -- ℤ[i]   : μ₄  (density 2)
    ∧ units6.length = 6           -- ℤ[ω]   : μ₆  (density 3)
    ∧ hur_units.length = 24 :=    -- Hurwitz: 2T  (rank-2 seed)
  ⟨by decide, by decide, units6_length, hur_units_count⟩

/-- ★ **Density `= |μ|/2` at two independent scales.**  The per-level unit
    count is `(|μ|/2)·dim` at both dim 8 and dim 16 for all three rank-1
    columns — densities `2, 1, 3` (Type A `ℤ[i]`, B `ℤ[√-2]`, C `ℤ[ω]`),
    not a single-dimension coincidence. -/
theorem seed_density_two_scales :
    -- dim 8
    (cay_units.length = 2 * 8 ∧ L4T_units.length = 1 * 8 ∧ zoq_units.length = 3 * 8)
    -- dim 16
    ∧ (sed_units.length = 2 * 16 ∧ L5T_units.length = 1 * 16
       ∧ zooct_units.length = 3 * 16) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide

/-- ★ **The densest rank-1 seed has `|μ| = NS · NT`.**  The Eisenstein
    seed `ℤ[ω]` has unit-group order `6 = NS · NT = 3 · 2`.  The
    *structural* reading is proved in `eisenstein_units_crt`: `μ₆ ≅
    μ_NT × μ_NS` (CRT), an order-`NT` factor `{±1}` times an order-`NS`
    factor `{1,ω,ω²}`, so `6` is the genuine `μ_NS × μ_NT` decomposition,
    not a numerical collision. -/
theorem eisenstein_seed_unit_count_eq_NS_NT : units6.length = NS * NT :=
  units_count_eq_NSNT

set_option maxHeartbeats 4000000 in
/-- ★ **Branch is the odd torsion of `μ`.**  Across *every* measured
    dyadic cell — Type A `Lipschitz, Cayley, Sedenion` and Type B `L4T,
    L5T` — the order-3 count is `0`; the Eisenstein column
    (`ZOmegaDouble`) carries `2`, the Hurwitz seed `8`.  So a column is
    Eisenstein/Hurwitz-type exactly when its loops carry 3-torsion.

    The load-bearing direction — CD doubling never *creates* odd torsion
    on the dyadic side — is verified pointwise on these cells (no uniform
    "all levels" theorem); the Eisenstein side has the matching
    preservation `typeC_cyclotomic_3_preserved`. -/
theorem branch_by_odd_torsion :
    (lip_units.countP (fun u => lip_orderOf u = 3) = 0
     ∧ cay_units.countP (fun u => cay_orderOf u = 3) = 0
     ∧ sed_units.countP (fun u => sed_orderOf u = 3) = 0
     ∧ L4T_units.countP (fun u => L4T_orderOf u = 3) = 0
     ∧ L5T_units.countP (fun u => L5T_orderOf u = 3) = 0)
    ∧ zod_units.countP (fun u => zod_orderOf u = 3) = 2
    ∧ hur_units.countP (fun u => hur_orderOf u = 3) = 8 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
   by decide, hur_order_distribution.2.2.1⟩

/-- ★ **The Hurwitz seed `2T` carries the Eisenstein cyclotomic torsion.**
    `2T` has both order-3 (8) and order-6 (8) units — the cyclotomic
    orders `{3,6}` of the Eisenstein menu.  This is the *order-count*
    statement: `2T`'s torsion menu includes `{3,6}`, hence overlaps the
    Eisenstein branch.  The actual subgroup `μ₆ ⊂ 2T` is witnessed
    separately in `mu6_subgroup_of_2T` (a cyclic order-6 generator + its
    powers).  Note `2T`'s 3-torsion (8 elements) is far richer than a
    single `μ₆` (2 order-3 elements): `2T ≅ SL(2,𝔽₃)` is non-abelian of
    order 24, with `μ₆` only one cyclic subgroup. -/
theorem hurwitz_carries_cyclotomic_torsion :
    hur_units.countP (fun u => hur_orderOf u = 3) = 8
    ∧ hur_units.countP (fun u => hur_orderOf u = 6) = 8 :=
  ⟨hur_order_distribution.2.2.1, hur_order_distribution.2.2.2.2.1⟩

/-- ★★ **Seed governs tower — master statement.**  The decidable shadows
    of seed-`μ` governance, bundled: the unit-count trichotomy
    `|μ| ∈ {2,4,6}` (+ 24 for Hurwitz), the Eisenstein length `= NS·NT`,
    the branch separator (order-3 count `0` dyadic vs `2`/`8`
    Eisenstein/Hurwitz), and the Hurwitz cyclotomic counts.  The density
    `|μ|/2` and the loop-class names live in the per-theorem docstrings;
    the *number-theoretic* labels (the `{±1}/μ₄/μ₆` trichotomy is the full
    list of imaginary-quadratic unit groups; `μ₆ ⊂ 2T`) are classical
    facts cited, not formalized here. -/
theorem seed_governs_tower :
    (z2_base_units.length = 2 ∧ ZIUnits.length = 4
       ∧ units6.length = 6 ∧ hur_units.length = 24)
    ∧ units6.length = NS * NT
    ∧ (cay_units.countP (fun u => cay_orderOf u = 3) = 0
       ∧ zod_units.countP (fun u => zod_orderOf u = 3) = 2
       ∧ hur_units.countP (fun u => hur_orderOf u = 3) = 8)
    ∧ (hur_units.countP (fun u => hur_orderOf u = 3) = 8
       ∧ hur_units.countP (fun u => hur_orderOf u = 6) = 8) :=
  ⟨seed_unit_trichotomy, eisenstein_seed_unit_count_eq_NS_NT,
   ⟨branch_by_odd_torsion.1.2.1, branch_by_odd_torsion.2.1, branch_by_odd_torsion.2.2⟩,
   hurwitz_carries_cyclotomic_torsion⟩

/-! ### Hardening the cited claims into proofs -/

/-- A primitive 6th root in the Hurwitz units `2T`:
    `g = (1+i+j+k)/2` (scaled `⟨1,1,1,1⟩`).  `g³ = -1`, `g⁶ = 1`. -/
def hur_zeta6 : Hurwitz := ⟨1, 1, 1, 1⟩

/-- The cyclic subgroup `⟨g⟩ = {1, g, g², g³, g⁴, g⁵}` inside `2T`. -/
def mu6_in_hurwitz : List Hurwitz :=
  [hur_one, hur_zeta6, hur_zeta6 * hur_zeta6,
   hur_zeta6 * hur_zeta6 * hur_zeta6,
   hur_zeta6 * hur_zeta6 * hur_zeta6 * hur_zeta6,
   hur_zeta6 * hur_zeta6 * hur_zeta6 * hur_zeta6 * hur_zeta6]

/-- ★ **`μ₆ ⊂ 2T` — an actual cyclic-6 subgroup witness.**  `g = ⟨1,1,1,1⟩`
    is a primitive 6th root (`hur_orderOf g = 6`); its 6 powers are
    distinct and all lie in `hur_units`.  So `⟨g⟩ ≅ μ₆` is a genuine
    cyclic subgroup of the Hurwitz unit group `2T` — the subgroup
    containment the order counts alone could not witness. -/
theorem mu6_subgroup_of_2T :
    hur_orderOf hur_zeta6 = 6
    ∧ mu6_in_hurwitz.length = 6
    ∧ mu6_in_hurwitz.Nodup
    ∧ (∀ x ∈ mu6_in_hurwitz, hur_units.contains x = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The order-`NT` (= 2) factor `{±1}` of the Eisenstein unit group. -/
def eis_mu_NT : List ZOmega := [⟨1, 0⟩, ⟨-1, 0⟩]

/-- The order-`NS` (= 3) factor `{1, ω, ω²}` (cube roots of unity). -/
def eis_mu_NS : List ZOmega := [⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]

/-- The CRT product list `{s · t : s ∈ μ_NT, t ∈ μ_NS}`. -/
def eis_crt_products : List ZOmega :=
  [(⟨1, 0⟩ : ZOmega) * ⟨1, 0⟩, (⟨1, 0⟩ : ZOmega) * ⟨0, 1⟩,
   (⟨1, 0⟩ : ZOmega) * ⟨-1, -1⟩,
   (⟨-1, 0⟩ : ZOmega) * ⟨1, 0⟩, (⟨-1, 0⟩ : ZOmega) * ⟨0, 1⟩,
   (⟨-1, 0⟩ : ZOmega) * ⟨-1, -1⟩]

/-- ★ **`μ₆ ≅ μ_NT × μ_NS`, wiring `6 = NS·NT` to structure.**  The
    Eisenstein unit group splits by CRT as `{±1} × {1,ω,ω²}` — an
    order-`NT` factor times an order-`NS` factor.  The product map
    `μ_NT × μ_NS → μ₆`, `(s,t) ↦ s·t`, is a bijection onto `units6`
    (`Nodup`, both inclusions).  So `|μ₆| = NS · NT` is the *structural*
    `μ_NS × μ_NT` decomposition, not a numerical collision. -/
theorem eisenstein_units_crt :
    eis_mu_NT.length = NT
    ∧ eis_mu_NS.length = NS
    ∧ eis_crt_products.length = NS * NT
    ∧ eis_crt_products.Nodup
    ∧ (∀ x ∈ eis_crt_products, units6.contains x = true)
    ∧ (∀ x ∈ units6, eis_crt_products.contains x = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Tower.SeedUnitGovernance
