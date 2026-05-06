import E213.Lib.Math.HodgeConjecture.Bridge.MotiveEtaleFusion

import E213.Lib.Math.HodgeConjecture.Bridge.BeilinsonRegulator
import E213.Lib.Math.HodgeConjecture.Bridge.GaloisCounterfactual
import E213.Lib.Physics.Simplex.Counts
/-!
# — same lattice, different trajectory routes

213-internal framing of "":
NOT a discrete jump (finitist vocabulary, presupposes a continuum
baseline that's been broken) NOR a non-analytic limit (infinitist
vocabulary, presupposes completed infinity).  Both terms come from
ZFC-internal debates *about* infinity that 213 does not engage in.

In 213 the trajectory IS the object.  At a parameter change, the
trajectory **re-routes**: the same finite lattice now passes
through a different set of atomic indicators.  Two phases = two
routes coexisting on the same lattice; the order parameter is the
trajectory itself, not a scalar measured at a point.

Three concrete route-pairs witnessed here, each `decide`-checked:

  · BL route-pair: at p = q+1 the motivic arrow re-routes from
    "identity onto atomic basis" (p ≤ q) to "zero object" (p > q).
  · Galois route-pair: full vs σ-fixed sub-trajectory; both reach
    the same lattice positions, only the σ-fixed mask is different.
  · K_{3,2} cell-filling family: k=0,1,2,3 each a different
    cup-product route; "b_1 = 8 − k" is which-route-you're-on,
    not a value jumping.

STRICT ∅-AXIOM by `decide`.
-/

namespace E213.Lib.Math.HodgeConjecture.Bridge.PhaseRouting

open E213.Lib.Physics.Simplex.Counts (binom NS NT)
open E213.Lib.Math.HodgeConjecture.Bridge.BeilinsonRegulator (zetaΔ)
open E213.Lib.Math.HodgeConjecture.Bridge.GaloisCounterfactual (fixedCount)
open E213.Lib.Math.HodgeConjecture.Bridge.MotiveEtaleFusion
  (motivicDim etaleDim)

/-! §1  The Route abstraction.

A route is a Nat-indexed function giving the *count of atomic
indicators reached* at each parameter step.  Two routes are
"distinguishable at parameter p" iff their counts at p differ. -/

abbrev Route : Type := Nat → Nat

/-- Routes agree at parameter p: same indicator-count reached. -/
def routesAgree (r₁ r₂ : Route) (p : Nat) : Bool := decide (r₁ p = r₂ p)

/-- Route divergence at parameter p: they reach different counts. -/
def routesDiverge (r₁ r₂ : Route) (p : Nat) : Bool := decide (r₁ p ≠ r₂ p)

/-! §2  BL route-pair: motivic vs étale on Δ⁴ at fixed Tate twist q. -/

/-- Motivic BL route at twist q: stratum p ↦ motivicDim 5 p q.
    Drops to 0 once p > q (the BL "forbidden" regime). -/
def routeBL_motivic (q : Nat) : Route := fun p => motivicDim 5 p q

/-- Étale BL route at twist q: stratum p ↦ binom 5 p (no drop). -/
def routeBL_etale (q : Nat) : Route := fun p => etaleDim 5 p q

/-- BL routes AGREE on p ≤ q (the strict-BL regime). -/
theorem BL_routes_agree_2_at_0 : routesAgree (routeBL_motivic 2) (routeBL_etale 2) 0 = true := by decide
theorem BL_routes_agree_2_at_1 : routesAgree (routeBL_motivic 2) (routeBL_etale 2) 1 = true := by decide
theorem BL_routes_agree_2_at_2 : routesAgree (routeBL_motivic 2) (routeBL_etale 2) 2 = true := by decide

/-- BL routes RE-ROUTE at p = q+1 (motivic kills, étale survives).
    This is the "" — same lattice, different route. -/
theorem BL_routes_diverge_2_at_3 : routesDiverge (routeBL_motivic 2) (routeBL_etale 2) 3 = true := by decide
theorem BL_routes_diverge_2_at_4 : routesDiverge (routeBL_motivic 2) (routeBL_etale 2) 4 = true := by decide
theorem BL_routes_diverge_2_at_5 : routesDiverge (routeBL_motivic 2) (routeBL_etale 2) 5 = true := by decide

/-- The re-route is sharp: divergence appears exactly at p = q+1, not earlier. -/
theorem BL_sharp_at_q3 :
    routesAgree (routeBL_motivic 3) (routeBL_etale 3) 3 = true
    ∧ routesDiverge (routeBL_motivic 3) (routeBL_etale 3) 4 = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-! §3  Galois route-pair: full vs σ-fixed sub-trajectory on Δ⁴.

    Both routes live on the SAME lattice (Δ⁴'s 6 strata).  They
    coexist; the σ-fixed route is not "ζ_Δ minus something" but a
    PARALLEL route through only the σ-invariant indicators. -/

/-- Full route on Δ⁴: stratum k ↦ binom 5 k. -/
def routeFull : Route := fun k => binom 5 k

/-- σ-fixed route on Δ⁴: only ∅ (k=0) and full set (k=5) are σ-fixed
    as atomic indicators (the only k-subsets preserved by the
    cyclic 5-rotation σ = (0 1 2 3 4)). -/
def routeGalois : Route := fun k =>
  if k = 0 then 1 else if k = 5 then 1 else 0

/-- The two routes COEXIST on the lattice; their indicator counts
    differ at strata 1, 2, 3, 4 (where σ has no fixed atoms) and
    agree at the extremes 0, 5 (where the unique subset is σ-fixed). -/
theorem galois_route_agrees_at_0  : routesAgree    routeFull routeGalois 0 = true := by decide
theorem galois_route_diverges_1   : routesDiverge  routeFull routeGalois 1 = true := by decide
theorem galois_route_diverges_2   : routesDiverge  routeFull routeGalois 2 = true := by decide
theorem galois_route_diverges_3   : routesDiverge  routeFull routeGalois 3 = true := by decide
theorem galois_route_diverges_4   : routesDiverge  routeFull routeGalois 4 = true := by decide
theorem galois_route_agrees_at_5  : routesAgree    routeFull routeGalois 5 = true := by decide

/-- Sum-over-route gives the conserved trajectory invariant.
    Full route ⇒ 32; Galois route ⇒ 2 = fixedCount.  Same lattice,
    two parallel sums = two coexisting "phases". -/
def routeSum (r : Route) (n : Nat) : Nat :=
  (List.range (n+1)).foldl (fun acc k => acc + r k) 0

theorem routeSum_full   : routeSum routeFull 5   = 32 := by decide
theorem routeSum_galois : routeSum routeGalois 5 = 2  := by decide
theorem routeSum_full_eq_zeta : routeSum routeFull 5 = zetaΔ 5 0 := by decide
theorem routeSum_galois_eq_fixed : routeSum routeGalois 5 = fixedCount := by decide

/-! §4  K_{3,2} cell-filling routing family.

    K_{3,2}^{(c=2)} as a 1-skeleton has 5 vertices and 12 edges.
    Filling k of the 3 simple 4-cycles with 2-cells defines a new
    cup-product route.  Each k ∈ {0, 1, 2, 3} is its OWN trajectory
    on the same vertex/edge lattice — not "the same theory with a
    parameter dialed", but DIFFERENT routes through cohomology. -/

/-- Cell-filling route: at fixed k 2-cells filled, indicator counts
    at degrees (0, 1, 2) are (1, 8 − k, 0) (rank-nullity per
    `Bipartite.V32Betti.b1_eq_8_dim_count` + 2-cell extension).
    Beyond degree 2 vanishes for these small k. -/
def routeFilling (k : Nat) : Route := fun degree =>
  if degree = 0 then 1
  else if degree = 1 then 8 - k
  else 0

/-- The four routes (k=0..3) all live on the same vertex/edge
    skeleton.  Each pair of routes differs at degree 1 by 1 unit
    (the # atomic indicators reached after extra cell-filling). -/
theorem filling_route_0_at_1 : routeFilling 0 1 = 8 := by decide
theorem filling_route_1_at_1 : routeFilling 1 1 = 7 := by decide
theorem filling_route_2_at_1 : routeFilling 2 1 = 6 := by decide
theorem filling_route_3_at_1 : routeFilling 3 1 = 5 := by decide

/-- Adjacent filling routes differ by exactly 1 at degree 1: each
    new 2-cell *re-routes* one cohomology class to be killed. -/
theorem filling_step_0_to_1 :
    routeFilling 0 1 = routeFilling 1 1 + 1 := by decide
theorem filling_step_1_to_2 :
    routeFilling 1 1 = routeFilling 2 1 + 1 := by decide
theorem filling_step_2_to_3 :
    routeFilling 2 1 = routeFilling 3 1 + 1 := by decide

/-- Routes diverge at degree 1, but agree at degrees 0 and ≥ 2:
    the cell-filling re-routes ONLY the H¹ trajectory, not the
    others.  in route language. -/
theorem filling_localised_at_degree_1 :
    routesAgree    (routeFilling 0) (routeFilling 3) 0 = true
    ∧ routesDiverge (routeFilling 0) (routeFilling 3) 1 = true
    ∧ routesAgree   (routeFilling 0) (routeFilling 3) 2 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! §5  Cross-bridge: BL route-pair gives the SAME pattern as
    Galois route-pair on the trajectory's "fixed indicator count".

    BL extreme (q = 5): motivic = étale at every p ∈ 0..5 ⇒ no re-route
    Galois extreme (full lattice): both routes touch all 6 strata.
    BL boundary (q = 0): motivic re-routes at p ≥ 1.
    Galois boundary (σ-fixed): Galois re-routes at strata 1..4. -/

theorem BL_no_reroute_at_q5 :
    routesAgree (routeBL_motivic 5) (routeBL_etale 5) 0 = true
    ∧ routesAgree (routeBL_motivic 5) (routeBL_etale 5) 5 = true := by
  refine ⟨?_, ?_⟩ <;> decide

theorem BL_full_reroute_at_q0 :
    routesAgree    (routeBL_motivic 0) (routeBL_etale 0) 0 = true
    ∧ routesDiverge (routeBL_motivic 0) (routeBL_etale 0) 1 = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-! §6  ★★★★★ capstone — STRICT ∅-AXIOM by decide.

    Three families of route-pairs on the same Δ⁴ + K_{3,2}^{(c=2)}
    lattice, each demonstrating the trajectory-routing framing
    of "phase".  No jumps, no limits — only re-routing at
    parameter changes. -/

theorem phase_routing_capstone :
    -- BL re-routing at p = q+1 (sharp boundary)
    routesAgree    (routeBL_motivic 2) (routeBL_etale 2) 2 = true
    ∧ routesDiverge (routeBL_motivic 2) (routeBL_etale 2) 3 = true
    -- BL "no re-route" at maximal twist q = 5
    ∧ routesAgree (routeBL_motivic 5) (routeBL_etale 5) 4 = true
    -- Galois route coexistence (different where σ has no fixed atom)
    ∧ routeSum routeFull   5 = 32
    ∧ routeSum routeGalois 5 = 2
    ∧ routesDiverge routeFull routeGalois 2 = true
    ∧ routesAgree   routeFull routeGalois 0 = true
    ∧ routesAgree   routeFull routeGalois 5 = true
    -- K_{3,2} cell-filling family: 4 routes coexist
    ∧ routeFilling 0 1 = 8 ∧ routeFilling 1 1 = 7
    ∧ routeFilling 2 1 = 6 ∧ routeFilling 3 1 = 5
    -- Cell-filling re-route is localised at degree 1
    ∧ routesAgree   (routeFilling 0) (routeFilling 3) 0 = true
    ∧ routesDiverge (routeFilling 0) (routeFilling 3) 1 = true
    ∧ routesAgree   (routeFilling 0) (routeFilling 3) 2 = true
    -- Trajectory invariants (route sums) match the Beilinson L-values
    ∧ routeSum routeFull 5 = zetaΔ 5 0
    ∧ routeSum routeGalois 5 = fixedCount := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.HodgeConjecture.Bridge.PhaseRouting
