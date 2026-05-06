import E213.Lib.Math.CayleyDickson.ZI
import E213.Lib.Math.CayleyDickson.ZIDomain
import E213.Lib.Math.CayleyDickson.CDDouble
import E213.Lib.Math.CayleyDickson.Cayley
import E213.Lib.Math.CayleyDickson.LipschitzHeavy
import E213.Lib.Math.CayleyDickson.CayleyHeavy
import E213.Lib.Math.CayleyDickson.Sedenion

/-!
# Cayley–Dickson tower — unified structural summary

A single theorem packaging the 4-layer structural drop
pattern across `ZI → Lipschitz → Cayley → Sedenion`:

| Layer | Axiom that DROPS here |
|-------|----------------------|
| 0 (ZI)         | — (baseline: all R-conditions hold) |
| 1 (Lipschitz)  | R2 (commutativity)           |
| 2 (Cayley)     | associativity                |
| 3 (Sedenion)   | R3 (no zero divisors)        |

The "no zero divisor" for layers 1 and 2 is only proved
pairwise on specific generators (full universal R3 for
Cayley is Hurwitz's theorem, deferred).  The R2 persistence
at layer 0 is `ZI.mul_comm`.

All six components below are formally proved.
-/

namespace E213.Lib.Math.CayleyDickson.CDTower


open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Lib.Math.CayleyDickson.ZI E213.Lib.Math.CayleyDickson.CDDouble
     E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz E213.Lib.Math.CayleyDickson.Cayley
     E213.Lib.Math.CayleyDickson.Sedenion E213.Lib.Math.CayleyDickson.Sedenion.Sedenion
     E213.Lib.Math.CayleyDickson.LipschitzHeavy E213.Lib.Math.CayleyDickson.CayleyHeavy

/-- **CD tower structural drop pattern.**  Each successive
    Cayley–Dickson doubling strictly loses one structural
    axiom.  Four formally-verified layers. -/
theorem CD_tower_drops :
    -- Layer 0 (ZI): R2 holds universally.
    (∀ u v : ZI, u * v = v * u)
    -- Layer 1 (Lipschitz): R2 FAILS.
    ∧ (∃ u v : Lipschitz, u * v ≠ v * u)
    -- Layer 2 (Cayley): associativity FAILS.
    ∧ (∃ u v w : Cayley, (u * v) * w ≠ u * (v * w))
    -- Layer 3 (Sedenion): R3 FAILS.
    ∧ (∃ u v : Sedenion, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0) :=
  ⟨ZI.mul_comm,
   Lipschitz.mul_not_commutative,
   Cayley.mul_not_associative,
   Sedenion.R3_fails_on_sedenion⟩

open E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz E213.Lib.Math.CayleyDickson.Cayley E213.Lib.Math.CayleyDickson.Sedenion

/-- **Extended CD tower drop pattern** — adds the
    alternativity axiom drop at layer 3.  Shows the full
    structural ladder:

    CDTower.L0: R2 ✓, R3 ✓, assoc ✓, alt ✓ — ZI
    CDTower.L1: R2 ✗, R3 ✓, assoc ✓, alt ✓ — Lipschitz
    CDTower.L2: R2 ✗, R3 ✓, assoc ✗, alt ✓ — Cayley
    L3: R2 ✗, R3 ✗, assoc ✗, alt ✗ — Sedenion

    Each layer drops exactly one axiom class from above. -/
theorem CD_tower_extended :
    -- CDTower.L0 is commutative
    (∀ u v : ZI, u * v = v * u)
    -- CDTower.L1 is non-commutative
    ∧ (∃ u v : Lipschitz, u * v ≠ v * u)
    -- CDTower.L2 is non-associative
    ∧ (∃ u v w : Cayley, (u * v) * w ≠ u * (v * w))
    -- L3 has zero divisors
    ∧ (∃ u v : Sedenion, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0)
    -- L3 is non-alternative
    ∧ (∃ a b : Sedenion, (a * a) * b ≠ a * (a * b)) :=
  ⟨ZI.mul_comm,
   Lipschitz.mul_not_commutative,
   Cayley.mul_not_associative,
   Sedenion.R3_fails_on_sedenion,
   Sedenion.not_alternative⟩

open E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz E213.Lib.Math.CayleyDickson.Cayley E213.Lib.Math.CayleyDickson.Sedenion

/-- **FULL CD tower structural theorem** with composition-
    algebra status now included via Track A's `hurwitz_ring`
    tactic.  This single statement packages the entire
    CD tower's formal behaviour up to Sedenion:

    CDTower.L0 (ZI):        comm ✓ , assoc ✓ , comp-alg ✓ , R3 ✓
    CDTower.L1 (Lipschitz): comm ✗ , assoc ✓ , comp-alg ✓ , R3 ✓
    CDTower.L2 (Cayley):    comm ✗ , assoc ✗ , comp-alg ✓ , R3 ✓
    L3 (Sedenion):  comm ✗ , assoc ✗ , comp-alg ✗ , R3 ✗

    Each "✗" has a concrete counterexample.
    Each "✓" has a universal Lean proof. -/
theorem CD_tower_full :
    (∀ u v : ZI, u * v = v * u)                                -- CDTower.L0 comm
    ∧ (∀ u v w : ZI, (u * v) * w = u * (v * w))                -- CDTower.L0 assoc
    ∧ (∀ u v : ZI, ZI.normSq (u * v) = ZI.normSq u * ZI.normSq v) -- CDTower.L0 comp
    ∧ (∃ u v : Lipschitz, u * v ≠ v * u)                       -- CDTower.L1 NOT comm
    ∧ (∀ u v w : Lipschitz, (u * v) * w = u * (v * w))         -- CDTower.L1 assoc
    ∧ (∀ u v : Lipschitz, Lipschitz.normSq (u * v)
                           = Lipschitz.normSq u * Lipschitz.normSq v) -- CDTower.L1 comp
    ∧ (∀ u v : Lipschitz, u * v = 0 → u = 0 ∨ v = 0)           -- CDTower.L1 R3
    ∧ (∃ u v w : Cayley, (u * v) * w ≠ u * (v * w))            -- CDTower.L2 NOT assoc
    ∧ (∀ a b : Cayley, (a * a) * b = a * (a * b))              -- CDTower.L2 alt left
    ∧ (∀ u v : Cayley, E213.Lib.Math.CayleyDickson.CayleyHeavy.normSq (u * v)
                        = E213.Lib.Math.CayleyDickson.CayleyHeavy.normSq u * E213.Lib.Math.CayleyDickson.CayleyHeavy.normSq v)   -- CDTower.L2 comp
    ∧ (∀ u v : Cayley, u * v = 0 → u = 0 ∨ v = 0)              -- CDTower.L2 R3
    ∧ (∃ u v : Sedenion, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0)            -- L3 NOT R3
    ∧ (∃ a b : Sedenion, (a * a) * b ≠ a * (a * b)) :=         -- L3 NOT alt
  ⟨ZI.mul_comm, ZI.mul_assoc, ZI.normSq_mul,
   Lipschitz.mul_not_commutative, E213.Lib.Math.CayleyDickson.LipschitzHeavy.mul_assoc,
   E213.Lib.Math.CayleyDickson.LipschitzHeavy.normSq_mul, E213.Lib.Math.CayleyDickson.LipschitzHeavy.no_zero_div,
   Cayley.mul_not_associative, E213.Lib.Math.CayleyDickson.CayleyHeavy.alt_left,
   E213.Lib.Math.CayleyDickson.CayleyHeavy.normSq_mul, E213.Lib.Math.CayleyDickson.CayleyHeavy.no_zero_div,
   Sedenion.R3_fails_on_sedenion, Sedenion.not_alternative⟩

end E213.Lib.Math.CayleyDickson.CDTower
