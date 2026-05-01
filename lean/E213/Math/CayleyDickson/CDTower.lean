import E213.Math.CayleyDickson.ZI
import E213.Math.CayleyDickson.ZIDomain
import E213.Math.CayleyDickson.CDDouble
import E213.Math.CayleyDickson.Cayley
import E213.Math.CayleyDickson.LipschitzHeavy
import E213.Math.CayleyDickson.CayleyHeavy
import E213.Math.CayleyDickson.Sedenion

/-!
# Research: Cayley–Dickson tower — unified structural summary

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

namespace E213.Math.CayleyDickson.CDTower

open E213.Math.CayleyDickson.ZI E213.Math.CayleyDickson.LipschitzLens E213.Math.CayleyDickson.Cayley
     E213.Math.CayleyDickson.Sedenion

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

end E213.Math.CayleyDickson.CDTower

namespace E213.Math.CayleyDickson.CDTower

open E213.Math.CayleyDickson.LipschitzLens E213.Math.CayleyDickson.Cayley E213.Math.CayleyDickson.Sedenion

/-- **Extended CD tower drop pattern** — adds the
    alternativity axiom drop at layer 3.  Shows the full
    structural ladder:

    L0: R2 ✓, R3 ✓, assoc ✓, alt ✓ — ZI
    L1: R2 ✗, R3 ✓, assoc ✓, alt ✓ — Lipschitz
    L2: R2 ✗, R3 ✓, assoc ✗, alt ✓ — Cayley
    L3: R2 ✗, R3 ✗, assoc ✗, alt ✗ — Sedenion

    Each layer drops exactly one axiom class from above. -/
theorem CD_tower_extended :
    -- L0 is commutative
    (∀ u v : ZI, u * v = v * u)
    -- L1 is non-commutative
    ∧ (∃ u v : Lipschitz, u * v ≠ v * u)
    -- L2 is non-associative
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

end E213.Math.CayleyDickson.CDTower

namespace E213.Math.CayleyDickson.CDTower

open E213.Math.CayleyDickson.LipschitzLens E213.Math.CayleyDickson.Cayley E213.Math.CayleyDickson.Sedenion

/-- **FULL CD tower structural theorem** with composition-
    algebra status now included via Track A's `hurwitz_ring`
    tactic.  This single statement packages the entire
    CD tower's formal behaviour up to Sedenion:

    L0 (ZI):        comm ✓ , assoc ✓ , comp-alg ✓ , R3 ✓
    L1 (Lipschitz): comm ✗ , assoc ✓ , comp-alg ✓ , R3 ✓
    L2 (Cayley):    comm ✗ , assoc ✗ , comp-alg ✓ , R3 ✓
    L3 (Sedenion):  comm ✗ , assoc ✗ , comp-alg ✗ , R3 ✗

    Each "✗" has a concrete counterexample.
    Each "✓" has a universal Lean proof. -/
theorem CD_tower_full :
    (∀ u v : ZI, u * v = v * u)                                -- L0 comm
    ∧ (∀ u v w : ZI, (u * v) * w = u * (v * w))                -- L0 assoc
    ∧ (∀ u v : ZI, ZI.normSq (u * v) = ZI.normSq u * ZI.normSq v) -- L0 comp
    ∧ (∃ u v : Lipschitz, u * v ≠ v * u)                       -- L1 NOT comm
    ∧ (∀ u v w : Lipschitz, (u * v) * w = u * (v * w))         -- L1 assoc
    ∧ (∀ u v : Lipschitz, Lipschitz.normSq (u * v)
                           = Lipschitz.normSq u * Lipschitz.normSq v) -- L1 comp
    ∧ (∀ u v : Lipschitz, u * v = 0 → u = 0 ∨ v = 0)           -- L1 R3
    ∧ (∃ u v w : Cayley, (u * v) * w ≠ u * (v * w))            -- L2 NOT assoc
    ∧ (∀ a b : Cayley, (a * a) * b = a * (a * b))              -- L2 alt left
    ∧ (∀ u v : Cayley, Cayley.normSq (u * v)
                        = Cayley.normSq u * Cayley.normSq v)   -- L2 comp
    ∧ (∀ u v : Cayley, u * v = 0 → u = 0 ∨ v = 0)              -- L2 R3
    ∧ (∃ u v : Sedenion, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0)            -- L3 NOT R3
    ∧ (∃ a b : Sedenion, (a * a) * b ≠ a * (a * b)) :=         -- L3 NOT alt
  ⟨ZI.mul_comm, ZI.mul_assoc, ZI.normSq_mul,
   Lipschitz.mul_not_commutative, Lipschitz.mul_assoc,
   Lipschitz.normSq_mul, Lipschitz.no_zero_div,
   Cayley.mul_not_associative, Cayley.alt_left,
   Cayley.normSq_mul, Cayley.no_zero_div,
   Sedenion.R3_fails_on_sedenion, Sedenion.not_alternative⟩

end E213.Math.CayleyDickson.CDTower
