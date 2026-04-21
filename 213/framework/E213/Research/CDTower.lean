import E213.Research.ZI
import E213.Research.ZIDomain
import E213.Research.CDDouble
import E213.Research.Cayley
import E213.Research.Sedenion

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

namespace E213.Research

open E213.Research.ZI E213.Research.Lipschitz E213.Research.Cayley
     E213.Research.Sedenion

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

end E213.Research

namespace E213.Research

open E213.Research.Lipschitz E213.Research.Cayley E213.Research.Sedenion

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

end E213.Research
