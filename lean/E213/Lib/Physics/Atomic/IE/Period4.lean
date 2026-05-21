import E213.Lib.Physics.Simplex.Counts

/-!
# Phase 4 Period4IE — Period 4 (K ~ Kr) atomic catalog

Period 4 = 18 elements (K to Kr, Z = 19-36).
Period 4 closure: Kr at Z = 36 = 6² = (NS·NT)² atomic.

## Z atomic forms

  K  (19) = NS³ - NT³ atomic (discovered in Phase 3)
  Ca (20) = 4·d atomic
  Sc (21) = NS·d + NS·NT atomic (= 15+6=21)
  Ti (22) = 2·d² - NT² + NT² ... or 22 = d²-NS atomic (= Cabibbo λ denom!)
  V  (23) = ? (no clean form)
  Cr (24) = d²-1 atomic (Phase 3)
  Mn (25) = d² atomic (Phase 3)
  Fe (26) = d²+1
  Co (27) = NS³ atomic
  Ni (28) = NS·d + NS·NT·NT - NT
  Cu (29) = ?
  Zn (30) = NS·NT·d atomic = 1/α_2 (Phase 3)
  Ga (31) = ?
  Ge (32) = NT^d = 2^5 atomic (Phase 3)
  As (33) = ?
  Se (34) = ?
  Br (35) = ?
  Kr (36) = (NS·NT)² atomic = 6² ★ Period 4 closure
-/

namespace E213.Lib.Physics.Atomic.IE.Period4

open E213.Lib.Physics.Simplex.Counts

/-- ★ Period 4 atomic Z chain (clean cases) — Z(K..Kr) atomic forms in
    {NS, NT, d} where they admit one; Period-4 size + closure identities.
    STRICT ∅-AXIOM. -/
theorem period4_atomic :
    -- Clean Z atomic forms for the 9 elements that admit one
    NS * NS * NS - NT * NT * NT = 19   -- K = NS³ − NT³
    ∧ 4 * d = 20                       -- Ca = 4d
    ∧ d * d - NS = 22                  -- Ti = d² − NS (= Cabibbo λ denom)
    ∧ d * d - 1 = 24                   -- Cr = d² − 1
    ∧ d * d = 25                       -- Mn = d²
    ∧ NS * NS * NS = 27                -- Co = NS³
    ∧ NS * NT * d = 30                 -- Zn = NS·NT·d (= 1/α_2)
    ∧ NT * NT * NT * NT * NT = 32      -- Ge = NT^d (= 2^5)
    ∧ (NS * NT) * (NS * NT) = 36       -- Kr = (NS·NT)² ★ Period 4 closure
    -- Period 4 size = 18 = 2·NS²
    ∧ 2 * NS * NS = 18
    -- Period 4 closure = Period 3 close + Period 4 size
    ∧ 18 + 18 = 36 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Atomic.IE.Period4
