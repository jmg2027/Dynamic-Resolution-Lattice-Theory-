import E213.Physics.Phase2
import E213.Physics.SimplexCounts

/-!
# Translation: SU(5) fermion content → DRLT atomic

Standard SM: 15+1 = 16 fermions per generation (1 = right-handed ν).
SU(5): 5̄ + 10 = 15 fermions + 1 sterile ν = 16.

DRLT atomic: 16 = NT^(d-1) = 2^4 atomic.

## fermion decomposition

  5̄ representation (5 fermions):
    quark d^c × NS = 3 (anti-down color)
    lepton e + ν_e = 2 = NT
    sum = 3 + 2 = NS + NT = d = 5 ✓

  10 representation (10 fermions):
    quark u × NS, d × NS = 6 = NS·NT
    quark u^c × NS = 3 = NS
    lepton e^c = 1
    sum = 6 + 3 + 1 = 10 = C(d, 2) ✓

  ★ 5 + 10 + 1 = 16 atomic ★
  16 = NT^(d-1) (atomic exponent d-1 = 4)
-/

namespace E213.Physics.Phase3.Translation.FermionContent

open E213.Physics.Simplex

/-- 5̄ representation count = d atomic. -/
theorem fermion_5bar : d = 5 := by decide

/-- 10 representation count = C(d, 2) = 10 atomic. -/
theorem fermion_10 : d * (d - 1) / 2 = 10 := by decide

/-- 16 = 5 + 10 + 1 atomic. -/
theorem fermion_16 : d + d * (d - 1) / 2 + 1 = 16 := by decide

/-- 16 = NT^(d-1) atomic exponent. -/
theorem sixteen_NT_d_minus_1 : NT * NT * NT * NT = 16 := by decide

/-- 16 = 2·8 = NT·(NS²-1) atomic. -/
theorem sixteen_atomic_alt : NT * (NS * NS - 1) = 16 := by decide

/-- ★ Fermion Content Capstone ★ -/
theorem fermion_content_atomic :
    (NS = 3) ∧ (NT = 2) ∧ (d = 5)
    -- 5̄ rep
    ∧ (d = 5)
    -- 10 rep = C(d, 2)
    ∧ (d * (d - 1) / 2 = 10)
    -- 16 fermion = 5 + 10 + 1
    ∧ (d + d * (d - 1) / 2 + 1 = 16)
    -- 16 = NT⁴
    ∧ (NT * NT * NT * NT = 16)
    -- 16 = NT·(NS²-1)
    ∧ (NT * (NS * NS - 1) = 16) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Phase3.Translation.FermionContent
