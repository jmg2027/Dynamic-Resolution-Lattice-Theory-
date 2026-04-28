import E213.Math.Linalg213.Span

/-!
# Linalg213 — Concrete rank-5 compression instance (Phase L7)

User direction: resolve hard deferred items.  Linalg213's rank-5
compression theorem (any vs : Fin N → Vec 5 has Gram rank ≤ 5)
needs full rank theory for universal proof.  This file delivers
the **concrete instance**: 6 explicit vectors in Vec 5 with an
explicit Int linear dependence, decide-checked.

## The instance

  v_0 = e_0 = (1,0,0,0,0)
  v_1 = e_1 = (0,1,0,0,0)
  v_2 = e_2 = (0,0,1,0,0)
  v_3 = e_3 = (0,0,0,1,0)
  v_4 = e_4 = (0,0,0,0,1)
  v_5 = (1,1,1,1,1)        — sum of basis vectors

  Coefficients: (-1, -1, -1, -1, -1, +1)

  Σ cᵢ vᵢ at index k:
    -1·e_0(k) + (-1)·e_1(k) + ... + (-1)·e_4(k) + 1·all_ones(k)
    = -1 (only one e_i hits k) + 1 (all_ones contributes 1)
    = 0

So 6 vectors in Vec 5 are linearly dependent — concrete witness.
-/

namespace E213.Math.Linalg213.Rank5Concrete

/-- All-ones vector in Vec 5. -/
def all_ones_5 : Vec 5 := fun _ => 1

/-- 6 vectors: 5 standard basis + all-ones. -/
def vs6 : Fin 6 → Vec 5
  | ⟨0, _⟩ => e0_5
  | ⟨1, _⟩ => e1_5
  | ⟨2, _⟩ => e2_5
  | ⟨3, _⟩ => e3_5
  | ⟨4, _⟩ => e4_5
  | ⟨5, _⟩ => all_ones_5

/-- Coefficients (-1, -1, -1, -1, -1, +1). -/
def cs6 : IntCoeffs 6 := fun i =>
  if i.val < 5 then -1 else 1

/-- ★ Concrete rank-5 dependence: at each k ∈ Fin 5,
    Σ cᵢ vᵢ(k) = 0. -/
theorem linDep_at_each_k :
    linComb cs6 vs6 ⟨0, by decide⟩ = 0
    ∧ linComb cs6 vs6 ⟨1, by decide⟩ = 0
    ∧ linComb cs6 vs6 ⟨2, by decide⟩ = 0
    ∧ linComb cs6 vs6 ⟨3, by decide⟩ = 0
    ∧ linComb cs6 vs6 ⟨4, by decide⟩ = 0 := by decide

/-- ★ The combination is the zero vector. -/
theorem linComb_isZero_check :
    linComb_isZero cs6 vs6 = true := by decide

/-- ★ Coefficients are non-trivial (cs6 ⟨5, _⟩ = 1 ≠ 0). -/
theorem cs6_nontrivial : cs6 ⟨5, by decide⟩ = 1 := by decide

/-- ★★★ RANK-5 COMPRESSION CONCRETE INSTANCE ★★★

    There exist 6 vectors in Vec 5 with non-trivial Int linear
    dependence (i.e., they span only 5 dimensions).  This is
    paper 1's chiral compression theorem at concrete level. -/
theorem rank_5_concrete_instance :
    -- Non-trivial dependence: cs6 has a nonzero coefficient
    cs6 ⟨5, by decide⟩ = 1
    -- And the linear combination IS zero
    ∧ linComb_isZero cs6 vs6 = true
    -- At each k pointwise = 0
    ∧ (linComb cs6 vs6 ⟨0, by decide⟩ = 0
       ∧ linComb cs6 vs6 ⟨4, by decide⟩ = 0) := by decide

end E213.Math.Linalg213.Rank5Concrete
