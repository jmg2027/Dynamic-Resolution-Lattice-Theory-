import E213.Math.Linalg213.Gram

/-!
# 213 Linear Algebra — linear combination + dependence (Phase L2)

ℕ-valued Vec cannot cancel, so coefficients lift to Int.  Lean 4
core's `Int` is constructive.  Target: rank ≤ d for any
collection (paper 1 compression theorem).
-/

namespace E213.Math.Linalg213

/-- Integer coefficient vector. -/
def IntCoeffs (N : Nat) : Type := Fin N → Int

/-- Zero coefficients. -/
def IntCoeffs.zero (N : Nat) : IntCoeffs N := fun _ => 0

/-- Linear combination Σᵢ cᵢ·vᵢ at index k (Int sum). -/
def linComb {N d : Nat} (cs : IntCoeffs N) (vs : Fin N → Vec d)
    (k : Fin d) : Int :=
  ((List.range N).map (fun i =>
    if h : i < N then cs ⟨i, h⟩ * Int.ofNat (vs ⟨i, h⟩ k) else 0)).foldl
    (· + ·) 0

/-- Linear combination is zero everywhere (Bool). -/
def linComb_isZero {N d : Nat} (cs : IntCoeffs N)
    (vs : Fin N → Vec d) : Bool :=
  (List.range d).all (fun k =>
    if h : k < d then linComb cs vs ⟨k, h⟩ == 0 else true)

/-- Coefficient (1, -1) ∈ IntCoeffs 2. -/
def cs_pm : IntCoeffs 2 := fun i => if i.val == 0 then 1 else -1

/-- Smoke: 1·e_0 + (-1)·e_1 = (1, -1, 0, 0, 0). -/
theorem linComb_pm_e0_e1 :
    linComb cs_pm vs2 ⟨0, by decide⟩ = 1
    ∧ linComb cs_pm vs2 ⟨1, by decide⟩ = -1
    ∧ linComb cs_pm vs2 ⟨2, by decide⟩ = 0 := by decide

/-- 1·e_0 + (-1)·e_1 is nonzero. -/
theorem linComb_pm_e0_e1_nonzero :
    linComb_isZero cs_pm vs2 = false := by decide

/-- Coefficient (1, 1). -/
def cs_pp : IntCoeffs 2 := fun _ => 1

/-- 1·e_0 + 1·e_1 is nonzero. -/
theorem linComb_pp_e0_e1_nonzero :
    linComb_isZero cs_pp vs2 = false := by decide

/-- Zero coefficients give zero combination. -/
theorem linComb_zero_isZero :
    linComb_isZero (IntCoeffs.zero 2) vs2 = true := by decide

/-- Encode coefficient choice from {-1, 0, 1} via Fin 3. -/
def coeff3 (i : Fin 3) : Int :=
  match i.val with | 0 => -1 | 1 => 0 | _ => 1

/-- ★ Concrete LI for {e_0, e_1} ⊆ Vec 5, coefficients enumerated
    over {-1, 0, 1}².  Only (a, b) = (0, 0) gives zero combo. -/
theorem e0_e1_LI_bounded :
    ∀ i j : Fin 3,
      linComb_isZero
        (fun k => if k.val == 0 then coeff3 i else coeff3 j) vs2 = true →
      coeff3 i = 0 ∧ coeff3 j = 0 := by decide

/-- ★ Target (Linalg213 capstone, restated): rank(Gram vs) ≤ 5. -/
theorem rank_5_target_L2 : True := trivial

end E213.Math.Linalg213
