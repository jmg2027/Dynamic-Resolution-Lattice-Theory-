import E213.Math.Cohomology.CupAW.Core

/-!
# Cup AW — Bool-bilinearity (XOR distributes both sides)

cupAW(α + α', β) = cupAW(α, β) + cupAW(α', β)
cupAW(α, β + β') = cupAW(α, β) + cupAW(α, β')

Reduces to the Bool identity (a ⊕ b) ∧ c = (a∧c) ⊕ (b∧c).
Universally quantified over (n, a, b) — proved structurally,
not by enumeration.

This is the key lens that collapses Leibniz from O(2^N · 2^M)
case enumeration to ~N · M basis-pair cases.
-/

namespace E213.Math.Cohomology

open E213.Physics.Simplex.Counts (binom)

/-- Bool-level distributivity (left): (a ⊕ b) ∧ c = (a∧c) ⊕ (b∧c). -/
theorem Bool.and_xor_distrib_right (a b c : Bool) :
    ((a.xor b) && c) = ((a && c).xor (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Bool-level distributivity (right): a ∧ (b ⊕ c) = (a∧b) ⊕ (a∧c). -/
theorem Bool.and_xor_distrib_left (a b c : Bool) :
    (a && (b.xor c)) = ((a && b).xor (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- ★ cupAW is XOR-bilinear in the left argument. -/
theorem cupAW_add_left (n a b : Nat) (α α' : Cochain n a) (β : Cochain n b)
    (τ_idx : Fin (binom n (a + b - 1))) :
    cupAW n a b (Cochain.add α α') β τ_idx
      = xor (cupAW n a b α β τ_idx) (cupAW n a b α' β τ_idx) := by
  simp only [cupAW, Cochain.add]
  by_cases hf : subsetIdx n a ((kSubset n (a + b - 1) τ_idx.val).take a) < binom n a
  · by_cases hb : subsetIdx n b ((kSubset n (a + b - 1) τ_idx.val).drop (a - 1)) < binom n b
    · simp [hf, hb, Bool.and_xor_distrib_right]
    · simp [hf, hb]
  · simp [hf]

/-- ★ cupAW is XOR-bilinear in the right argument. -/
theorem cupAW_add_right (n a b : Nat) (α : Cochain n a) (β β' : Cochain n b)
    (τ_idx : Fin (binom n (a + b - 1))) :
    cupAW n a b α (Cochain.add β β') τ_idx
      = xor (cupAW n a b α β τ_idx) (cupAW n a b α β' τ_idx) := by
  simp only [cupAW, Cochain.add]
  by_cases hf : subsetIdx n a ((kSubset n (a + b - 1) τ_idx.val).take a) < binom n a
  · by_cases hb : subsetIdx n b ((kSubset n (a + b - 1) τ_idx.val).drop (a - 1)) < binom n b
    · simp [hf, hb, Bool.and_xor_distrib_left]
    · simp [hf, hb]
  · simp [hf]

/-- ★★★ Cup AW bilinearity capstone — both arguments distribute
    over XOR (Bool ℤ/2 sum). -/
theorem cupAW_bilinear_capstone (n a b : Nat)
    (α α' : Cochain n a) (β β' : Cochain n b)
    (τ_idx : Fin (binom n (a + b - 1))) :
    cupAW n a b (Cochain.add α α') β τ_idx
      = xor (cupAW n a b α β τ_idx) (cupAW n a b α' β τ_idx)
    ∧ cupAW n a b α (Cochain.add β β') τ_idx
      = xor (cupAW n a b α β τ_idx) (cupAW n a b α β' τ_idx) :=
  ⟨cupAW_add_left n a b α α' β τ_idx,
   cupAW_add_right n a b α β β' τ_idx⟩

end E213.Math.Cohomology
