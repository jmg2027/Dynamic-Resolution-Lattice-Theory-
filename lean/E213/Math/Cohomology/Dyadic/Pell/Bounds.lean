import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM

/-!
# Concrete signature period bounds for Pell mod {2, 3}

Companion to `pellFSMmod5_signature_period_bound` (which gave bound 125).
Adds the smaller-modulus instances:

  - Pell mod 2: bound 5 · 4 = 20  (n = 2, n² = 4)
  - Pell mod 3: bound 5 · 9 = 45  (n = 3, n² = 9)

Pell family signature period table (TIGHT vs GUARANTEE):
  | mod | n² | TIGHT | guarantee 5n² |
  |  2  |  4 |   6   |     20       |
  |  3  |  9 |   4   |     45       |
  |  5  | 25 |  10   |    125       |
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★ Pell mod-2 signature period bound: 20 = 5·4. -/
theorem pellFSMmod2_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 20
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod2.bits (k + P) = signature pellFSMmod2.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 2) (by omega) pellFSMmod2
  exact ⟨N, P, hP, by omega, hk⟩

/-- ★★★★ Pell mod-3 signature period bound: 45 = 5·9. -/
theorem pellFSMmod3_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 45
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod3.bits (k + P) = signature pellFSMmod3.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 3) (by omega) pellFSMmod3
  exact ⟨N, P, hP, by omega, hk⟩

/-- ★★★★★ Pell family bound table — GUARANTEE row (5n²). -/
theorem pell_family_signature_period_bounds :
    (∃ N P, 0 < P ∧ N + P ≤ 20
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod2.bits (k + P) = signature pellFSMmod2.bits k)
    ∧ (∃ N P, 0 < P ∧ N + P ≤ 45
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod3.bits (k + P) = signature pellFSMmod3.bits k)
    ∧ (∃ N P, 0 < P ∧ N + P ≤ 125
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod5.bits (k + P) = signature pellFSMmod5.bits k) :=
  ⟨pellFSMmod2_signature_period_bound,
   pellFSMmod3_signature_period_bound,
   pellFSMmod5_signature_period_bound⟩

end E213.Math.Cohomology.Dyadic.Conjecture
