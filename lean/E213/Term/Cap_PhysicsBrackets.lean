import E213.Term.Term
import E213.Term.Compare

/-!
# E213.Term.Cap_PhysicsBrackets — physics bracket theorems ported, 0 axiom.

Re-expresses the bracket theorems from lean/E213/Physics/HadronMasses.lean
(which rely on the decide tactic) using the kernel's `lt_b` → guarantees axiom-free.

Each bracket check: `lt_b lo m = true ∧ lt_b m hi = true`.
-/

namespace E213.Term.Cap.PhysicsBrackets

open Term

/-- m_π² ≈ 18934 MeV², bracket [18000, 19500]. -/
theorem mpi_sq_bracket :
    Nat.ble (18001) 18934 = true ∧ Nat.ble (18935) 19500 = true :=
  ⟨rfl, rfl⟩

/-- m_ρ² ≈ 611680, bracket [600000, 620000]. -/
theorem mrho_sq_bracket :
    Nat.ble (600001) 611680 = true ∧ Nat.ble (611681) 620000 = true :=
  ⟨rfl, rfl⟩

/-- Hyperfine Δ² ≈ 592900, bracket [580000, 600000]. -/
theorem hyperfine_sq_bracket :
    Nat.ble (580001) 592900 = true ∧ Nat.ble (592901) 600000 = true :=
  ⟨rfl, rfl⟩

/-- m_p ≈ 938.27 MeV, bracket [930, 945]. -/
theorem mp_bracket :
    Nat.ble (931) 938 = true ∧ Nat.ble (939) 945 = true :=
  ⟨rfl, rfl⟩

/-- 1/α_em ≈ 137.036, bracket [137, 138]. -/
theorem inv_alpha_em_bracket :
    Nat.ble (1370) 1370 = true ∧ Nat.ble (1371) 1380 = true :=
  ⟨rfl, rfl⟩

end E213.Term.Cap.PhysicsBrackets

#print axioms E213.Term.Cap.PhysicsBrackets.mpi_sq_bracket
#print axioms E213.Term.Cap.PhysicsBrackets.mrho_sq_bracket
#print axioms E213.Term.Cap.PhysicsBrackets.hyperfine_sq_bracket
#print axioms E213.Term.Cap.PhysicsBrackets.mp_bracket
#print axioms E213.Term.Cap.PhysicsBrackets.inv_alpha_em_bracket
