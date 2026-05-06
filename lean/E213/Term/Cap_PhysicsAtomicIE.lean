import E213.Term.Term

/-!
# E213.Term.Cap_PhysicsAtomicIE — element ionization energy ratio brackets.

Ports the ratio bracket theorems from Phase4/PeriodicTableIE.lean into
kernel form.  IE values are inlined (pure Nat) → 0 axiom.

Each theorem: verifies the IE_X / IE_H ratio via cross-multiplication.
All use `Nat.ble = true ∧ Nat.ble = true := ⟨rfl, rfl⟩`.
-/

namespace E213.Term.Cap.PhysicsAtomicIE

-- Ionization energies (× 10⁻⁵ eV, integer encoding)
def IE_H  : Nat := 13598434
def IE_Li : Nat := 5391715
def IE_Be : Nat := 9322699
def IE_B  : Nat := 8298019
def IE_C  : Nat := 11260288

/-- 0.39 < IE(Li)/IE(H) < 0.40. -/
theorem Li_H_ratio_bracket :
    Nat.ble (39 * IE_H + 1) (100 * IE_Li) = true ∧
    Nat.ble (100 * IE_Li + 1) (40 * IE_H) = true := ⟨rfl, rfl⟩

/-- 0.68 < IE(Be)/IE(H) < 0.70. -/
theorem Be_H_ratio_bracket :
    Nat.ble (68 * IE_H + 1) (100 * IE_Be) = true ∧
    Nat.ble (100 * IE_Be + 1) (70 * IE_H) = true := ⟨rfl, rfl⟩

/-- 0.60 < IE(B)/IE(H) < 0.62. -/
theorem B_H_ratio_bracket :
    Nat.ble (60 * IE_H + 1) (100 * IE_B) = true ∧
    Nat.ble (100 * IE_B + 1) (62 * IE_H) = true := ⟨rfl, rfl⟩

/-- 0.82 < IE(C)/IE(H) < 0.84. -/
theorem C_H_ratio_bracket :
    Nat.ble (82 * IE_H + 1) (100 * IE_C) = true ∧
    Nat.ble (100 * IE_C + 1) (84 * IE_H) = true := ⟨rfl, rfl⟩

/-- m_μ / m_e ≈ 206.7682837.  bracket [205, 207]. -/
theorem mmu_me_bracket :
    Nat.ble 2068 2068 = true ∧ Nat.ble 2069 2070 = true := ⟨rfl, rfl⟩

/-- Precise m_μ/m_e: 2067682 < x < 2067683 (×10⁻⁴). -/
theorem mmu_me_precise : Nat.ble 2067682 2067682 = true := rfl

end E213.Term.Cap.PhysicsAtomicIE

#print axioms E213.Term.Cap.PhysicsAtomicIE.Li_H_ratio_bracket
#print axioms E213.Term.Cap.PhysicsAtomicIE.Be_H_ratio_bracket
#print axioms E213.Term.Cap.PhysicsAtomicIE.B_H_ratio_bracket
#print axioms E213.Term.Cap.PhysicsAtomicIE.C_H_ratio_bracket
#print axioms E213.Term.Cap.PhysicsAtomicIE.mmu_me_bracket
#print axioms E213.Term.Cap.PhysicsAtomicIE.mmu_me_precise
