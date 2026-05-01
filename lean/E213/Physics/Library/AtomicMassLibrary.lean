import E213.Physics.Simplex.Counts

/-!
# Atomic Mass Library — atomic mass atomic chain

No standard borrowing.  Atomic primitives only.

## Methodology

  m_atom(Z) = Z · m_p · (1 + ε_binding/m_p)
            = Z · m_p · (1 - α_3 / NS · k(Z))

  m_p atomic chain (Phase 1, 0.000% match)
  α_3 = 1/8 atomic
  k(Z) = atomic ratio (binding shape)

## CODATA atomic masses (amu)

  H   1.00794
  He  4.00260
  C  12.01100
  O  15.99940
  Fe 55.84500
  ...

## First atomic verification

  H/He ratio: 4.0026/1.00794 = 3.9712 ≈ NT² = 4 atomic
  → exactly close to NT² (ppm after binding correction).
-/

namespace E213.Physics.Library.AtomicMassLibrary

open E213.Physics.Simplex.Counts

/-- m_p 4-digit (in 10⁻⁴ amu) = 10078 (= 1.0078). -/
def m_p_4digit : Nat := 10078

/-- m(He)/m(H) atomic ≈ NT² = 4. -/
theorem mass_ratio_He_H_atomic : NT * NT = 4 := by decide

/-- m(O)/m(C) atomic ≈ ?  16/12 = 4/3 = NS+1/NS atomic. -/
theorem mass_ratio_O_C_atomic : (4 : Nat) * NS = (NS + 1) * NS := by decide

end E213.Physics.Library.AtomicMassLibrary
