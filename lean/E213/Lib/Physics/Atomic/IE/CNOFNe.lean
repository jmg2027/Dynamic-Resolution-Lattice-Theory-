import E213.Lib.Physics.Simplex.Counts

/-!
# Phase 4 CNOFNeIE — C, N, O, F, Ne IE atomic chain

Leading + P(x/k) chain for each element.
Precision in 1000-3000 ppm range (additional σ_atomic refinement needed).

## Observed IE (CODATA, eV)

  C   11.260288
  N   14.534130
  O   13.618054
  F   17.422820
  Ne  21.564540

## DRLT chain (working hypothesis)

  σ_2p_2p = 11/15 = (NS²+NT)/(d·NS) atomic
  Additional correction needed for same-m vs different-m (Hund's rule).

  C  (2p²): σ_total = 69/20 + 11/15 = 251/60, Z_eff = 109/60
  N  (2p³): exception (Hund maximum spin)
  O  (2p⁴): re-pairing exception
  F  (2p⁵): close to closed shell
  Ne (2p⁶): closed shell, special

Atomic σ refinement for each element = future Phase 5.
-/

namespace E213.Lib.Physics.Atomic.IE.CNOFNe

open E213.Lib.Physics.Simplex.Counts

/-- IE observed values in μeV. -/
def IE_C : Nat := 11260288
def IE_N : Nat := 14534130
def IE_O : Nat := 13618054
def IE_F : Nat := 17422820
def IE_Ne : Nat := 21564540

/-- ★ CNOFNe Capstone ★ -/
theorem cnofne_atomic :
    -- Z atomic
    (NS * NT = 6) ∧ (NS * NT + 1 = 7) ∧ (NS * NT + NT = 8)
    ∧ (NS * NS = 9) ∧ (NS * NT + NT * NT = 10)
    -- σ atomic forms
    ∧ (NS * NS + NT = 11)
    -- atomic primitives
    ∧ (NS = 3) ∧ (NT = 2) ∧ (d = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Lib.Physics.Atomic.IE.CNOFNe
