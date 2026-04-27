import E213.Physics.SimplexCounts

/-!
# Phase 4 Period3IE — Period 3 (Na ~ Ar) IE atomic chain

★ pure 213 mode ★
Atomic primitives only, without borrowing standard quantum numbers.

## Z atomic forms (Period 3)

  Na (Z=11) = NS² + NT atomic
  Mg (Z=12) = 2·NS·NT atomic
  Al (Z=13) = NS² + NT² atomic (= F_7)
  Si (Z=14) = 2·d + d - 1 = 3d-1 atomic
  P  (Z=15) = NS·d atomic = 1/α_2 partial
  S  (Z=16) = NT⁴ atomic
  Cl (Z=17) = NS² + (NS²-1) atomic
  Ar (Z=18) = 2·NS² atomic

## Observed IE (eV, CODATA)

  Na  5.139076
  Mg  7.646235
  Al  5.985768
  Si  8.151683
  P  10.486686
  S  10.360010
  Cl 12.967632
  Ar 15.759610

## Period closure atomic integers

  Period 1: 2 = NT
  Period 2: 10 = ? (closing 2+8)
  Period 3: 18 = 2·NS² atomic ★ (Period 3 closes at Ar)

Each period closing = atomic integer (see Phase 3 MasterCatalog).
-/

namespace E213.Physics.Phase4.Period3IE

open E213.Physics.Simplex

/-- IE values in 10⁻⁶ eV (μeV). -/
def IE_Na : Nat := 5139076
def IE_Mg : Nat := 7646235
def IE_Al : Nat := 5985768
def IE_Si : Nat := 8151683
def IE_P  : Nat := 10486686
def IE_S  : Nat := 10360010
def IE_Cl : Nat := 12967632
def IE_Ar : Nat := 15759610

/-- Z atomic forms. -/
theorem Z_Na_atomic : NS * NS + NT = 11 := by decide
theorem Z_Mg_atomic : 2 * NS * NT = 12 := by decide
theorem Z_Al_atomic : NS * NS + NT * NT = 13 := by decide
theorem Z_Si_atomic : 3 * d - 1 = 14 := by decide
theorem Z_P_atomic : NS * d = 15 := by decide
theorem Z_S_atomic : NT * NT * NT * NT = 16 := by decide
theorem Z_Cl_atomic : NS * NS + (NS * NS - 1) = 17 := by decide
theorem Z_Ar_atomic : 2 * NS * NS = 18 := by decide

/-- Period 3 closes at Ar = 2·NS² atomic ★. -/
theorem period_3_close_atomic : 2 * NS * NS = 18 := by decide

end E213.Physics.Phase4.Period3IE
