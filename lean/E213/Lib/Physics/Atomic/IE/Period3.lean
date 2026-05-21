import E213.Lib.Physics.Simplex.Counts

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

namespace E213.Lib.Physics.Atomic.IE.Period3

open E213.Lib.Physics.Simplex.Counts

/-- IE values in 10⁻⁶ eV (μeV). -/
def IE_Na : Nat := 5139076
def IE_Mg : Nat := 7646235
def IE_Al : Nat := 5985768
def IE_Si : Nat := 8151683
def IE_P  : Nat := 10486686
def IE_S  : Nat := 10360010
def IE_Cl : Nat := 12967632
def IE_Ar : Nat := 15759610

/-- ★ Period 3 atomic Z chain — Z(Na..Ar) each expressed as a tight
    atomic form in {NS, NT, d}, plus the Ar = 2·NS² period-3 closing
    identity.  STRICT ∅-AXIOM. -/
theorem period3_atomic :
    -- Na = NS² + NT
    NS * NS + NT = 11
    -- Mg = 2·NS·NT
    ∧ 2 * NS * NT = 12
    -- Al = NS² + NT² (= F_7)
    ∧ NS * NS + NT * NT = 13
    -- Si = 3d − 1
    ∧ 3 * d - 1 = 14
    -- P = NS·d
    ∧ NS * d = 15
    -- S = NT⁴
    ∧ NT * NT * NT * NT = 16
    -- Cl = NS² + (NS² − 1)
    ∧ NS * NS + (NS * NS - 1) = 17
    -- Ar = 2·NS² (Period 3 closing)
    ∧ 2 * NS * NS = 18 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Atomic.IE.Period3
