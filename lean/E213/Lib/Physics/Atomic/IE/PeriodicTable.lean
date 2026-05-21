import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Physics.Atomic.Screening

/-!
# Phase 4 PeriodicTableIE — H ~ Ne IE atomic catalog

CODATA observed ionization energies (eV):
  H   13.598434  (1s)
  He  24.587387  (1s)
  Li   5.391715  (2s)
  Be   9.322699  (2s)
  B    8.298019  (2p)
  C   11.260288  (2p)
  N   14.534130  (2p)
  O   13.618054  (2p)
  F   17.422820  (2p)
  Ne  21.564540  (2p)

DRLT atomic chain for each element:

  IE(Z, n, shell) = R · Z_eff² / n²
  Z_eff = Z - σ_atomic
  σ_atomic = atomic shell-specific ratio

This file: atomic integer representation + bracket for each element's observed IE.
-/

namespace E213.Lib.Physics.Atomic.IE.PeriodicTable

open E213.Lib.Physics.Simplex.Counts

/-! ## IE values in 10⁻⁶ eV (μeV) — atomic catalog -/

def IE_H  : Nat := 13598434
def IE_He : Nat := 24587387
def IE_Li : Nat := 5391715
def IE_Be : Nat := 9322699
def IE_B  : Nat := 8298019
def IE_C  : Nat := 11260288
def IE_N  : Nat := 14534130
def IE_O  : Nat := 13618054
def IE_F  : Nat := 17422820
def IE_Ne : Nat := 21564540

/-- ★ Periodic Table (H..Ne) atomic master — Z atomic forms in
    {NS, NT, d} (10 elements) + IE/IE(H) cross-mult ratio brackets
    (He, Li, Be, B, C).  STRICT ∅-AXIOM. -/
theorem periodic_table_atomic :
    -- Z atomic forms
    (1 : Nat) = 1                          -- H
    ∧ NT = 2                               -- He
    ∧ NS = 3                               -- Li
    ∧ NS + 1 = 4                           -- Be
    ∧ d = 5                                -- B
    ∧ NS * NT = 6                          -- C
    ∧ NS * NT + 1 = 7                      -- N
    ∧ NS * NT + NT = 8                     -- O
    ∧ NS * NS = 9                          -- F
    ∧ NS * NT + NT * NT = 10               -- Ne
    -- IE/IE(H) ratio brackets (cross-mult forms)
    -- 1.80 < IE(He)/IE(H) < 1.82
    ∧ (180 * IE_H < 100 * IE_He ∧ 100 * IE_He < 182 * IE_H)
    -- 0.39 < IE(Li)/IE(H) < 0.40
    ∧ (39 * IE_H < 100 * IE_Li ∧ 100 * IE_Li < 40 * IE_H)
    -- 0.68 < IE(Be)/IE(H) < 0.70
    ∧ (68 * IE_H < 100 * IE_Be ∧ 100 * IE_Be < 70 * IE_H)
    -- 0.60 < IE(B)/IE(H) < 0.62
    ∧ (60 * IE_H < 100 * IE_B ∧ 100 * IE_B < 62 * IE_H)
    -- 0.82 < IE(C)/IE(H) < 0.84
    ∧ (82 * IE_H < 100 * IE_C ∧ 100 * IE_C < 84 * IE_H) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  <;> decide

end E213.Lib.Physics.Atomic.IE.PeriodicTable
