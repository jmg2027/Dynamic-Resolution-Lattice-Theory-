import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Physics.Atomic.Screening

/-!
# Phase 4 LithiumIE — Li IE atomic chain

## Standard formula

  IE(Li) = R · Z_eff² / n²

  Z_eff = Z - σ_inner = 3 - 2·σ_1s
  Z = NS = 3
  n = 2 (outer 2s electron)

## DRLT atomic chain

  σ_1s = 7/8 atomic (Phase 1 AtomicScreening, NS²-1-NS over NS²-1 reduced)
  σ_inner = 2·7/8 = 7/4
  Z_eff = 3 - 7/4 = 5/4 atomic
  n² = 4 = NT²

  IE(Li) = R · (5/4)² / NT² = R · 25/(16·4) = R · 25/64

## Numerical

  R = 13.605693 eV
  IE(Li) DRLT = R · 25/64 = 5.314 eV
  IE(Li) observed = 5.391715 eV
  Match: -1.4%

5/4 = (NS+NT)/(NS+1) = d/(NS+1) atomic.
25/64 = (d/(NS+1))² / (NT²) = d² / (16·NT²) atomic.

ppm precision: atomic refinement of σ_1s needed (Phase 5 work).
-/

namespace E213.Lib.Physics.Atomic.IE.Lithium

open E213.Lib.Physics.Simplex.Counts

/-- IE(Li) observed in μeV = 5391715. -/
def IE_Li_micro : Nat := 5391715

/-- IE(Li) DRLT = R · 25/64.  R_micro = 13605693.
    13605693 · 25 / 64 = 340142325 / 64 = 5314723. -/
def IE_Li_DRLT_micro : Nat := 5314723

/-- ★ Li IE atomic chain capstone.

  DRLT prediction vs measurement-Lens reading: differ by 76992
  μeV out of 5.4M = 1.4%.  Z_eff = 5/4 = d/(NS+1) atomic
  (cross-mult: d·4 = (NS+1)·5).  Leading ratio 25/64 = d²/(NT²·NT²)
  = d²/16. -/
theorem lithium_IE_atomic :
    (IE_Li_micro - IE_Li_DRLT_micro = 76992)
    ∧ (d * 4 = (NS + 1) * 5)
    ∧ (d * d * 16 = 25 * 16) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Atomic.IE.Lithium
