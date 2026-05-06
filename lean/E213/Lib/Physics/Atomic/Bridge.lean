import E213.Lib.Physics.Atomic.Hydrogen
import E213.Lib.Physics.Atomic.Screening

/-!
# Atomic structure ↔ Diamond bridge

Atomic structure (Bohr radii, screening σ) factors through
atomic primitives.

Per `Physics/HydrogenAtom.lean`:
  Bohr denom = NT = 2 (the "2" in n²·a_0)
  n=1 prefactor = NT·1·1 = 2
  n=2 prefactor = NT·2·2 = 8

Per `Physics/AtomicScreening.lean`:
  σ_1s = 7/8 (universal for K-shell)
  σ_p2 = NS/(NS+1) = 3/4
  σ_p3 = NT/(NT+1) = 2/3
-/

namespace E213.Lib.Physics.Atomic.Bridge

/-- Bohr denom = NT = 2. -/
theorem bohr_atomic :
    E213.Lib.Physics.Atomic.Hydrogen.bohr_denom = 2 := by decide

/-- n=1 hydrogen prefactor = NT·1² = 2. -/
theorem n1_atomic :
    E213.Lib.Physics.Atomic.Hydrogen.n1_prefactor_denom = 2 := by decide

/-- n=2 hydrogen prefactor = NT·2² = 8. -/
theorem n2_atomic :
    E213.Lib.Physics.Atomic.Hydrogen.n2_prefactor_denom = 8 := by decide

/-- σ_p2 screening = NS/(NS+1) = 3/4. -/
theorem sigma_p2_atomic :
    E213.Lib.Physics.Atomic.Screening.sigma_p2_num = 3
    ∧ E213.Lib.Physics.Atomic.Screening.sigma_p2_den = 4 := by decide

/-- σ_p3 screening = NT/(NT+1) = 2/3. -/
theorem sigma_p3_atomic :
    E213.Lib.Physics.Atomic.Screening.sigma_p3_num = 2
    ∧ E213.Lib.Physics.Atomic.Screening.sigma_p3_den = 3 := by decide

/-- ★★★ Atomic bridge capstone — Bohr + screening from
    NS, NT primitives. -/
theorem atomic_bridge_capstone :
    E213.Lib.Physics.Simplex.Counts.NS = 3
    ∧ E213.Lib.Physics.Simplex.Counts.NT = 2
    ∧ E213.Lib.Physics.Atomic.Hydrogen.bohr_denom = 2
    ∧ E213.Lib.Physics.Atomic.Hydrogen.n2_prefactor_denom = 8
    ∧ E213.Lib.Physics.Atomic.Screening.sigma_p2_num = 3
    ∧ E213.Lib.Physics.Atomic.Screening.sigma_p2_den = 4
    ∧ E213.Lib.Physics.Atomic.Screening.sigma_p3_num = 2 := by decide

end E213.Lib.Physics.Atomic.Bridge
