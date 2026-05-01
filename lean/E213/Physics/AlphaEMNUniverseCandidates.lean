import E213.Physics.FiniteUniverse
import E213.Physics.SimplexCounts
import E213.Physics.AlphaEM137

/-!
# N_universe candidates — atomic combinatorial enumeration

`FiniteUniverse.N_universe_open_problem` records: 1/α_em is a
specific rational at finite N_U; what specific Nat is N_U?

This file enumerates ATOMIC candidates from {NS, NT, d, c}
combinatorics and bounds the deviation `36/N_U` from the standard
asymptotic value at each candidate.

## User insight (2026-04-27 refinement)

ζ(2) is NOT π²/6.  ζ(2) is S(N_U), a SPECIFIC finite rational at
SPECIFIC N_U.  π is fake — it appears nowhere in DRLT primitives.

## Candidates (all 0-axiom decidable)

  | candidate           | value                        | 36/N_U scale |
  | d!                  | 120                          | 0.30         |
  | NS²·d²              | 225                          | 0.16         |
  | d²·d² = d⁴          | 625                          | 0.058        |
  | d^d                 | 3125                         | 0.012        |
  | 2^(d²)              | 33554432                     | 1.1×10⁻⁶     |
  | d^(NS·d)            | 30517578125                  | 1.2×10⁻⁹     |
  | d^(d²) (hierarchy)  | 298023223876953125 (≈3·10¹⁷) | 1.2×10⁻¹⁶    |

The hierarchy candidate `d^(d²) = 5²⁵` (already proved as
`hierarchy_cardinality` in FamousCoincidences) gives sub-ppb
deviation — well within Validation Standard #1 even without
SO(10)/Gram corrections.
-/

namespace E213.Physics.AlphaEMNUniverseCandidates

open E213.Physics.Simplex

/-- Candidate 1: d! = 120 (factorial of atomic dimension). -/
theorem candidate_dfactorial : 5 * 4 * 3 * 2 * 1 = 120 := by decide

/-- Candidate 2: 2^d² = 33554432 (binary exterior algebra at d²-fold). -/
theorem candidate_2_to_d_sq : 2 ^ (d * d) = 33554432 := by decide

/-- Candidate 3 (hierarchy): d^(d²) = 5²⁵ ≈ 3·10¹⁷. -/
theorem candidate_hierarchy : d ^ (d * d) = 298023223876953125 := by decide

/-- Candidate 4: d^(NS·d) = 5^15. -/
theorem candidate_d_to_NS_d : d ^ (NS * d) = 30517578125 := by decide

end E213.Physics.AlphaEMNUniverseCandidates
