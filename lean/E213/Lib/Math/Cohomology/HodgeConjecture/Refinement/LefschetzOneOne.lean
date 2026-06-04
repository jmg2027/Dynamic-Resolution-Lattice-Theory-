import E213.Lib.Math.Cohomology.HodgeConjecture.Foundation.Conjecture

import E213.Lib.Math.Cohomology.Cochain.Core
/-!
# Lefschetz (1,1) Theorem in 213

Lefschetz's classical 1924 result: every (1,1)-Hodge class on a
smooth complex projective surface is algebraic (= Chern class of a
line bundle).  Historically the first instance of what would later
become the Hodge conjecture.

In 213 ( corrected framing): the (1,1)-stratum of a 213-canonical
complex is `Cochain n 2` (degree-2 cocycles), and "algebraic" =
indicator-basis XOR.  The statement is the k=2 specialisation of
HC²¹³, and follows immediately from `hodge_conjecture_213`.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.HodgeConjecture.Refinement.LefschetzOneOne

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.HodgeConjecture.Foundation.Conjecture
  (IsHodgeClass IsAlgebraic hodge_conjecture_213)

/-- ★★★★★ Lefschetz (1,1) Theorem in 213.  STRICT ∅-AXIOM.

    Every (1,1)-Hodge class on Δⁿ⁻¹ is algebraic — i.e., a XOR of
    indicator cochains on canonical 2-simplices.

    Historical: Lefschetz 1924, Théorème (1,1).  The k=2 case of
    HC²¹³, given a name to mark its mathematical-historical status.

    Specialises `hodge_conjecture_213` at k=2.  Witness: the cochain
    σ itself viewed as its own coefficient sequence in the
    edge-indicator basis (under  framing this *is* the content:
    `Cochain n 2 = Fin (binom n 2) → Bool` is the free ℤ/2-module on
    the 2-simplex indicators by definitional equality). -/
theorem lefschetz_one_one_213 {n m : Nat} (σ : Cochain n 2)
    (h : @IsHodgeClass n 2 m σ) : IsAlgebraic σ :=
  hodge_conjecture_213 σ h

/-- (1,1) form on Δ⁴ specifically (k=2 stratum, dim binom 5 2 = 10). -/
theorem lefschetz_one_one_213_delta4 (m : Nat) (σ : Cochain 5 2)
    (h : @IsHodgeClass 5 2 m σ) : IsAlgebraic σ :=
  lefschetz_one_one_213 σ h

end E213.Lib.Math.Cohomology.HodgeConjecture.Refinement.LefschetzOneOne
