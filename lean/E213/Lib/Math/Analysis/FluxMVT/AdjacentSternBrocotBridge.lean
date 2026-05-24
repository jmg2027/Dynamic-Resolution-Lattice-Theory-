import E213.Lib.Math.Analysis.FluxMVT.TelescopingConservation
import E213.Lib.Math.Real213.Mobius213SternBrocot

/-!
# AdjacentSternBrocotBridge — Adjacent ⇒ sternBrocotEq on walls

`Adjacent db₀ db₁` (`Analysis/FluxMVT/TelescopingConservation`)
gives function equality at the shared wall:
`db₀.rightCut = db₁.leftCut` (`adjacent_walls_match`).  Function
equality immediately implies pointwise equality, hence
Stern-Brocot equivalence on the wall cuts.  This file records
the one-line corollary so that the bracket-adjacency reading of
the canonical equivalence is explicit.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Analysis.FluxMVT.AdjacentSternBrocotBridge

open E213.Lib.Math.Analysis.FluxMVT.TelescopingConservation
  (Adjacent adjacent_walls_match)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Real213.Mobius213SternBrocot
  (sternBrocotEq sternBrocotEq_refl)

/-- ★★ **Adjacency ⇒ Stern-Brocot equivalence on walls**:
    adjacent dyadic brackets share a wall as a function, and
    function equality implies Stern-Brocot equivalence (reflexive
    along the shared cut).  The DyadicBracket adjacency reading
    of the canonical Möbius-orbit equivalence. -/
theorem adjacent_walls_sternBrocotEq
    {db₀ db₁ : DyadicBracket} (h : Adjacent db₀ db₁) :
    sternBrocotEq db₀.rightCut db₁.leftCut := by
  rw [adjacent_walls_match h]
  exact sternBrocotEq_refl _

/-- ★ Pointwise equality form (subsumed by function equality
    from `adjacent_walls_match`, but recorded for direct cite). -/
theorem adjacent_walls_pointwise_eq
    {db₀ db₁ : DyadicBracket} (h : Adjacent db₀ db₁)
    (m k : Nat) :
    db₀.rightCut m k = db₁.leftCut m k := by
  rw [adjacent_walls_match h]

end E213.Lib.Math.Analysis.FluxMVT.AdjacentSternBrocotBridge
