import E213.Lib.Math.Analysis.FluxMVT.FluxEquiv
import E213.Lib.Math.Real213.Sum.CutSumEq

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Core.CutPoset
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.FluxMVT.FluxCut
/-!
# FluxEquivOps
-2: flux operations respect cohomEquiv.

Operations on FluxCut all preserve the cohomEquiv Setoid structure
— functorial / well-defined modulo dyadic equivalence.

  neg_cohomEquiv      : a ≈ b → neg a ≈ neg b
  add_cohomEquiv      : a ≈ b ∧ c ≈ d → add a c ≈ add b d
  sub_cohomEquiv      : a ≈ b ∧ c ≈ d → sub a c ≈ sub b d
  ofCut_cohomEquiv    : cutEq c c' → ofCut c ≈ ofCut c'
-/

namespace E213.Lib.Math.Analysis.FluxMVT.FluxEquivOps

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut.FluxCut (add neg sub ofCut zero)
open E213.Lib.Math.Real213.Core.CutPoset (cutEq_refl)
open E213.Lib.Math.Analysis.FluxMVT.FluxEquiv.FluxCut (cohomEquiv)
open E213.Lib.Math.Real213.Sum.CutSumEq (cutSum_cutEq_both cutMul_cutEq_both)

namespace FluxCut

/-- Negation preserves cohomEquiv (orientation reversal functorial). -/
theorem neg_cohomEquiv (a b : FluxCut) (h : cohomEquiv a b) :
    cohomEquiv a.neg b.neg :=
  ⟨h.2, h.1⟩

/-- Addition preserves cohomEquiv pairwise (chain-group functoriality). -/
theorem add_cohomEquiv (a b c d : FluxCut)
    (hab : cohomEquiv a b) (hcd : cohomEquiv c d) :
    cohomEquiv (add a c) (add b d) :=
  ⟨cutSum_cutEq_both a.forward b.forward c.forward d.forward hab.1 hcd.1,
   cutSum_cutEq_both a.backward b.backward c.backward d.backward
     hab.2 hcd.2⟩

/-- Subtraction preserves cohomEquiv (composition of add + neg). -/
theorem sub_cohomEquiv (a b c d : FluxCut)
    (hab : cohomEquiv a b) (hcd : cohomEquiv c d) :
    cohomEquiv (sub a c) (sub b d) :=
  add_cohomEquiv a b c.neg d.neg hab (neg_cohomEquiv c d hcd)

/-- ofCut preserves cutEq → cohomEquiv (functorial embedding). -/
theorem ofCut_cohomEquiv (c c' : Nat → Nat → Bool) (h : cutEq c c') :
    cohomEquiv (ofCut c) (ofCut c') :=
  ⟨h, cutEq_refl _⟩

/-- zero ≈ ofCut (constCut 0 1) (definitional). -/
theorem zero_cohomEquiv_ofCut_zero :
    cohomEquiv zero (ofCut (constCut 0 1)) :=
  ⟨cutEq_refl _, cutEq_refl _⟩

/-- -2 capstone: flux operations form a Setoid-respecting algebra. -/
theorem flux_ops_capstone (a b c d : FluxCut)
    (hab : cohomEquiv a b) (hcd : cohomEquiv c d) :
    cohomEquiv a.neg b.neg
    ∧ cohomEquiv (add a c) (add b d)
    ∧ cohomEquiv (sub a c) (sub b d) :=
  ⟨neg_cohomEquiv a b hab,
   add_cohomEquiv a b c d hab hcd,
   sub_cohomEquiv a b c d hab hcd⟩

end FluxCut

end E213.Lib.Math.Analysis.FluxMVT.FluxEquivOps
