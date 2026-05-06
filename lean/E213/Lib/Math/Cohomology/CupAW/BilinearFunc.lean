import E213.Lib.Math.Cohomology.CupAW.Bilinear
import E213.Lib.Math.Cohomology.Delta.Linear

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
/-!
# Function-level versions of bilinearity / linearity

The value-level lemmas `cupAW_add_left/right`, `delta_add` apply
at fixed `τ_idx`.  For rewriting INSIDE delta or cupAW (where
the inner cochain is treated as a function), we need
function-level (funext'd) versions.
-/

namespace E213.Lib.Math.Cohomology.CupAW.BilinearFunc

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.CupAW.Bilinear (cupAW_add_left cupAW_add_right)
open E213.Lib.Math.Cohomology.Delta.Linear (delta_add)


/-- Function-level cupAW left bilinearity. -/
theorem cupAW_add_left_eq (n a b : Nat)
    (α α' : Cochain n a) (β : Cochain n b) :
    cupAW n a b (Cochain.add α α') β
      = Cochain.add (cupAW n a b α β) (cupAW n a b α' β) := by
  funext τ_idx
  show cupAW n a b (Cochain.add α α') β τ_idx
    = xor (cupAW n a b α β τ_idx) (cupAW n a b α' β τ_idx)
  exact cupAW_add_left n a b α α' β τ_idx

/-- Function-level cupAW right bilinearity. -/
theorem cupAW_add_right_eq (n a b : Nat)
    (α : Cochain n a) (β β' : Cochain n b) :
    cupAW n a b α (Cochain.add β β')
      = Cochain.add (cupAW n a b α β) (cupAW n a b α β') := by
  funext τ_idx
  show cupAW n a b α (Cochain.add β β') τ_idx
    = xor (cupAW n a b α β τ_idx) (cupAW n a b α β' τ_idx)
  exact cupAW_add_right n a b α β β' τ_idx

/-- Function-level delta linearity. -/
theorem delta_add_eq (n k : Nat) (σ τ : Cochain n k) :
    delta (Cochain.add σ τ) = Cochain.add (delta σ) (delta τ) := by
  funext τ_idx
  show delta (Cochain.add σ τ) τ_idx = xor (delta σ τ_idx) (delta τ τ_idx)
  exact delta_add n k σ τ τ_idx

end E213.Lib.Math.Cohomology.CupAW.BilinearFunc
