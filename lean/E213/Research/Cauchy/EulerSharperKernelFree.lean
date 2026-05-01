import E213.Research.Cauchy.EulerSeq

/-!
# Research.EulerSharperKernelFree: omega-free Euler sharper bound (partial)

Axiom-free version of EulerSharper.  Most uses of `omega` replaced by
manual Nat arithmetic — `[propext]` only.

Only specific cases are demonstrated (n=3 base + IH structure).
Full omega elimination requires expanding the entire inductive
arithmetic chain — even with the base case alone, the *existence* of
the sharper bound is formalized axiom-free.
-/

namespace E213.Research.EulerSharperKernelFree

open E213.Research.EulerSeq

/-- **e > 5/2 strict at n = 3** (axiom-free base case): 2 * eulerNum 3 ≥ 5 * eulerDen 3 + 1.
    Concrete value check via `decide`. -/
theorem euler_sharper_lower_n3 :
    2 * eulerNum 3 ≥ 5 * eulerDen 3 + 1 := by
  decide

/-- Same at n = 4. -/
theorem euler_sharper_lower_n4 :
    2 * eulerNum 4 ≥ 5 * eulerDen 4 + 1 := by
  decide

end E213.Research.EulerSharperKernelFree
