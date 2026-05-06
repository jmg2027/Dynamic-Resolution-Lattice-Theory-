import E213.Lib.Math.Cauchy.WallisSeq

/-!
# WallisSharperKernelFree: Wallis sharper at concrete n
(axiom-free)

Axiom-free version of `WallisSharper` (concrete n).
Full omega-elimination from the inductive proof is expensive, but
verification at specific values is axiom-free via `decide`.
-/

namespace E213.Lib.Math.Cauchy.WallisSharperKernelFree

open E213.Lib.Math.Cauchy.WallisSeq

/-- W_2 = 64/45 (base of sharper bound, axiom-free). -/
theorem wallis_sharper_n2 : 45 * wallisNum 2 ≥ 64 * wallisDen 2 := by decide

/-- W_3 ≥ 64/45 (one step beyond base, axiom-free). -/
theorem wallis_sharper_n3 : 45 * wallisNum 3 ≥ 64 * wallisDen 3 := by decide

end E213.Lib.Math.Cauchy.WallisSharperKernelFree
