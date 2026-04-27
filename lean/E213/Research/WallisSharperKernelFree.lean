import E213.Research.WallisSeq

/-!
# Research.WallisSharperKernelFree: Wallis sharper at concrete n
(axiom-free)

`WallisSharper` 의 axiom-free version (concrete n).
Inductive proof full omega-elimination 은 비싼 일이지만,
specific value 의 verification 은 `decide` 로 axiom-free.
-/

namespace E213.Research.WallisSharperKernelFree

open E213.Research.WallisSeq

/-- W_2 = 64/45 (base of sharper bound, axiom-free). -/
theorem wallis_sharper_n2 : 45 * wallisNum 2 ≥ 64 * wallisDen 2 := by decide

/-- W_3 ≥ 64/45 (one step beyond base, axiom-free). -/
theorem wallis_sharper_n3 : 45 * wallisNum 3 ≥ 64 * wallisDen 3 := by decide

end E213.Research.WallisSharperKernelFree
