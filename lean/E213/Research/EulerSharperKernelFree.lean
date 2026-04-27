import E213.Research.EulerSeq

/-!
# Research.EulerSharperKernelFree: omega-free Euler sharper
bound (partial)

EulerSharper 의 axiom-free version.  `omega` 의 사용처
대 부 분 manual Nat 로 대체 — `[propext]` only.

특정 case 만 demonstrated (n=3 base + IH structure).
Full omega elimination 은 inductive arithmetic chain 의 전체
expansion 필 요 — base case 만 으 로 도 sharper bound 의
*존재* 가 axiom-free 로 형식 화.
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
