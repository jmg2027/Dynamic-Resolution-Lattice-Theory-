import E213.Research.Real213Order

/-!
# Research.Real213Sign: Real213 의 zero + constructive positivity (A5)

`E1_real213_analysis_roadmap.md` 의 Phase A5 milestone.

## 정의

- `zero : Real213 := const Raw.b` — Raw.b 의 abLens.view = (0, 1) =
  ratio 0/1 = 0.
- `positive r := lt zero r` — 0 < r 의 Bishop-style 형식.
- 직접 풀어 쓰면: ∃ m k, k ≥ 1 ∧ ∃ N, ∀ i ≥ N, view (r.xs i) 의
  orderProj m k = false (= r 가 m/k 보 다 크 다).  m = 0 도 허용
  (orderProj 0 k = false iff a-count ≥ 1).

## 의의

- LEM 부재 의 constructive positivity.
- "r > 0" 에 *explicit margin* m/k 가 evidence 로 attached.
- ZFC 의 r > 0 (set-theoretic) 와 다른 object — algorithm 적
  separation 요구.
-/

namespace E213.Research.Real213

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- **Real213 의 zero**: const Raw.b (abLens.view = (0, 1), ratio 0). -/
def zero : Real213 := const Raw.b

/-- **Real213 의 positivity**: 0 < r 의 Bishop-style. -/
def positive (r : Real213) : Prop := lt zero r

/-- **const Raw.a 의 positivity**: Raw.a (view = (1, 0)) 가 zero 보다 큼.
    Witness: m = k = 1.  orderProj 1 1 (0, 1) = true, orderProj 1 1 (1, 0) = false. -/
theorem const_a_positive : positive (const Raw.a) := by
  refine ⟨1, 1, Nat.le_refl 1, 0, fun i _ => ?_⟩
  refine ⟨?_, ?_⟩
  · show orderProj 1 1 (abLens.view Raw.b) = true
    rfl
  · show orderProj 1 1 (abLens.view Raw.a) = false
    rfl

end E213.Research.Real213
