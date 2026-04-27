import E213.Hypervisor.Lens

/-!
# Research.NoDepthParity: depth parity 는 Lens kernel 이 아니다

**관찰**: "depth r mod 2" 에 대한 equivalence relation 은 Raw
의 slash-congruence 가 **아님**.  따라서 어떤 Lens 도 depth
parity 를 정확히 추출하지 못함.

## 이유

`depth(slash x y h) = 1 + max(depth x)(depth y)`.  parity 는:

- depth x % 2, depth y % 2 만으로는 max(depth x, depth y)
  의 parity 를 결정할 수 없음.
- 예: (dx=1, dy=2) → max=2 → 1+2=3 odd.
       (dx=3, dy=2) → max=3 → 1+3=4 even.
  같은 parity 쌍 (odd, even) 이지만 결과 parity 가 다름.

## Witness

- `rA1`: depth 1 (odd).
- `rA3`: depth 3 (odd).
- `rB2`: depth 2 (even).

- ker_dp(rA1, rA3) (둘 다 odd).
- ker_dp(rB2, rB2) (자명).
- slash(rA1, rB2): depth 1 + max(1, 2) = 3 odd.
- slash(rA3, rB2): depth 1 + max(3, 2) = 4 even.

ker_dp 가 preserved 이려면 slash(rA1, rB2) ~ slash(rA3, rB2)
(둘 다 rA1~rA3, rB2~rB2).  하지만 실제는 odd vs even. 다름.
**slash-congruence 실패.**

따라서 depth parity 는 Lens 로 추출 불가.
-/

namespace E213.Research.NoDepthParity

open E213.Firmware E213.Hypervisor

/-- depth 1 witness: `a / b`. -/
def rA1 : Raw := Raw.slash Raw.a Raw.b (by decide)

/-- depth 2 witness: `a / (a/b)`. -/
def rB2 : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide)

/-- depth 3 witness: `a / (a / (a/b))`. -/
def rA3 : Raw :=
  Raw.slash Raw.a
    (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide))
    (by decide)

/-- slash (rA1, rB2) 은 depth 3 (odd). -/
def slash12 : Raw := Raw.slash rA1 rB2 (by decide)

/-- slash (rA3, rB2) 은 depth 4 (even). -/
def slash32 : Raw := Raw.slash rA3 rB2 (by decide)

theorem rA1_depth_odd : Lens.depth.view rA1 % 2 = 1 := by decide
theorem rA3_depth_odd : Lens.depth.view rA3 % 2 = 1 := by decide
theorem slash12_depth_odd : Lens.depth.view slash12 % 2 = 1 := by decide
theorem slash32_depth_even : Lens.depth.view slash32 % 2 = 0 := by decide

/-- **Depth parity 는 slash-congruence 가 아님**.  두 depth-odd
    원소 (rA1, rA3) 와 공통 rB2 에 대해 slash 결과의 parity 가
    다름. -/
theorem depth_parity_not_congruence :
    Lens.depth.view rA1 % 2 = Lens.depth.view rA3 % 2 ∧
    Lens.depth.view rB2 % 2 = Lens.depth.view rB2 % 2 ∧
    Lens.depth.view slash12 % 2 ≠ Lens.depth.view slash32 % 2 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · rfl
  · decide

end E213.Research.NoDepthParity
