import E213.Research.Real213Equiv

/-!
# Research.Real213Const: Real213 의 constant embedding (D3-A 후속)

`D3_real213_native_R.md` 의 D3-A 다음 단계 — Raw → Real213 의
embedding (constant Cauchy sequence).

## 정의

`Real213.const r` = 모든 index 에 서 r 를 출력 하 는 Cauchy
sequence + trivial modulus (N = 0).

## 의의

- Raw 의 element 가 Real213 에 *direct embed* (각 Raw 가 자기
  자신의 constant 으 로 ℝ-element 가 됨).
- `const r ~ const r'` ↔ orderProj m k 가 *모든* (m, k) 에 서
  agree — view (Nat × Nat) 의 ratio-equivalence.
- 이게 Real213 의 *최 소 한 의* element constructor.
-/

namespace E213.Research.Real213

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- Constant sequence at single Raw r. -/
def constSeq (r : Raw) : Nat → Raw := fun _ => r

/-- Constant sequence 의 trivial modulus — N = 0, cauchy_at trivial. -/
def constModulus (r : Raw) : HasModulus (constSeq r) where
  N := fun _ _ => 0
  cauchy_at := fun _ _ _ _ _ _ _ => rfl

/-- Real213 의 constant embedding: Raw → Real213. -/
def const (r : Raw) : Real213 :=
  ⟨constSeq r, constModulus r⟩

/-- Constant Real213 의 equivalence ↔ orderProj 가 모든 (m, k) 에 서 같 음. -/
theorem const_equiv_iff (r r' : Raw) :
    Real213.equiv (const r) (const r')
      ↔ ∀ m k, k ≥ 1 →
          orderProj m k (abLens.view r) = orderProj m k (abLens.view r') := by
  refine ⟨?_, ?_⟩
  · intro h m k hk
    obtain ⟨N, hN⟩ := h m k hk
    exact hN N (Nat.le_refl N)
  · intro h m k hk
    exact ⟨0, fun _ _ => h m k hk⟩

/-- const 가 자기 자신과 equivalent (trivial — equiv_refl 의 special case). -/
theorem const_equiv_self (r : Raw) : Real213.equiv (const r) (const r) :=
  equiv_refl (const r)

end E213.Research.Real213
