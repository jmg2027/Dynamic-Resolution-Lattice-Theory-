import E213.Hypervisor.Lens

/-!
# Research.KernelCongruence: Lens kernel 은 slash-congruence

**정리**: `L.equiv` 는 Raw 의 **slash-congruence** 이다 —
x ~ x' 이고 y ~ y' 이면 (slash 가 정의될 때) slash(x, y)
~ slash(x', y').

이는 Lens 의 kernel 이 "단순" equivalence 가 아니라 slash 와
compatible 한 equivalence 여야 함을 보여줌.

`NoDepthParity.lean` 의 negative 결과 (depth parity 는 slash-
congruence 아님) 의 positive 대응.

## 의의

모든 Lens kernel 이 congruence 이므로, "어떤 partition 이
Lens 로 실현 가능한가" 의 답은 "**slash-compatible partitions**".

이 정리 + `NoDepthParity` → Lens kernel 의 공간은 equivalence
space 의 **strict subset** (모든 equivalence 가 slash-compatible
은 아님).
-/

namespace E213.Research.KernelCongruence

open E213.Firmware E213.Hypervisor

/-- **Lens kernel congruence**: x ~ x' 이고 y ~ y' 이면
    slash-값들도 등가.  `hsym` 으로 AXIOM 수준 대칭성 요구. -/
theorem Lens.equiv_slash_congruence {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (x x' y y' : Raw) (hx : x ≠ y) (hx' : x' ≠ y')
    (hxx' : L.equiv x x') (hyy' : L.equiv y y') :
    L.equiv (Raw.slash x y hx) (Raw.slash x' y' hx') := by
  show L.view (Raw.slash x y hx) = L.view (Raw.slash x' y' hx')
  have hf1 : L.view (Raw.slash x y hx)
               = L.combine (L.view x) (L.view y) :=
    Raw.fold_slash _ _ _ hsym x y hx
  have hf2 : L.view (Raw.slash x' y' hx')
               = L.combine (L.view x') (L.view y') :=
    Raw.fold_slash _ _ _ hsym x' y' hx'
  rw [hf1, hf2]
  have hxx'' : L.view x = L.view x' := hxx'
  have hyy'' : L.view y = L.view y' := hyy'
  rw [hxx'', hyy'']

end E213.Research.KernelCongruence
