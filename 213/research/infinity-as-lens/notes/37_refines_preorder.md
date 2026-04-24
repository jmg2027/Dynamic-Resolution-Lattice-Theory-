# 37 — Lens refines 의 preorder 구조: idLens ⊑ L ⊑ constLens

## 관점 전환

Note 34-36: 개별 Lens 의 data (diagonal, base) 분석.
이 노트: Lens **사이의 관계** — `Lens.refines` preorder.

## §1. Lens.refines 복습

Hypervisor/Lens.lean:

```
def Lens.refines L M := ∀ x y : Raw, L.equiv x y → M.equiv x y
```

`L.equiv x y := L.view x = L.view y` — L 이 유도하는 Raw
의 equivalence.  `L.refines M` iff `L.ker ⊆ M.ker` (L 의
kernel 이 M 보다 finer).

이는 Lens 들 위의 preorder.

## §2. Top / Bottom (Lean 확인)

`Research/LensLattice.lean`:

- **Bottom** (finest kernel): `idLens` — equiv 는 Raw 의 `=`.
  `idLens_refines_all : idLens.refines L` for every L.
- **Top** (coarsest kernel): `constLens e` — equiv 는 universal.
  `all_refine_constLens : L.refines (constLens e)` for every L.

모든 Lens 가 이 둘 사이에 위치.

## §3. Injectivity characterisation

`refines_idLens_iff_injective : L.refines idLens ↔ Function.Injective L.view`.

즉 **injective Lens = idLens 를 refine 하는 Lens**.  note 36
의 injective Lens 개념이 refines preorder 의 한 단면으로
재해석.

## §4. Constancy characterisation

`constLens_refines_iff_const : (constLens e).refines L ↔
∀ x y, L.view x = L.view y`.

즉 **constant Lens = constLens 로부터 refined 되는 Lens**.

## §5. 의의

Lens 세계는 preorder 로 조직화:

```
idLens (⊥)  ⊑  ...  ⊑  constLens e (⊤)
  injective             constant
   (ker = =)           (ker = Raw × Raw)
```

각 Lens 의 "경계" 는 그 kernel.  refines preorder 는 경계
크기의 순서:

- **세밀한 경계** (작은 kernel) ↔ idLens 쪽.
- **거친 경계** (큰 kernel) ↔ constLens 쪽.

note 34 §3 의 4분류 (collapse/idempotent/escalate/multiply)
는 diagonal 의 local 거동; 이 노트의 preorder 는 Lens 전체의
global 구조.  서로 독립적 조직 원리.

## §6. 열린 질문

- **Q37.1**: refines preorder 에 meet / join 이 있는가?
  두 Lens L, M 의 common refinement (둘 다 refine 하는 finest
  Lens) 존재?  concrete 구성 가능?
- **Q37.2**: 기존 Lens 카탈로그 (parityLens, leaves, depth,
  f9Lens, ...) 사이의 refines 관계는?  누가 누구를 refine?
- **Q37.3**: refines 의 대응물인 **quotient** Lens 개념 —
  equiv 에 의한 Raw/~ 의 canonical Lens?

## 변경 이력

- 2026-04-24: Lens refines preorder 의 top / bottom 명시.
  injective ↔ refines idLens, constant ↔ refined-by constLens.
  `Research/LensLattice.lean`.
