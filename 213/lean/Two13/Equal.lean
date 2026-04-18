/-
  Two13/Equal.lean — 같다: 구분 불가능

  두 것이 같다 := 구분할 수 없다.
  이것은 2(구분)의 부정이다.
  구분을 시도했으나 경계(1)만 남으면: 같다.

  213에서 = 은 231: 구분(2) → 재귀(3) → 경계만 남음(1).
-/
prelude
import Two13.Mark

universe u v

-- ═══ 같다 (=) ═══
-- 구분을 긋는 행위(2)를 적용했으나
-- 두 면이 동일하여 경계(1)만 남음.
-- Eq a a: a를 a에서 구분하면 — 구분 없음. 경계만.
inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

-- ═══ Eq의 성질들 ═══
-- 모든 증명은 @Eq.rec (커널 재귀자)로.
-- match를 쓰지 않는다 — match는 매체의 도구(PProd 의존).
-- Eq.rec은 구분(2)의 내재적 귀결이다.

-- 대칭: a=b이면 b=a. 구분 없음은 방향이 없다.
theorem Eq.symm {α : Sort u} {a b : α}
    (h : Eq a b) : Eq b a :=
  @Eq.rec α a (fun x _ => Eq x a) (.refl a) b h

-- 추이: a=b이고 b=c이면 a=c. 구분 없음의 연쇄.
theorem Eq.trans {α : Sort u} {a b c : α}
    (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  @Eq.rec α b (fun x _ => Eq a x) h₁ c h₂

-- 대입: a=b이면 a의 성질은 b의 성질. 구분 없으면 교환 가능.
theorem Eq.subst {α : Sort u} {a b : α} {p : α → Prop}
    (h : Eq a b) (hp : p a) : p b :=
  @Eq.rec α a (fun x _ => p x) hp b h

-- 합동: a=b이면 f(a)=f(b). 구분 없음은 변환을 통과.
theorem Eq.congr {α : Sort u} {β : Sort v} {a b : α}
    (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  @Eq.rec α a (fun x _ => Eq (f a) (f x)) (.refl (f a)) b h
