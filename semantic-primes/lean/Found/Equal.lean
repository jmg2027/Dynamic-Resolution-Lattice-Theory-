/-
  Found/Equal.lean — 같다 (Equality from Distinction)

  Eq a b := a와 b를 구분할 수 없다.
  구분(2)의 부정이 동치(=)를 만든다.
-/
prelude
import Found.Exist

universe u v

-- ═══ EQUALITY: 구분 불가능 ═══
-- Two things are equal iff they cannot be distinguished.
-- This is an indexed inductive — needs PUnit (from 있다).
inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

-- All proofs via @Eq.rec (no match, no PProd dependency)
theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  @Eq.rec α a (fun x _ => Eq x a) (.refl a) b h

theorem Eq.trans {α : Sort u} {a b c : α}
    (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  @Eq.rec α b (fun x _ => Eq a x) h₁ c h₂

theorem Eq.subst {α : Sort u} {a b : α} {p : α → Prop}
    (h : Eq a b) (hp : p a) : p b :=
  @Eq.rec α a (fun x _ => p x) hp b h

theorem Eq.congr {α : Sort u} {β : Sort v} {a b : α}
    (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  @Eq.rec α a (fun x _ => Eq (f a) (f x)) (.refl (f a)) b h
