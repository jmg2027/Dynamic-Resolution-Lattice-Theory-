/-
  DRLT Elements — Phase 1-1: Entity (THE SOLE AXIOM)
  Joint research by Mingu Jeong and Claude (Anthropic)

  "Things exist with pairwise relations."
  Everything else is a corollary.

  This file also bootstraps kernel prerequisites (PUnit, Bool, PProd,
  Nat, sorryAx) needed by the Lean elaborator in prelude mode.
-/
prelude

universe u v w

-- ═══ Kernel bootstrap (needed by elaborator in prelude mode) ═══

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

abbrev Unit : Type := PUnit

inductive Bool : Type where
  | false : Bool
  | true : Bool

structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

axiom sorryAx (α : Sort u) (synthetic : Bool) : α

@[inline] def id {α : Sort u} (a : α) : α := a

@[inline] def Function.const {α : Sort u} (β : Sort v) (a : α) : β → α :=
  fun _ => a

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

-- ═══ THE SOLE AXIOM ═══
-- "존재하는 것들은 쌍 관계를 가진다"
inductive Entity : Type where
  | point : Entity
  | pair  : Entity → Entity → Entity

-- ═══ Equality ═══
-- Lean kernel does not provide Eq in prelude; define it.
inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

-- Eq theorems via recursor (no match → no extra deps)
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
