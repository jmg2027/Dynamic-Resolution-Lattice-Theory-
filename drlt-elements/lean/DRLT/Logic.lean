/-
  DRLT Elements — Phase 1-2: Logic (propositional logic)
  Joint research by Mingu Jeong and Claude (Anthropic)

  True, False, And, Or, Not, Iff, Exists, Decidable
  — all derived from Entity's universe, no tactics.
-/
prelude
import DRLT.Entity

universe u v

-- ═══ Propositional constants ═══
inductive True : Prop where
  | intro : True

inductive False : Prop
-- no constructors ⇒ unprovable

def False.elim {α : Sort u} (h : False) : α :=
  False.rec (fun _ => α) h

-- ═══ Connectives ═══
inductive And (a b : Prop) : Prop where
  | intro (left : a) (right : b) : And a b

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

def Not (a : Prop) : Prop := a → False

structure Iff (a b : Prop) : Prop where
  intro ::
  mp  : a → b
  mpr : b → a

-- ═══ Existential quantifier ═══
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

-- ═══ Decidability ═══
inductive Decidable (p : Prop) : Type where
  | isFalse : Not p → Decidable p
  | isTrue  : p → Decidable p
