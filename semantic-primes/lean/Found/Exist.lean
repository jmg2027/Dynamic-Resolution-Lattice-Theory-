/-
  Found/Exist.lean — 의미소 1: 있다 (Existence) + 구분 (Distinction)

  Two semantic primes. Everything else is derived.
  Lean's kernel types are CONSEQUENCES, not assumptions.

  Joint research by Mingu Jeong and Claude (Anthropic)
-/
prelude

universe u v

-- ═══ SEMANTIC PRIME 1: 있다 ═══
-- Something is. The minimum: one thing, nothing more.
-- Lean's kernel calls this PUnit. That's not arbitrary —
-- the kernel needs existence because existence is foundational.
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

abbrev Unit : Type := PUnit

-- ═══ SEMANTIC PRIME 2: 구분 ═══
-- This is not that. The minimum distinction.
-- Lean's kernel calls this Bool. That's not arbitrary —
-- the kernel needs binary choice because distinction is foundational.
inductive Bool : Type where
  | false : Bool
  | true : Bool

-- ═══ CONSEQUENCES OF THE TWO PRIMES ═══
-- The elaborator needs these. We derive them from 있다 + 구분.

-- Pair: two things held together (구분 applied to container)
structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

-- Sorry: the gap between intention and proof (있다 without 구분)
axiom sorryAx (α : Sort u) (synthetic : Bool) : α

-- Identity: 있다 applied to itself (self-reference)
@[inline] def id {α : Sort u} (a : α) : α := a

-- Constancy: 있다 ignoring 구분 (existence independent of distinction)
@[inline] def Function.const {α : Sort u} (β : Sort v) (a : α) : β → α :=
  fun _ => a
