# 19 — Lens ≠ Functor (2026-04-24)

## The trap

Claude's training bias is strong on category theory.
When asked "what is a Lens?", the reflex answer is
"a functor from Raw (viewed as a category) to the target
category".  This reflex has already wasted multiple
sessions.  The error is not just imprecise language —
it silently re-founds Raw on category theory.

## Why it is wrong

A **functor** `F : C → D` requires:
- a source category `C` with objects + morphisms + id +
  composition;
- a target category `D` with the same;
- a map on objects `F_0 : ob C → ob D`;
- a map on morphisms `F_1 : hom_C(X,Y) → hom_D(F_0 X, F_0 Y)`;
- preservation of id and composition.

Raw has **no morphisms**.  It has no category structure.
To call a Lens a functor, one would first have to choose a
category structure on Raw — and that choice is already a
Lens.  The circularity: *"Lens is a functor"* presupposes
that Raw has been viewed through a category-Lens, which is
precisely what Lens is supposed to be general over.

## What a Lens actually is

From `framework/E213/Hypervisor/Lens.lean`:

```
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α

def Lens.view (L : Lens α) (r : Raw) : α :=
  r.fold L.base_a L.base_b L.combine
```

A Lens is:
1. A choice of two target values for the two primitive
   distinctions.
2. A binary operation on the target type.
3. The catamorphism-style fold that these induce.

That is all.  There is no morphism preservation, no source
category, no composition law (beyond `refines`, which is
a partial order on Lenses, not a category structure on
Raw).

## The pre-categorical position

Raw sits **below** the level at which category theory
becomes applicable.  Morphisms between Raw terms are not
part of the axiom; to speak of them, one must first choose
a Lens that defines them.  The relationship is:

```
Raw  ─────(Lens)────→  α
```

Lens is the arrow.  Category theory is a tool for studying
the targets `α` — not the source.  A functor-level
analysis only becomes meaningful once two Lenses are in
play and one asks whether they factor compatibly.

## What *is* fine category-theoretically

After Lens selection, downstream objects can be functorial:

- `CDDouble : R4Codomain A → R4Codomain (A × A)` is a
  doubling construction on Lens codomains.  In standard
  mathematics this is indeed a functor (between categories
  of normed rings with conjugation).  In 213 notes we
  call it a **"doubling construction"** or **"typeclass
  construction"** to keep the Lens / functor distinction
  visible, even though the construction itself is
  functorial.
- `Lens.refines` is a **partial order** (reflexive,
  transitive) on Lenses.  A partial order is a thin
  category, and one *could* study Lens refinement
  functorially — but the functor here lives at the
  meta-level (on Lenses), not between Raw and α.

## Rule of thumb

> If the thing you want to call a functor has Raw on
> either the source or the target side, stop.  Use
> "Lens", "observation", "view", or "fold" instead.
> If both endpoints are already Lens codomains (or
> Lens-catalogue meta-objects), "functor" is fine.

## Audit of existing text

Grep results (2026-04-24) before patching:

| File                         | Line | Issue                     |
|------------------------------|------|---------------------------|
| `PAPER.md`                   | 423  | "the Lens is a functor"   |
| `notes/03_cayley_dickson.md` | 63   | "functorial construction" |
| `notes/10_session4_cd_tower.md` | 84 | "CD … as a 'functor'"   |
| `notes/11_sedenion_r3_fail.md` | 100 | "CD Functor wrapper"    |
| `notes/13_master_summary.md` | 108  | "CDDouble functor"        |
| `infinity-as-lens/HANDOFF.md` | 56  | "CD `Functor`"            |

- PAPER.md:423 — direct Lens-is-functor claim.  **Patched
  in this arc.**
- Other entries refer to CDDouble which is not a Lens but
  a downstream construction.  Tone down to "doubling
  construction" for consistency, even though the strict
  category-theoretic usage is defensible there.

## Why this matters (sessions wasted)

HANDOFF already records: *"I had said Raw = initial
object in CommMagma — wrong framing (imports category
theory as prior).  Corrected: Raw IS the axiomatic
space; category theory is one possible Lens output."*

The correction has had to be re-applied in later sessions.
This note is the durable fix.
