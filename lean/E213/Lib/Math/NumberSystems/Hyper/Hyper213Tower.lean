import E213.Lib.Math.NumberSystems.Hyper.Hyper213
import E213.Lens.Compose

/-!
# Hyper213Tower: Simultaneous capture of the Hyper213 × Lens tower

User insight: "Hyperreals or large axiom systems are
rather naturally absorbed into 213.  The real final boss is ℝ as
defined in ZFC itself."

This file simultaneously demonstrates the framework-internal capture
of two *large* axes:

- *Sequence-large* axis: Hyper213 = Nat → Raw (looser equivalence
  without a Cauchy modulus — Hyper213.lean).
- *Tower-large* axis: Lens^n α via lensHasDistinguishing
  (LensOnLens.lean — unbounded recursive self-application).

Both axes are framework-internal — Lens or sequence-of-Raw.
ZFC-style power-set construction is not a primitive of this
chart; large structure is built type-theoretically.

## Core statement

`HyperTower α n := Nat → (LensTower α n)` is a framework-internal type —
a simultaneous extension of both axes.  The *sum* of both *large*
directions of the framework also remains inside the framework.

## Significance

Working evidence for "all frameworks ... Lenses" in CLAUDE.md:
- Hyper-real-like is also a Lens (sequence + cofinite quotient).
- The Lens^n α tower is also a Lens (recursive instance).
- Their simultaneous construction is also a Lens (HyperTower).

ZFC's arbitrary-subset construction (Dedekind cuts) is not a primitive in 213's raw framework; the corresponding objects are reconstructed type-theoretically when needed.
-/

namespace E213.Lib.Math.NumberSystems.Hyper.Hyper213Tower

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Compose.OnLens
open E213.Lib.Math.NumberSystems.Hyper.Hyper213

/-- LensTower α n: n-fold lens-on-lens self-application. -/
def LensTower (α : Type) [HasDistinguishing α] : Nat → Type
  | 0 => α
  | n + 1 => Lens (LensTower α n)

/-- HasDistinguishing instance for LensTower α n — recursive.
    Category (A) classical-correspondence surface
    (`catalogs/correspondence-surface.md`): states that the tower carries
    the standard `HasDistinguishing` structure; `Quot.sound` enters via
    the Lens `combine` function-`=`.  Terminal (no 213-internal consumer). -/
def lensTowerHasDistinguishing (α : Type) [d : HasDistinguishing α] :
    (n : Nat) → HasDistinguishing (LensTower α n)
  | 0 => d
  | n + 1 => lensHasDistinguishing (LensTower α n)
              (d := lensTowerHasDistinguishing α n)

/-- HyperTower α n := Nat → LensTower α n.  Combining two axes. -/
def HyperTower (α : Type) [HasDistinguishing α] (n : Nat) : Type :=
  Nat → LensTower α n

/-- Cofinite equivalence of HyperTower — n-independent form. -/
def hyperTowerEquiv {α : Type} [HasDistinguishing α] {n : Nat}
    (xs ys : HyperTower α n) : Prop :=
  ∃ N, ∀ k, k ≥ N → xs k = ys k

/-- Reflexivity. -/
theorem hyperTower_refl {α : Type} [HasDistinguishing α] {n : Nat}
    (xs : HyperTower α n) : hyperTowerEquiv xs xs :=
  ⟨0, fun _ _ => rfl⟩

/-- Constant tower-hyper: LensTower α n element → constant sequence. -/
def constHyperTower {α : Type} [HasDistinguishing α] {n : Nat}
    (a : LensTower α n) : HyperTower α n := fun _ => a

end E213.Lib.Math.NumberSystems.Hyper.Hyper213Tower
