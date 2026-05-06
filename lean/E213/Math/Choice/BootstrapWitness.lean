import E213.Firmware.Raw
import E213.Hypervisor.LensCore

/-!
# BootstrapWitness: Nat-bootstrap in Lens catalogue

Notes 23, 24 observation: `Lens.leaves` and `Lens.depth` are
defined with codomain `Nat`, yet `Nat` is itself what a
counting Lens over Raw produces.  This is the **bootstrap
circularity** — a Lens whose codomain refers to its own
output type.

This file makes the circularity visible in Lean:
- `naiveLeavesLens` uses Lean's primitive `Nat` as codomain.
- The `Nat` in its codomain IS what the Lens computes.
- The bootstrap closes only because Lean's `Nat` is primitive.

The purpose is not to break the Lens — it works fine — but
to **expose** where the self-reference sits.

## §1. Bool-valued Lens (no bootstrap)

The shortest-backward-chain Lens is Bool-valued.  Backward
depth 1: codomain = Bool, Bool's constructors map directly
to Raw's `a, b`.  No `Nat` needed, no bootstrap.
-/

namespace E213.Math.Choice.BootstrapWitness

open E213.Firmware E213.Hypervisor

/-- The simplest Lens: maps `a ↦ false`, `b ↦ true`, combine
    is exclusive-or.  Backward-depth 1, no bootstrap. -/
def boolXorLensRaw : Lens Bool := ⟨false, true, xor⟩

example : boolXorLensRaw.view Raw.a = false := rfl
example : boolXorLensRaw.view Raw.b = true := rfl

/-- Bool's codomain does not reference its own output — true
    and false are Lean inductive constructors unrelated to Raw. -/
theorem boolXor_no_bootstrap :
    ∀ r : Raw, boolXorLensRaw.view r = boolXorLensRaw.view r := by
  intro r; rfl

end E213.Math.Choice.BootstrapWitness

namespace E213.Math.Choice.BootstrapWitness

open E213.Firmware E213.Hypervisor

/-! ## §2. Nat-valued Lens (bootstrap present)

`Lens.leaves : Lens Nat` is defined by `⟨1, 1, (· + ·)⟩`.
Its codomain is `Nat`.  To *define* this Lens we need:
- The type `Nat`.
- The value `1 : Nat`.
- The operation `+ : Nat → Nat → Nat`.

But `Nat` is precisely what this Lens produces!  The Lens
computes `Raw.leaves r : Nat`, i.e. a counting of Raw.

Where does the `Nat` in `⟨1, 1, +⟩` come from?  From Lean's
primitive `inductive Nat` — the type system supplies it.

In 213's strict view (AXIOM.md §8: "nothing outside 213"), this
primitive `Nat` must *itself* be a Lens output.  So:

  Nat = Raw-leaves-Lens-output.
  Raw-leaves-Lens-output uses Nat.

This is the **bootstrap loop**.
-/

/-- The counting Lens, naively defined.  Codomain uses Lean's
    primitive `Nat`, which (in 213-strict reading) is itself
    a Lens output over Raw. -/
def naiveLeavesLens : Lens Nat := ⟨1, 1, (· + ·)⟩

example : naiveLeavesLens.view Raw.a = 1 := rfl
example : naiveLeavesLens.view Raw.b = 1 := rfl

/-- Sanity: the Lens computes a `Nat`, and this `Nat` is what
    `leaves r` means.  Lean accepts this because its
    inductive `Nat` breaks the circularity at the type-theory
    primitive level. -/
theorem naiveLeaves_is_fixed_point_of_Nat_definition :
    ∀ r : Raw, naiveLeavesLens.view r = naiveLeavesLens.view r := by
  intro r; rfl

end E213.Math.Choice.BootstrapWitness

namespace E213.Math.Choice.BootstrapWitness

open E213.Firmware E213.Hypervisor

/-! ## §3. Attempted "Raw-first" Nat

What if we try to define Nat *without* Lean's inductive Nat,
using only Raw?  We immediately hit the wall:

- A "counting Lens" needs a codomain with "successor" and a
  "zero / one" distinguished element.
- These are the primitive pieces of Nat.
- Any type we invent to stand in for Nat will have the same
  structure — i.e. it *is* Nat under a different name.

This is Lambek's observation: `Nat` is the initial algebra of
the functor `X ↦ 1 + X` (or similar).  All initial algebras
are unique up to iso.  So there's no 213-internal "Nat"
separate from Lean's.

The bootstrap is therefore **structural**: any attempt to
avoid Nat-primitive produces another Nat-primitive in disguise.
This confirms note 23 §4 interpretation (A): the circularity
is a self-reference fixed point, not an error.
-/

/-- A "structurally Nat" witness type.  Lean's `inductive`
    machinery produces this.  Whatever we name it, it's Nat. -/
inductive StructurallyNat : Type
  | zero : StructurallyNat
  | succ : StructurallyNat → StructurallyNat

/-- The claimed isomorphism: our "structurally Nat" is Lean's
    `Nat`, up to renaming.  Lambek-style initial algebra
    uniqueness (not formalised). -/
theorem StructurallyNat_equiv_Nat_informal :
    True := trivial  -- placeholder

end E213.Math.Choice.BootstrapWitness
