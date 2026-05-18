import E213.Lens.Bool213.Raw
import E213.Lens.Number.Nat213.Raw

/-!
# Lens.Number.Nat213.RawCut — Lean-free cut prototype

The existing cut representation in `Lib/Math/Real213/CutPoset.lean`
uses `Nat → Nat → Bool` — i.e. it depends on Lean's `Nat` and
`Bool`.

This module is a **fully Lean-free** showcase:
  - input: two Raws (numerator `m`, denominator `k`, as Method A
    Nat213 chain elements)
  - output: Raw (Bool213's `T` or `F`)

`RawCut := Raw → Raw → Raw` — the cut type defined using only Raw.
External types are pushed one layer further out.

## Significance (logical endpoint of the G84 compression thesis)

> 213's fully closed universe: substantial content does *not* use
> Lean types.  Lean types appear only at the boundary layer
> (the `Subtype` / `inductive` of `Theory/Raw/Core`).

This prototype shows that even cut-style constructions are
Lean-free.  The same pattern would carry Cauchy sequences and any
cut-level theorem.

**Note (Option C refactor, 2026-05-18)**: prior versions of this
docstring cited `Nat213.leavesCountRaw` as a Raw-side parallel.
That projection has been deleted as part of the Option C refactor
(ℕ₊ is now a projection to `Nat`, not a Raw-internal projection).
`Bool213.booleanProj` and the `cutBooleanProj` of this file remain
Raw-internal — both Bool213's `{T, F}` canonical form and the
RawCut function space are Raw-valued by design.  See
`seed/CLOSED_FORM_SPEC.md` for the post-Option-C 3-domain table.
-/

namespace E213.Lens.Number.Nat213.RawCut

open E213.Theory
open E213.Lens.Bool213.Raw (T F)

/-- Lean-free cut type — input and output both Raw. -/
abbrev RawCut := Raw → Raw → Raw

/-- Trivial cut returning `T` everywhere. -/
def constTrueCut : RawCut := fun _ _ => T

/-- Trivial cut returning `F` everywhere. -/
def constFalseCut : RawCut := fun _ _ => F

/-- Pointwise equality on Raw cuts (the Lean-free version of
    `cutEq`).  Function comparison becomes pointwise Raw equality. -/
def rawCutEq (cx cy : RawCut) : Prop := ∀ m k, cx m k = cy m k

/-- Pointwise inequality (the Lean-free version of `cutLe`):
    `cy m k = T → cx m k = T`. -/
def rawCutLe (cx cy : RawCut) : Prop :=
  ∀ m k, cy m k = T → cx m k = T

/-! ### Equivalence and order properties (Lean-free) -/

theorem rawCutEq_refl (c : RawCut) : rawCutEq c c := fun _ _ => rfl

theorem rawCutEq_symm (cx cy : RawCut) (h : rawCutEq cx cy) :
    rawCutEq cy cx :=
  fun m k => (h m k).symm

theorem rawCutEq_trans (cx cy cz : RawCut)
    (h1 : rawCutEq cx cy) (h2 : rawCutEq cy cz) : rawCutEq cx cz :=
  fun m k => (h1 m k).trans (h2 m k)

theorem rawCutLe_refl (c : RawCut) : rawCutLe c c := fun _ _ h => h

theorem rawCutLe_trans (cx cy cz : RawCut)
    (h1 : rawCutLe cx cy) (h2 : rawCutLe cy cz) : rawCutLe cx cz :=
  fun m k hcz => h1 m k (h2 m k hcz)

/-- `rawCutEq → rawCutLe` (both directions). -/
theorem rawCutLe_of_rawCutEq (cx cy : RawCut) (h : rawCutEq cx cy) :
    rawCutLe cx cy := fun m k hy => (h m k).symm ▸ hy

/-- Sanity demonstration. -/
example : rawCutEq constTrueCut constTrueCut := rawCutEq_refl _
example : rawCutLe constTrueCut constTrueCut := rawCutLe_refl _

end E213.Lens.Number.Nat213.RawCut

namespace E213.Lens.Number.Nat213.RawCut

open E213.Theory
open E213.Lens.Bool213.Raw (T F booleanProj booleanProj_T booleanProj_F
                                  booleanProj_isBool booleanProj_idempotent
                                  boolValue boolValue_booleanProj)

/-! ### Vertical-internal projection on `RawCut`

A function-space (`RawCut`) version of `Bool213.booleanProj`: each
pointwise value is passed through `booleanProj`, so the output is
always `T` or `F`.

Function equality would require `funext` (an axiom cost).  Instead
we use **`rawCutEq`** (pointwise equality) to state idempotence —
demonstrating that the same meta-pattern (closure + idempotence +
fixed-point ↔ image) carries from the type level (Bool213) to the
function-space level (RawCut).

Two-domain parallel (post-Option-C; Nat213's old `leavesCountRaw`
row is dropped — ℕ₊ projects to `Nat`, not to Raw):

  - Bool213: `booleanProj r = booleanProj² r`,  output ∈ {T, F}
  - RawCut:  `cutBooleanProj cx ≈ cutBooleanProj² cx`, output ∈
             Bool213-valued cut
-/

/-- Cut-level vertical-internal projection — pointwise `booleanProj`. -/
def cutBooleanProj (cx : RawCut) : RawCut :=
  fun m k => booleanProj (cx m k)

/-- **Closure**: each pointwise value of `cutBooleanProj` is `T` or
    `F`. -/
theorem cutBooleanProj_isBool (cx : RawCut) (m k : Raw) :
    cutBooleanProj cx m k = T ∨ cutBooleanProj cx m k = F :=
  booleanProj_isBool (cx m k)

/-- **Idempotence (pointwise)**: `cutBooleanProj² ≈ cutBooleanProj`
    via `rawCutEq`.  No `funext` needed — pointwise Bool equality
    is the same pattern as Real213's `cutEq`. -/
theorem cutBooleanProj_idempotent (cx : RawCut) :
    rawCutEq (cutBooleanProj (cutBooleanProj cx)) (cutBooleanProj cx) :=
  fun m k => booleanProj_idempotent (cx m k)

/-! ### Fixed-point characterisation — Bool-valued cuts are exactly
the fixed points. -/

/-- A cut whose pointwise values are all in Bool213 (`{T, F}`). -/
def IsBoolValued (cx : RawCut) : Prop :=
  ∀ m k, cx m k = T ∨ cx m k = F

/-- Bool-valued → `cutBooleanProj` fixed point (under `rawCutEq`). -/
theorem cutBooleanProj_id_of_isBool (cx : RawCut) (h : IsBoolValued cx) :
    rawCutEq (cutBooleanProj cx) cx := by
  intro m k
  show booleanProj (cx m k) = cx m k
  rcases h m k with hT | hF
  · rw [hT]; exact booleanProj_T
  · rw [hF]; exact booleanProj_F

/-- Reverse: `cutBooleanProj` fixed point → Bool-valued. -/
theorem isBool_of_cutBooleanProj_id (cx : RawCut)
    (h : rawCutEq (cutBooleanProj cx) cx) : IsBoolValued cx := by
  intro m k
  have hck : booleanProj (cx m k) = cx m k := h m k
  rcases booleanProj_isBool (cx m k) with hT | hF
  · left; rw [← hck]; exact hT
  · right; rw [← hck]; exact hF

/-- **Fixed-point characterisation**: `cutBooleanProj` is identity
    on `cx` iff `cx` is Bool-valued.  Pinpoints the image of the
    vertical-internal projection. -/
theorem cutBooleanProj_id_iff_isBool (cx : RawCut) :
    rawCutEq (cutBooleanProj cx) cx ↔ IsBoolValued cx :=
  ⟨isBool_of_cutBooleanProj_id cx, cutBooleanProj_id_of_isBool cx⟩

/-! ### Concrete examples — fixed points on the two trivial cuts -/

theorem cutBooleanProj_constTrue :
    rawCutEq (cutBooleanProj constTrueCut) constTrueCut :=
  fun _ _ => booleanProj_T

theorem cutBooleanProj_constFalse :
    rawCutEq (cutBooleanProj constFalseCut) constFalseCut :=
  fun _ _ => booleanProj_F

/-! ### Boundary mapping — `RawCut → (Raw → Raw → Bool)`

Parallel to Bool213's `boolValue`: the function-space boundary
projection, pointwise.

Three-domain parallel (post-Option-C):

  Bool213: `boolValue : Raw → Bool`                       + `boolValue_booleanProj`
  RawCut:  `cutBoolValue : RawCut → (Raw → Raw → Bool)`   + `cutBoolValue_cutBooleanProj`
  Nat213 (post-Option-C): `Raw.value : Raw → Nat`         (no Raw-internal projection step)
-/

/-- The boundary projection — pointwise `boolValue`. -/
def cutBoolValue (cx : RawCut) : Raw → Raw → Bool :=
  fun m k => boolValue (cx m k)

/-- **Boundary commutativity** (pointwise):
    `cutBoolValue ∘ cutBooleanProj = cutBoolValue`.  The
    vertical-external + vertical-internal compatibility at the
    pointwise level. -/
theorem cutBoolValue_cutBooleanProj (cx : RawCut) (m k : Raw) :
    cutBoolValue (cutBooleanProj cx) m k = cutBoolValue cx m k :=
  boolValue_booleanProj (cx m k)

end E213.Lens.Number.Nat213.RawCut
