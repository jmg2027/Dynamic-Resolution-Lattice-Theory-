import E213.Lib.Math.Cohomology.Cup.LeibnizLex

/-!
# Cup.LeibnizLexSelfRef — generalised self-referential Leibniz

Generalisation of `LeibnizLex.lex_cup_leibniz_forall_1_1`:

The boundary-endpoint correction `α(τ[0]) · β(τ[2])` at bidegree
(1, 1) is *not* an external term added to repair Leibniz — it IS
the lex-projection cup evaluated at the middle-removed face:

  α(τ[0]) · β(τ[2]) = (α ⌣ β)([τ[0], τ[2]]) = (α ⌣ β)(τ \ {τ[1]})

Hence the twisted Leibniz rewrites as a **self-referential** identity:

  δ(α ⌣ β)(τ) = (δα ⌣ β)(τ) ⊕ (α ⌣ δβ)(τ) ⊕ (α ⌣ β)(τ \ {τ[k]})

δ of (α ⌣ β) involves α ⌣ β *itself* evaluated at a shifted
argument.  Aligns perfectly with `seed/AXIOM/05_no_exterior.md` §5 — the operation's δ behaviour refers back to the operation's
own face values.

## General conjecture (∀ n, k, l)

For arbitrary bidegree (k, l) on Δⁿ⁻¹ and any (k+l+1)-subset τ:

  correction(α, β, τ) := (α ⌣ β)(τ \ {τ[k]})
  twisted_leibniz: δ(α⌣β)(τ) = δα⌣β(τ) ⊕ α⌣δβ(τ) ⊕ correction(α, β, τ)

The standard simplicial Leibniz captures the (k+l) face removals
at positions [0..k-1] (via δα) and [k+1..k+l] (via δβ); the missing
position-k face IS the correction, which is itself a cup value.

This file proves the (1, 1) case in self-referential form;
`LeibnizLex21.lean` (TBD) would extend to (2, 1).

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.LeibnizLexSelfRef

open E213.Lib.Physics.Simplex.Counts (binom d NS NT)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Cup.LeibnizLex

set_option maxHeartbeats 4000000

/-! ## §1.  Middle-removed face map at (1, 1) on Δ⁴

For each 3-subset τ ∈ Fin (binom 5 3), the middle-removed face
τ \ {τ[1]} is a 2-subset, indexed in Fin (binom 5 2).

Hardcoded from colex enumeration:

  3-subset i      τ \ {τ[1]}    2-subset colex idx
  ─────────────  ────────────  ──────────────────
  0  [0,1,2]     [0,2]         1
  1  [0,1,3]     [0,3]         3
  2  [0,2,3]     [0,3]         3
  3  [1,2,3]     [1,3]         4
  4  [0,1,4]     [0,4]         6
  5  [0,2,4]     [0,4]         6
  6  [1,2,4]     [1,4]         7
  7  [0,3,4]     [0,4]         6
  8  [1,3,4]     [1,4]         7
  9  [2,3,4]     [2,4]         8

Note Fin (binom 5 3) = Fin 10 and Fin (binom 5 2) = Fin 10 by Hodge
duality.  The map below collapses 10 → 10 with 7 distinct values. -/

/-- The middle-removed face map at (k, l, n) = (1, 1, 5).  Maps a
    3-subset's colex index to the colex index of its middle-removed
    2-subset (τ \ {τ[1]}). -/
def faceMiddleRemoved_5_1_1 (i : Fin (binom 5 3)) : Fin (binom 5 2) :=
  if i.val == 0 then ⟨1, by decide⟩
  else if i.val == 1 then ⟨3, by decide⟩
  else if i.val == 2 then ⟨3, by decide⟩
  else if i.val == 3 then ⟨4, by decide⟩
  else if i.val == 4 then ⟨6, by decide⟩
  else if i.val == 5 then ⟨6, by decide⟩
  else if i.val == 6 then ⟨7, by decide⟩
  else if i.val == 7 then ⟨6, by decide⟩
  else if i.val == 8 then ⟨7, by decide⟩
  else ⟨8, by decide⟩  -- i.val = 9: [2,3,4] → [2,4]

/-! ## §2.  Self-referential correction

The correction `α(τ[0]) · β(τ[2])` from `LeibnizLex.correction` is
recognised as `(α ⌣ β)` evaluated at the middle-removed face. -/

/-- Correction term as a cup self-reference.  PURE. -/
def correction_self_ref (α β : Fin (binom 5 1) → Bool)
    (i : Fin (binom 5 3)) : Bool :=
  cup 5 1 1 α β (faceMiddleRemoved_5_1_1 i)

/-- ★★ **Self-referential equivalence** — the boundary-endpoint
    correction equals the cup evaluated at the middle-removed face.
    Decide-verified across the 1024 (α, β) Bool-tuple parameters and
    10 face indices.  PURE. -/
theorem correction_eq_self_ref :
    ∀ (a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : Bool)
      (i : Fin (binom 5 3)),
      let α : Fin 5 → Bool := fun v =>
        if v.val = 0 then a₀
        else if v.val = 1 then a₁
        else if v.val = 2 then a₂
        else if v.val = 3 then a₃
        else a₄
      let β : Fin 5 → Bool := fun v =>
        if v.val = 0 then b₀
        else if v.val = 1 then b₁
        else if v.val = 2 then b₂
        else if v.val = 3 then b₃
        else b₄
      LeibnizLex.correction α β i = correction_self_ref α β i := by
  decide

/-! ## §3.  Self-referential Leibniz universal form

Substituting `correction = correction_self_ref` in `LeibnizLex
.lex_cup_leibniz_forall_1_1` yields the self-referential form.

The statement now reads:

  δ(α ⌣ β)(τ) = (δα ⌣ β)(τ) ⊕ (α ⌣ δβ)(τ) ⊕ (α ⌣ β)(face_k(τ))

i.e., δ of α⌣β at face τ is the standard Leibniz combination
*plus* the cup value at the middle-removed face τ \ {τ[k]}.  No
external correction term needed; just cup, δ, and the face map. -/

/-- ★★★ **Self-referential twisted Leibniz at (1, 1) on Δ⁴** —
    the cleanest 213-native form: the lex-projection cup's δ
    obeys a Leibniz rule whose "correction" is the cup itself
    at the middle-removed face.

      δ(α ⌣ β)(τ) = (δα ⌣ β)(τ) ⊕ (α ⌣ δβ)(τ) ⊕ (α ⌣ β)(face_1(τ))

    Aligns with §8 self-reference: the operation's δ refers back
    to the operation's own face values, no external term enters.
    PURE. -/
theorem lex_cup_leibniz_self_ref_1_1 :
    ∀ (a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : Bool)
      (i : Fin (binom 5 3)),
      let α : Fin 5 → Bool := fun v =>
        if v.val = 0 then a₀
        else if v.val = 1 then a₁
        else if v.val = 2 then a₂
        else if v.val = 3 then a₃
        else a₄
      let β : Fin 5 → Bool := fun v =>
        if v.val = 0 then b₀
        else if v.val = 1 then b₁
        else if v.val = 2 then b₂
        else if v.val = 3 then b₃
        else b₄
      delta (cup 5 1 1 α β) i
        = xor (xor (cup 5 2 1 (delta α) β i) (cup 5 1 2 α (delta β) i))
              (cup 5 1 1 α β (faceMiddleRemoved_5_1_1 i)) := by
  decide

end E213.Lib.Math.Cohomology.Cup.LeibnizLexSelfRef
