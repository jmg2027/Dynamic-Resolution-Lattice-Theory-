import E213.Lib.Math.Analysis.Cauchy.DepthOmegaTower
import E213.Lib.Math.Analysis.Cauchy.DepthCeilingResidue

/-!
# DepthHeightDiagonal — naming the whole `ω^r` height-tower escapes every finite height

`DepthOmegaTower` builds the `ω^r` ladder: the coordinate `Coord r` is well-founded for
every `r` (`coord_wf`), each layer multiplies the rank by `ω` (`coord_layer_dominates`),
and the sequence side is the `r`-fold exponential `expTower c r` (`expTower c (r+1) =
c^{expTower c r}`).  `DepthCeilingResidue` shows that *naming the act of raising the
ceiling* is a diagonalisation that escapes the sequence it summarises (`diag_not_in_seq`)
— the Cantor self-cover, the residue.

This file applies that diagonalisation to the **height index itself**.  The height-tower
is a two-argument family `heightTower c r n = expTower c r n` (height `r`, sequence index
`n`) — exactly the shape `diag` consumes.  Then:

  * `height_diagonal_escapes` — the diagonal `diag (heightTower c)` (naming "all the
    heights `ω^r` at once") is **not** any finite-height tower `expTower c r`.  Every
    attempt to name the whole `ω^r` ladder lands outside it, producing a new object one
    step beyond every finite height — the `ω^ω` ceiling, and naming *that* is the next
    step again.

This is the residue read at the scale of the tower's *height*: the `ω^r` ladder has no
top finite height, and naming the whole ladder is the same self-cover as
`DepthCeilingResidue`, one scale up.  It is the structural content of the frontier
*toward* `ε₀` — the open-ended "diagonalise the tower height" step — **not** a
construction of `ε₀` as an ordinal object (there is no `Ordinal` type here; the
classical ε₀ reading is exactly that, a reading).  `epsilon_direction` bundles the
`ω`-per-layer growth with the height-diagonal escape.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.DepthHeightDiagonal

open E213.Lib.Math.Analysis.Cauchy.DepthOmegaTower (expTower coord_layer_dominates coordLt Coord)
open E213.Lib.Math.Analysis.Cauchy.DepthCeilingResidue (diag diag_not_in_seq)

/-- The **height-tower** as a two-argument family: `heightTower c r n = expTower c r n`,
    the `r`-fold exponential tower at sequence index `n`.  Diagonalising it ranges over
    both the height `r` and the index `n`. -/
def heightTower (c : Nat) : Nat → Nat → Nat := fun r n => expTower c r n

/-- The diagonal value: naming "all heights at once" reads `expTower c r r + 1` at the
    diagonal point `r` — one above the height-`r` tower's own diagonal entry. -/
theorem heightTower_diag (c r : Nat) :
    diag (heightTower c) r = expTower c r r + 1 := rfl

/-- ★★★ **Naming the whole `ω^r` height-tower escapes every finite height.**  The
    diagonal `diag (heightTower c)` is not any finite-height tower `expTower c r`: for
    every `r`, `diag (heightTower c) ≠ heightTower c r`.  So referencing "all the heights
    at once" produces an object beyond every finite `ω^r` — the `ω^ω` ceiling — and
    naming it is the same Cantor self-cover (`diag_not_in_seq`) read at the height scale:
    the residue, the frontier toward `ε₀`. -/
theorem height_diagonal_escapes (c : Nat) :
    ∀ r, diag (heightTower c) ≠ heightTower c r :=
  diag_not_in_seq (heightTower c)

/-- ★★★ **The `ε₀`-direction.**  Two facts about the height-tower, bundled:

    1. each height layer multiplies the rank by `ω` (`coord_layer_dominates`): a larger
       leading coefficient outranks the entire lower tower, so the `ω^r` heights are
       strictly increasing without a top finite level;
    2. naming the whole height-ladder (the diagonal) escapes every finite height
       (`height_diagonal_escapes`): the `ω^ω` ceiling, the residue one scale up.

    The `ω^r` ladder has no top, and the act of naming the ladder reproduces the residue
    — the open-ended step *toward* `ε₀`.  (No `Ordinal` object is constructed; `ε₀` is
    the classical reading of this open-endedness.) -/
theorem epsilon_direction (c : Nat) :
    (∀ (r a : Nat) (p q : Coord r), coordLt (r+1) (a, p) (a+1, q))
    ∧ (∀ r, diag (heightTower c) ≠ heightTower c r) :=
  ⟨coord_layer_dominates, height_diagonal_escapes c⟩

/-! ## §2 — the chain is self-applying: the residue-chain is itself a residue-chain -/

/-- ★★★ **The diagonalisation applies to its own output.**  Collect the diagonals of
    any family-of-families `g` into one family `n ↦ diag (g n)` — the assembled
    residue-chain — and name *that* with the same `diag`: it escapes again,
    `diag (n ↦ diag (g n)) ≠ (n ↦ diag (g n)) r` for every `r`.  So the chain of chains
    is a chain by the **same** operation: there is no meta-level sitting outside the
    mechanism, and naming the whole cascade is itself a cascade-step.  `diag_not_in_seq`
    holds for *every* family, including one built from diagonals — the operation is
    scale-invariant, applied identically at each level, always leaving a residue. -/
theorem diag_self_applies (g : Nat → (Nat → Nat → Nat)) :
    ∀ r, diag (fun n => diag (g n)) ≠ (fun n => diag (g n)) r :=
  diag_not_in_seq (fun n => diag (g n))

end E213.Lib.Math.Analysis.Cauchy.DepthHeightDiagonal
