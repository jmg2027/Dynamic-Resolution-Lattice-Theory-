import E213.Lens.Number
import E213.Theory.Raw.API

/-!
# Proof-ISA — a worked compilation (`seed/PROOF_ISA.md` demonstration)

A problem about the infinite, compiled to the instruction set — no insight, just ISA operations.

**Problem (L3).**  "The count reading is unbounded" — there is no `Raw` of maximal count; i.e. the
infinite of `ℕ` seen through the count-Lens (`05`/`06`: `ℕ` is `Lens.leaves`'s image).

**Compilation.**
  * `value` is the **READ** instruction (`Lens.leaves.view = Raw.fold 1 1 (·+·)`).
  * `value_slash` is **READ distributing over DISTINGUISH**: reading a residue `x/y` is reading `x` plus
    reading `y` (`Raw.fold_slash`, the homomorphism — combine `+` is symmetric).
  * `count_unbounded` is **DISTINGUISH ∘ READ**: form the residue `r / x` (DISTINGUISH); its count is
    `value r + value x ≥ value r + 1` (READ) — strictly larger.  This is the "no largest" / Euclid move,
    which is the `DIAGONALIZE` family (the something distinguishable from what was pointed at).

All `∅`-axiom.  The point is the *method*: the proof is the composition of two instructions, located
mechanically, not a problem-specific trick.
-/

namespace E213.Lens.ProofISADemo

open E213.Theory E213.Lens
open E213.Lens.Number.Nat213.Raw (value)

/-- **READ over DISTINGUISH**: `value (x / y) = value x + value y` (the count homomorphism). -/
theorem value_slash (x y : Raw) (h : x ≠ y) : value (Raw.slash x y h) = value x + value y :=
  Raw.fold_slash 1 1 (· + ·) (fun u v => Nat.add_comm u v) x y h

/-- ★★★★★ **Worked compilation — the count reading is unbounded** (`DISTINGUISH ∘ READ`).  For every
    `r`, distinguishing it from an atom forms `r / x` whose count strictly exceeds `r`'s.  The "no
    largest" infinity proof, as a two-instruction composition. -/
theorem count_unbounded (r : Raw) : ∃ r' : Raw, value r < value r' := by
  by_cases h : r = Raw.b
  · -- DISTINGUISH: r / a  (r = b ≠ a)
    refine ⟨Raw.slash r Raw.a (by rw [h]; decide), ?_⟩
    rw [value_slash]                                   -- READ: value (r/a) = value r + value a
    exact Nat.lt_add_of_pos_right (by decide)          -- value a = 1 > 0
  · -- DISTINGUISH: r / b
    refine ⟨Raw.slash r Raw.b h, ?_⟩
    rw [value_slash]                                   -- READ: value (r/b) = value r + value b
    exact Nat.lt_add_of_pos_right (by decide)          -- value b = 1 > 0

end E213.Lens.ProofISADemo
