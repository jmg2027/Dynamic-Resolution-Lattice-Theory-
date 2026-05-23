import E213.Lib.Math.Cohomology.Examples.BettiKernel

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Hodge.Involution
import E213.Lib.Math.Cohomology.Examples.SimplexBasis
import E213.Lib.Physics.Simplex.Counts
/-!
# Cohomology — lex-projection cup product

  ⌣ : Cᵏ × Cˡ → Cᵏ⁺ˡ
  (α ⌣ β)(τ) = α(τ first k) · β(τ last l)
over a sorted (k+l)-subset τ.  In ℤ/2 (Bool) `·` is AND.

## Identity disclosure 

This is the **lex-projection cup** — for a sorted (k+l)-subset τ
it picks the *single sorted partition* (front k vertices, back l
vertices) and multiplies the cochain values at those two parts.

It is NOT:
  · Standard simplicial Alexander–Whitney cup (which uses
    (k+1)+(l+1)-vertex τ with a shared vertex at position k —
    different type signature).
  · The ℤ/2 antisymmetric wedge `Λ^k ⊗ Λ^l → Λ^(k+l)` (which
    XOR-sums over all k-l partitions of τ; in ℤ/2 the sign
    vanishes but partitions still differ from sorted-only).

The lex-projection cup admits its own natural Leibniz rule with a
**boundary-endpoint correction term** distinguishing it from both
AW and full wedge.  See `Cup/LeibnizLex.lean` for the (1, 1)
universal form, and `research-notes/G85_cup_delta_lens_mismatch.md`
for the 213-native re-reading of cup / δ as parallel Lens choices.

The prior docstring's "Alexander–Whitney" label was a misclaim —
self-corrected here in the spirit of `CLAUDE.md` §8 (catalog
misclaim self-correction).  Existing 4-pair Leibniz tests in
`Cup/Leibniz.lean` happen to satisfy the standard Leibniz at their
symmetric cochain inputs (v0, all_true, zero) because the
boundary-endpoint correction degenerates for these; asymmetric
basis pairs expose the genuine algebraic content.

All three arities (n, k, l) explicit to avoid metavariables.
-/

namespace E213.Lib.Math.Cohomology.Cup.Core

open E213.Lib.Physics.Simplex.Counts (binom d NS NT)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Delta.Core (subsetIdx)
open E213.Lib.Math.Cohomology.Hodge.Involution (v0_5)

/-- Cup product (lex-projection) at fixed (n, k, l).  See file
    docstring for identity disclosure. -/
def cup (n k l : Nat) (α : Cochain n k) (β : Cochain n l) :
    Cochain n (k + l) :=
  fun τ_idx =>
    let τ := kSubset n (k + l) τ_idx.val
    let front := τ.take k
    let back := τ.drop k
    let f_idx := subsetIdx n k front
    let b_idx := subsetIdx n l back
    if hf : f_idx < binom n k then
      if hb : b_idx < binom n l then
        α ⟨f_idx, hf⟩ && β ⟨b_idx, hb⟩
      else false
    else false

/-- Smoke: cup with zero left = zero. -/
theorem cup_zero_left_5_1_1 :
    ∀ i : Fin (binom 5 2),
      cup 5 1 1 (Cochain.zero 5 1) v0_5 i = false := by decide

/-- Smoke: cup with zero right = zero. -/
theorem cup_zero_right_5_1_1 :
    ∀ i : Fin (binom 5 2),
      cup 5 1 1 v0_5 (Cochain.zero 5 1) i = false := by decide

/-- v0 ⌣ v0 on edge [0,1]: front=[0], back=[1]; v0([0])=true,
    v0([1])=false; AND = false. -/
theorem cup_v0_v0_concrete :
    cup 5 1 1 v0_5 v0_5 ⟨0, by decide⟩ = false
    ∧ cup 5 1 1 v0_5 v0_5 ⟨1, by decide⟩ = false := by decide

/-- All-ones cochain at (5, 1). -/
def all_true_5_1 : Cochain 5 1 := fun _ => true

/-- All-ones ⌣ all-ones at edge [0,1] = true AND true = true. -/
theorem cup_all_true_5_1_at_edge0 :
    cup 5 1 1 all_true_5_1 all_true_5_1 ⟨0, by decide⟩ = true := by decide

/-- ★ intermediate capstone (file 1) — cup well-defined
    and decide-checked; zero-on-either-side preserved. -/
theorem phase_CD_cup_smoke :
    (∀ i : Fin (binom 5 2),
       cup 5 1 1 (Cochain.zero 5 1) v0_5 i = false)
    ∧ (∀ i : Fin (binom 5 2),
         cup 5 1 1 v0_5 (Cochain.zero 5 1) i = false)
    ∧ (cup 5 1 1 all_true_5_1 all_true_5_1 ⟨0, by decide⟩ = true) :=
  ⟨cup_zero_left_5_1_1, cup_zero_right_5_1_1, cup_all_true_5_1_at_edge0⟩

end E213.Lib.Math.Cohomology.Cup.Core
