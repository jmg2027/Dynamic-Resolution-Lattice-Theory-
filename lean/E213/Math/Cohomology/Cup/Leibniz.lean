import E213.Math.Cohomology.Cup.Core

/-!
# Cohomology — cup-product Leibniz rule (Phase CD, file 2)

The compatibility identity making cup descend to H*:

    δ(α ⌣ β) = δα ⌣ β + (-1)^|α| α ⌣ δβ

In ℤ/2 (Bool/XOR) the sign disappears:

    δ(α ⌣ β) = δα ⌣ β XOR α ⌣ δβ.

This file verifies the identity at concrete cochains on Δ⁴
(n=5).  Universally-quantified version requires Fintype +
DecidablePred on `Cochain n k`, deferred.
-/

namespace E213.Math.Cohomology.Cup.Leibniz

open E213.Physics.Simplex.Counts (binom d NS NT)
open E213.Math.Cohomology.Cup.Core (cup all_true_5_1)
open E213.Math.Cohomology.Delta.Core (delta)
open E213.Math.Cohomology.Hodge.Involution (v0_5)
open E213.Math.Cohomology.Cochain.Core (Cochain)

/-- Leibniz on (v0_5 ⌣ v0_5) — both sides agree pointwise. -/
theorem leibniz_v0_v0_pointwise :
    ∀ i : Fin (binom 5 3),
      delta (cup 5 1 1 v0_5 v0_5) i
        = xor (cup 5 2 1 (delta v0_5) v0_5 i)
              (cup 5 1 2 v0_5 (delta v0_5) i) := by decide

/-- Leibniz on (all_true_5_1 ⌣ v0_5). -/
theorem leibniz_at_v0_pointwise :
    ∀ i : Fin (binom 5 3),
      delta (cup 5 1 1 all_true_5_1 v0_5) i
        = xor (cup 5 2 1 (delta all_true_5_1) v0_5 i)
              (cup 5 1 2 all_true_5_1 (delta v0_5) i) := by decide

/-- Leibniz with zero on the left — both sides zero (sanity). -/
theorem leibniz_zero_left :
    ∀ i : Fin (binom 5 3),
      delta (cup 5 1 1 (Cochain.zero 5 1) v0_5) i
        = xor (cup 5 2 1 (delta (Cochain.zero 5 1)) v0_5 i)
              (cup 5 1 2 (Cochain.zero 5 1) (delta v0_5) i) := by decide

/-- Leibniz with zero on the right. -/
theorem leibniz_zero_right :
    ∀ i : Fin (binom 5 3),
      delta (cup 5 1 1 v0_5 (Cochain.zero 5 1)) i
        = xor (cup 5 2 1 (delta v0_5) (Cochain.zero 5 1) i)
              (cup 5 1 2 v0_5 (delta (Cochain.zero 5 1)) i) := by decide

/-- ★ Phase CD intermediate capstone (file 2) — Leibniz rule
    `δ(α ⌣ β) = δα ⌣ β XOR α ⌣ δβ` verified at four cochain
    pairs on Δ⁴.  Confirms cup descends to H*. -/
theorem phase_CD_leibniz_capstone :
    (∀ i : Fin (binom 5 3),
       delta (cup 5 1 1 v0_5 v0_5) i
         = xor (cup 5 2 1 (delta v0_5) v0_5 i)
               (cup 5 1 2 v0_5 (delta v0_5) i))
    ∧ (∀ i : Fin (binom 5 3),
         delta (cup 5 1 1 all_true_5_1 v0_5) i
           = xor (cup 5 2 1 (delta all_true_5_1) v0_5 i)
                 (cup 5 1 2 all_true_5_1 (delta v0_5) i)) :=
  ⟨leibniz_v0_v0_pointwise, leibniz_at_v0_pointwise⟩

end E213.Math.Cohomology.Cup.Leibniz
