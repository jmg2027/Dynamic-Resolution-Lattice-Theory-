import E213.Math.Cohomology.Universal.Prop52
import E213.Math.Cohomology.Delta.Pointwise

import E213.Math.Cohomology.Cochain.Core
import E213.Math.Cohomology.Delta.Core
import E213.Physics.Simplex.Counts
/-!
# Universal δ²=0 Prop-lift at (5, 3) — Δ⁴ 3-cochain (top-stratum)

Cochain 5 3 = Fin (binom 5 3) → Bool = Fin 10 → Bool, 2¹⁰ = 1024
functions.  δ² goes 3 → 4 → 5 with codomain Fin (binom 5 5) = Fin 1
(single index).  1024 × 1 = 1024 evals.

Closes the (5, k) Universal chain at top stratum.  Together with
UniversalProp51 (5,1) and UniversalProp52 (5,2), this completes
δ²=0 over all interior strata of Δ⁴.

**∅-axiom**: pattern via `match i.val` (Nat-match), `pattern_eq_at`
via `cases_lt_ten + subst`, `dsq_zero_prop_5_3` via
`delta_pointwise_eq` chain (no funext).
-/

namespace E213.Math.Cohomology.Universal.Prop53

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Delta.Core (delta)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Tactic.Nat213 (cases_lt_ten)

/-- Cochain 5 3 parametrized by 10 Bool values.  ∅-axiom (Nat match). -/
def pattern (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Cochain 5 3 :=
  fun i =>
    match i.val with
    | 0 => b0
    | 1 => b1
    | 2 => b2
    | 3 => b3
    | 4 => b4
    | 5 => b5
    | 6 => b6
    | 7 => b7
    | 8 => b8
    | _ => b9

/-- Pointwise pattern equality.  ∅-axiom via `cases_lt_ten + subst`. -/
theorem pattern_eq_at (σ : Cochain 5 3) (k : Fin (binom 5 3)) :
    σ k = pattern
      (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩) (σ ⟨2, by decide⟩)
      (σ ⟨3, by decide⟩) (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩)
      (σ ⟨6, by decide⟩) (σ ⟨7, by decide⟩) (σ ⟨8, by decide⟩)
      (σ ⟨9, by decide⟩) k := by
  obtain ⟨n, hn⟩ := k
  show σ ⟨n, hn⟩ = pattern _ _ _ _ _ _ _ _ _ _ ⟨n, hn⟩
  rcases cases_lt_ten hn with h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> rfl

set_option maxHeartbeats 8000000 in
/-- δ²=0 on every pattern: 1024 Bool 10-tuples × 1 index.
    ∅-axiom (decide on Bool variables; pattern itself ∅-axiom). -/
theorem dsq_pattern :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      ∀ i : Fin (binom 5 5),
        delta (delta (pattern b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) i
          = false := by decide

/-- ★★★ Prop-level ∀ σ : Cochain 5 3, δ²σ = 0.  ∅-axiom — chains
    `pattern_eq_at` through `delta_pointwise_eq` twice (no funext). -/
theorem dsq_zero_prop_5_3 (σ : Cochain 5 3)
    (i : Fin (binom 5 5)) : delta (delta σ) i = false :=
  let p := pattern (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩) (σ ⟨2, by decide⟩)
                   (σ ⟨3, by decide⟩) (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩)
                   (σ ⟨6, by decide⟩) (σ ⟨7, by decide⟩) (σ ⟨8, by decide⟩)
                   (σ ⟨9, by decide⟩)
  let h_pw : ∀ k, σ k = p k := pattern_eq_at σ
  let h_delta_pw : ∀ k, delta σ k = delta p k :=
    fun k => delta_pointwise_eq σ p h_pw k
  let h_dd : delta (delta σ) i = delta (delta p) i :=
    delta_pointwise_eq (delta σ) (delta p) h_delta_pw i
  h_dd.trans (dsq_pattern _ _ _ _ _ _ _ _ _ _ i)

end E213.Math.Cohomology.Universal.Prop53
