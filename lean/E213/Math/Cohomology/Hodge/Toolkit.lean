import E213.Math.Cohomology.Hodge.Conjecture213

/-!
# Hodge Toolkit T1 — practical primitives

Computational tools for the 213-Hodge framework:

  * `support σ`     — extract the algebraic-cycle representation
                      (list of canonical k-simplex indices where σ = 1)
  * `fromList S`    — encode a list of canonical k-simplex indices
                      as a cochain (set-indicator)
  * `isCocycle σ`   — decidable cocycle predicate (δσ = 0)
  * `weight σ`      — Hamming weight = number of true coords
                      (= |support σ|)

All STRICT ∅-axiom (definitions on `Fin (binom n k) → Bool`; smoke
tests by `decide`).
-/

namespace E213.Math.Cohomology.Hodge.Toolkit

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Delta.Core (delta)
open E213.Physics.Simplex.Counts (binom)

/-- Support of σ: list of canonical k-simplex indices where σ = true. -/
def support {n k : Nat} (σ : Cochain n k) : List (Fin (binom n k)) :=
  (List.finRange (binom n k)).filter (fun i => σ i)

/-- Encode a list of indices as a cochain (set-indicator).
    Pointwise inverse to `support` (proved generically in T2). -/
def fromList {n k : Nat} (S : List (Fin (binom n k))) : Cochain n k :=
  fun j => S.any (fun i => i.val = j.val)

/-- Hamming weight of σ: number of indices where σ = true. -/
def weight {n k : Nat} (σ : Cochain n k) : Nat :=
  (support σ).length

/-- Decidable cocycle check: δσ = 0 at every (k+1)-face. -/
def isCocycle {n k : Nat} (σ : Cochain n k) : Bool :=
  (List.finRange (binom n (k + 1))).all (fun τ => !delta σ τ)

/-- Smoke: zero cochain has empty support. -/
theorem support_zero_5_2 :
    support (fun _ : Fin (binom 5 2) => false) = [] := by decide

/-- Smoke: all-true cochain in C¹(Δ⁴) has weight 5. -/
theorem weight_allTrue_5_1 :
    weight (fun _ : Fin (binom 5 1) => true) = 5 := by decide

/-- Smoke: fromList [] is the zero cochain (pointwise). -/
theorem fromList_empty_5_2 :
    ∀ j : Fin (binom 5 2),
      fromList ([] : List (Fin (binom 5 2))) j = false := by decide

/-- Smoke: zero cochain is a cocycle. -/
theorem isCocycle_zero_5_2 :
    isCocycle (fun _ : Fin (binom 5 2) => false) = true := by decide

/-- Smoke: at the top stratum k = n, every cochain is automatically
    a cocycle (no (k+1)-cells in Δⁿ⁻¹). -/
theorem isCocycle_top (σ : Cochain 5 5) : isCocycle σ = true := rfl

end E213.Math.Cohomology.Hodge.Toolkit
