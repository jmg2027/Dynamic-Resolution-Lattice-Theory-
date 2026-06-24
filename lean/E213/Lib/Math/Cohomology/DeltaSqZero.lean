import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Examples.ColexRoundTrip
import E213.Lib.Math.Cohomology.Examples.XorInvolution
import E213.Lib.Math.Cohomology.Delta.Pointwise

/-!
# Toward the dimension-free `δ² = 0` — `deltaAt` as a clean `xorFold`

`deltaAt`'s body is a `List.foldl` over a **dependent `if`** (the in-range guard on the
face's colex index).  To feed `δ²` into the involution engine
(`XorInvolution.xorFold_involution`), the guard must be removed.

The trick: evaluate `σ` at a `Nat` index via `cochainAtNat`, which returns `false`
out of range.  Then each `deltaAt` step is `xor acc (cochainAtNat σ faceIdx)`
**unconditionally** — in range it is the real `σ`-value; out of range
`xor acc false = acc`, exactly the `else` branch.  So `deltaAt = xorFold (…)` with no
guard, the form the involution engine consumes.

This is the first bridge lemma; the full `delta_sq_zero_general` then composes two
`deltaAt_eq_xorFold` rewrites with the reverse round-trip (`kSubset_subsetIdx`) and the
`(a,b) ↦ (b+1,a)` involution (`eraseIdx_eraseIdx_comm`).
-/

namespace E213.Lib.Math.Cohomology.DeltaSqZero

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Delta.Core (deltaAt subsetIdx delta)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Examples.XorInvolution (xorFold)

/-! ## Bool XOR algebra (local, propext-free) -/

private theorem xor_false (b : Bool) : xor b false = b := by cases b <;> rfl
private theorem false_xor (b : Bool) : xor false b = b := by cases b <;> rfl
private theorem xor_assoc (a b c : Bool) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## `List.foldl xor` is `xorFold` -/

/-- Accumulator extraction for a left XOR-fold. -/
private theorem foldl_xor_acc {α : Type _} (h : α → Bool) :
    ∀ (l : List α) (init : Bool),
      l.foldl (fun acc x => xor acc (h x)) init = xor init (xorFold h l)
  | [],      init => (xor_false init).symm
  | x :: xs, init => by
    show (xs.foldl (fun acc x => xor acc (h x)) (xor init (h x)))
          = xor init (xorFold h (x :: xs))
    exact (foldl_xor_acc h xs (xor init (h x))).trans (xor_assoc init (h x) (xorFold h xs))

/-- `List.foldl (xor · (h ·)) false = xorFold h`. -/
private theorem foldl_xor_false {α : Type _} (h : α → Bool) (l : List α) :
    l.foldl (fun acc x => xor acc (h x)) false = xorFold h l :=
  (foldl_xor_acc h l false).trans (false_xor _)

/-! ## `cochainAtNat` — evaluate a cochain at a `Nat` index (false out of range) -/

/-- `σ` at a `Nat` index, `false` outside `Fin (binom n k)`.  The guard-absorbing
    evaluation: in range it is `σ ⟨idx, _⟩`; out of range it is `false`. -/
def cochainAtNat {n k : Nat} (σ : Cochain n k) (idx : Nat) : Bool :=
  if h : idx < binom n k then σ ⟨idx, h⟩ else false

/-- ★★★ **`deltaAt` is a guard-free `xorFold`.**  Reading `σ` through `cochainAtNat`
    collapses the dependent-`if` in `deltaAt` to an unconditional XOR over the faces:
    `deltaAt n k σ τ = xorFold (cochainAtNat σ ∘ faceIdx) (range (k+1))`, where
    `faceIdx i = subsetIdx n k ((kSubset n (k+1) τ).eraseIdx i)`.  ∅-axiom. -/
theorem deltaAt_eq_xorFold {n k : Nat} (σ : Cochain n k) (τ_idx : Nat) :
    deltaAt n k σ τ_idx
      = xorFold (fun i => cochainAtNat σ (subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i)))
                (List.range (k + 1)) := by
  show (List.range (k + 1)).foldl
        (fun acc i =>
          if h : subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i) < binom n k
          then xor acc (σ ⟨_, h⟩) else acc) false
       = xorFold _ _
  have hstep : ∀ acc i,
      (if h : subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i) < binom n k
       then xor acc (σ ⟨_, h⟩) else acc)
      = xor acc (cochainAtNat σ (subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i))) := by
    intro acc i
    by_cases hc : subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i) < binom n k
    · have hL : (if h : subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i) < binom n k
                 then xor acc (σ ⟨_, h⟩) else acc) = xor acc (σ ⟨_, hc⟩) := dif_pos hc
      have hR : cochainAtNat σ (subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i))
                  = σ ⟨_, hc⟩ := dif_pos hc
      exact hL.trans (congrArg (xor acc) hR.symm)
    · have hL : (if h : subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i) < binom n k
                 then xor acc (σ ⟨_, h⟩) else acc) = acc := dif_neg hc
      have hR : cochainAtNat σ (subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i))
                  = false := dif_neg hc
      exact hL.trans ((xor_false acc).symm.trans (congrArg (xor acc) hR.symm))
  exact (E213.Lib.Math.Cohomology.Delta.Pointwise.foldl_step_eq _ _ hstep (List.range (k + 1)) false).trans
    (foldl_xor_false _ (List.range (k + 1)))

end E213.Lib.Math.Cohomology.DeltaSqZero
