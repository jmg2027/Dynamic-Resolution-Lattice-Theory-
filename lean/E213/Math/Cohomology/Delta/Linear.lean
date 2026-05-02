import E213.Math.Cohomology.Delta.Core

/-!
# δ is XOR-linear: δ(σ + τ) = δσ + δτ

Universal over (n, k).  Reduces to a foldl-XOR distributivity
lemma proved by induction on the list.

Together with `cupAW_add_left/right`, this gives the full lens
to collapse Cup Leibniz from O(2^N · 2^M) decide cases to
~N · M basis-pair cases.
-/

namespace E213.Math.Cohomology.Delta.Linear

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.Delta.Core (delta deltaAt subsetIdx)
open E213.Math.Cohomology.SimplexBasis (kSubset)

/-- foldl-XOR distributivity over a Decidable conditional. -/
private theorem List.foldl_xor_dist
    {α : Type} (xs : List α)
    (P : α → Prop) [DecidablePred P]
    (f g : (a : α) → P a → Bool) (a b : Bool) :
    xs.foldl (fun acc x =>
        if h : P x then xor acc (xor (f x h) (g x h)) else acc)
      (xor a b)
      = xor
        (xs.foldl (fun acc x =>
            if h : P x then xor acc (f x h) else acc) a)
        (xs.foldl (fun acc x =>
            if h : P x then xor acc (g x h) else acc) b) := by
  induction xs generalizing a b with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h : P hd
    · simp only [_root_.List.foldl, h, ↓reduceDIte]
      have heq : xor (xor a b) (xor (f hd h) (g hd h))
                  = xor (xor a (f hd h)) (xor b (g hd h)) := by
        cases a <;> cases b <;> cases (f hd h) <;> cases (g hd h) <;> rfl
      rw [heq]
      exact ih (xor a (f hd h)) (xor b (g hd h))
    · simp only [_root_.List.foldl, h, ↓reduceDIte]
      exact ih a b

/-- ★ δ is XOR-linear: δ(σ.add τ)(τ_idx) = xor (δσ τ_idx) (δτ τ_idx). -/
theorem delta_add (n k : Nat) (σ τ : Cochain n k)
    (τ_idx : Fin (binom n (k + 1))) :
    delta (Cochain.add σ τ) τ_idx
      = xor (delta σ τ_idx) (delta τ τ_idx) := by
  show deltaAt n k (Cochain.add σ τ) τ_idx.val
        = xor (deltaAt n k σ τ_idx.val) (deltaAt n k τ τ_idx.val)
  unfold deltaAt
  show (List.range (k + 1)).foldl
        (fun acc i =>
          let face_i := (kSubset n (k+1) τ_idx.val).eraseIdx i
          let f_idx := subsetIdx n k face_i
          if h : f_idx < binom n k then
            xor acc (xor (σ ⟨f_idx, h⟩) (τ ⟨f_idx, h⟩))
          else acc) false
      = _
  have key := List.foldl_xor_dist (List.range (k + 1))
    (fun i =>
      subsetIdx n k ((kSubset n (k+1) τ_idx.val).eraseIdx i)
        < binom n k)
    (fun i h => σ ⟨_, h⟩) (fun i h => τ ⟨_, h⟩)
    false false
  show _ = xor _ _
  rw [show (false.xor false) = false from rfl] at key
  exact key

/-- ★★★ Delta linearity capstone — XOR distributes through δ. -/
theorem delta_linear_capstone (n k : Nat)
    (σ τ : Cochain n k) (τ_idx : Fin (binom n (k + 1))) :
    delta (Cochain.add σ τ) τ_idx
      = xor (delta σ τ_idx) (delta τ τ_idx) :=
  delta_add n k σ τ τ_idx

end E213.Math.Cohomology.Delta.Linear
