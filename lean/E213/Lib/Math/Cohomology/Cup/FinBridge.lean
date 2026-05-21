import E213.Lib.Math.Cohomology.Cup.Core
import E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtrip

/-!
# Cohomology.Cup.FinBridge

Bridge between the Fin-indexed `cup` operation (used in the cohomology
codebase) and explicit vertex-extraction functions.  Built on the
SubsetIdxRoundtrip primitives.

For the (1, 1) bidegree on Δ⁴, the cup at any 2-face τ_idx unfolds to
`α (first vertex) && β (last vertex)`, where the vertex extractions are
hard-coded from colex enumeration.

PURE: all theorems decide-verified per (n, k, l, τ_idx) case.
-/

namespace E213.Lib.Math.Cohomology.Cup.FinBridge

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §1.  Vertex extraction functions on Δ⁴

For each 2-face τ_idx ∈ Fin (binom 5 2) = Fin 10, extract the
first vertex (τ[0]) and the second vertex (τ[1]) as Fin 5. -/

/-- First vertex of the τ_idx-th 2-subset of {0..4} (in colex). -/
def firstVertex_5_2 (j : Fin (binom 5 2)) : Fin 5 :=
  if j.val == 0 then ⟨0, by decide⟩
  else if j.val == 1 then ⟨0, by decide⟩
  else if j.val == 2 then ⟨1, by decide⟩
  else if j.val == 3 then ⟨0, by decide⟩
  else if j.val == 4 then ⟨1, by decide⟩
  else if j.val == 5 then ⟨2, by decide⟩
  else if j.val == 6 then ⟨0, by decide⟩
  else if j.val == 7 then ⟨1, by decide⟩
  else if j.val == 8 then ⟨2, by decide⟩
  else ⟨3, by decide⟩  -- j = 9

/-- Last vertex of the τ_idx-th 2-subset of {0..4} (in colex). -/
def lastVertex_5_2 (j : Fin (binom 5 2)) : Fin 5 :=
  if j.val == 0 then ⟨1, by decide⟩
  else if j.val == 1 then ⟨2, by decide⟩
  else if j.val == 2 then ⟨2, by decide⟩
  else if j.val == 3 then ⟨3, by decide⟩
  else if j.val == 4 then ⟨3, by decide⟩
  else if j.val == 5 then ⟨3, by decide⟩
  else if j.val == 6 then ⟨4, by decide⟩
  else if j.val == 7 then ⟨4, by decide⟩
  else if j.val == 8 then ⟨4, by decide⟩
  else ⟨4, by decide⟩  -- j = 9

/-! ## §2.  Fin-indexed cup unfold at (5, 1, 1)

The bridge lemma: cup α β τ_idx for any α, β : Cochain 5 1 and
any τ_idx : Fin 10 equals `α (firstVertex τ_idx) && β (lastVertex τ_idx)`.

Pattern: parameterise α and β by their 5 Bool values each
(Bool-tuple parameterisation, Pattern #2), then decide over
2¹⁰ · 10 = 10240 cases. -/

/-- ★★★ **Fin-indexed cup bridge at (5, 1, 1)** — cup unfolds to
    explicit vertex evaluations on the underlying 2-subset.
    Decide-verified across 10240 cases (Pattern #2).  PURE. -/
theorem cup_5_1_1_unfold :
    ∀ (a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : Bool)
      (τ_idx : Fin (binom 5 2)),
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
      cup 5 1 1 α β τ_idx
        = (α (firstVertex_5_2 τ_idx) && β (lastVertex_5_2 τ_idx)) := by
  decide

/-! ## §3.  Face-index extraction on Δ⁴ at (k=1, l=1)

For each 3-face τ_idx ∈ Fin (binom 5 3) and each i ∈ {0, 1, 2}
(face position to remove), the resulting 2-subset has a colex
index in Fin (binom 5 2).  Hardcoded from kSubset enumeration. -/

/-- For 3-subset at colex idx j on Δ⁴, return the colex idx (in
    Fin 10 = Fin (binom 5 2)) of the 2-subset obtained by removing
    the position-i vertex.  i ∈ {0, 1, 2}. -/
def face2idx_5_3 (j : Fin (binom 5 3)) (i : Fin 3) : Fin (binom 5 2) :=
  if j.val == 0 then
    if i.val == 0 then ⟨2, by decide⟩       -- [0,1,2] \ {0} = [1,2]
    else if i.val == 1 then ⟨1, by decide⟩  -- \ {1} = [0,2]
    else ⟨0, by decide⟩                       -- \ {2} = [0,1]
  else if j.val == 1 then
    if i.val == 0 then ⟨4, by decide⟩
    else if i.val == 1 then ⟨3, by decide⟩
    else ⟨0, by decide⟩
  else if j.val == 2 then
    if i.val == 0 then ⟨5, by decide⟩
    else if i.val == 1 then ⟨3, by decide⟩
    else ⟨1, by decide⟩
  else if j.val == 3 then
    if i.val == 0 then ⟨5, by decide⟩
    else if i.val == 1 then ⟨4, by decide⟩
    else ⟨2, by decide⟩
  else if j.val == 4 then
    if i.val == 0 then ⟨7, by decide⟩
    else if i.val == 1 then ⟨6, by decide⟩
    else ⟨0, by decide⟩
  else if j.val == 5 then
    if i.val == 0 then ⟨8, by decide⟩
    else if i.val == 1 then ⟨6, by decide⟩
    else ⟨1, by decide⟩
  else if j.val == 6 then
    if i.val == 0 then ⟨8, by decide⟩
    else if i.val == 1 then ⟨7, by decide⟩
    else ⟨2, by decide⟩
  else if j.val == 7 then
    if i.val == 0 then ⟨9, by decide⟩    -- [0,3,4] \ {0} = [3,4] → 9
    else if i.val == 1 then ⟨6, by decide⟩  -- \ {3} = [0,4] → 6
    else ⟨3, by decide⟩                    -- \ {4} = [0,3] → 3
  else if j.val == 8 then
    if i.val == 0 then ⟨9, by decide⟩    -- [1,3,4] \ {1} = [3,4] → 9
    else if i.val == 1 then ⟨7, by decide⟩  -- \ {3} = [1,4] → 7
    else ⟨4, by decide⟩                    -- \ {4} = [1,3] → 4
  else  -- j = 9: [2,3,4]
    if i.val == 0 then ⟨9, by decide⟩  -- \{2} = [3,4]
    else if i.val == 1 then ⟨8, by decide⟩  -- \{3} = [2,4]
    else ⟨5, by decide⟩                  -- \{4} = [2,3]

/-! ## §4.  Delta-cup composition at (5, 1, 1) — Fin-level

The full Fin-level expression `delta (cup α β) τ_idx` decomposes
into a 3-term XOR over the cup values at face-indices.  Combined
with `cup_5_1_1_unfold`, this gives the complete Fin-level
unfolding of the LHS of the (1, 1) Leibniz on Δ⁴. -/

open E213.Lib.Math.Cohomology.Delta.Core (delta)

set_option maxHeartbeats 4000000 in

/-- ★★★ **Delta-of-cup unfold at (5, 1, 1)** — for any α, β :
    Cochain 5 1 and τ_idx : Fin 10 (binom 5 3),

      delta (cup 5 1 1 α β) τ_idx
      = xor (xor (xor false
                (cup 5 1 1 α β (face2idx_5_3 τ_idx ⟨0, by decide⟩)))
                (cup 5 1 1 α β (face2idx_5_3 τ_idx ⟨1, by decide⟩)))
              (cup 5 1 1 α β (face2idx_5_3 τ_idx ⟨2, by decide⟩))

    PURE.  Decide-verified across 10240 parameter cases. -/
theorem delta_cup_5_1_1_unfold :
    ∀ (a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : Bool)
      (τ_idx : Fin (binom 5 3)),
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
      delta (cup 5 1 1 α β) τ_idx
        = (xor (xor (xor false
                (cup 5 1 1 α β (face2idx_5_3 τ_idx ⟨0, by decide⟩)))
                (cup 5 1 1 α β (face2idx_5_3 τ_idx ⟨1, by decide⟩)))
              (cup 5 1 1 α β (face2idx_5_3 τ_idx ⟨2, by decide⟩))) := by
  decide

end E213.Lib.Math.Cohomology.Cup.FinBridge
