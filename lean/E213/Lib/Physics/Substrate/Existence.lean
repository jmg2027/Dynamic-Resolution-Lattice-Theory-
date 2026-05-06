import E213.Lib.Physics.Substrate.Origin

/-!
# Phase 2 Existence — what *exists* in d=5?

**Layer: App** (`Vertex := Fin 5` + block classification — *exactly the same pattern*
as `isA, classify` in math track `App/Simplex.lean`).

Origin.lean: *the universe is d=5 dimensional*.
Shape.lean: *5 points, (3,2) partition, 10 pairs*.
This file: *what are those 5, and what is the information between them?*

## What 213 can (and cannot) answer

### Can answer
- There are *5 things* (Fin 5 type).
- Between two things: the answer is *same / not same* (DecidableEq).
- The pattern of those answers is classified as (3,2) following *atomic partition*.

### Cannot do from 213 alone
- The *names* of those 5 things are not in the axiom (determined when Lens is added).
- *Classifications* such as distance, time, particles are also not in the axiom (Lens output).
- "labels" (which is spatial, which is temporal) are also Lens decisions.
  Only *block sizes* are determined by axiom.
-/

namespace E213.Lib.Physics.Substrate.Existence

/-- Type of d=5 things — Fin 5.  Minimal Lens output. -/
def Vertex : Type := Fin 5

/-- Whether two things are the same is *decidable*. -/
instance : DecidableEq Vertex := inferInstanceAs (DecidableEq (Fin 5))

/-- Which vertex belongs to the "big block" (size 3) — block 0.
    Labels are arbitrary (Lens decision), only size is axiom-determined. -/
def inBigBlock (v : Vertex) : Bool := v.val < 3

/-- Which vertex belongs to "small block" (size 2) — complement. -/
def inSmallBlock (v : Vertex) : Bool := decide (3 ≤ v.val)

/-- Every vertex is in exactly one block (mutually exclusive). -/
theorem block_disjoint_at_0 :
    inBigBlock ⟨0, by decide⟩ = !inSmallBlock ⟨0, by decide⟩ := by decide
theorem block_disjoint_at_1 :
    inBigBlock ⟨1, by decide⟩ = !inSmallBlock ⟨1, by decide⟩ := by decide
theorem block_disjoint_at_2 :
    inBigBlock ⟨2, by decide⟩ = !inSmallBlock ⟨2, by decide⟩ := by decide
theorem block_disjoint_at_3 :
    inBigBlock ⟨3, by decide⟩ = !inSmallBlock ⟨3, by decide⟩ := by decide
theorem block_disjoint_at_4 :
    inBigBlock ⟨4, by decide⟩ = !inSmallBlock ⟨4, by decide⟩ := by decide

/-- Exactly 3 vertices in big block. -/
theorem big_block_size_three :
    ((List.finRange 5).filter (fun v => inBigBlock v)).length = 3 := by
  decide

/-- Exactly 2 vertices in small block. -/
theorem small_block_size_two :
    ((List.finRange 5).filter (fun v => inSmallBlock v)).length = 2 := by
  decide

/-- Two block sizes sum to 5 (total vertex count). -/
theorem block_sizes_sum_to_5 :
    ((List.finRange 5).filter (fun v => inBigBlock v)).length
    + ((List.finRange 5).filter (fun v => inSmallBlock v)).length
    = 5 := by decide

/-- ★ Phase 2 Existence — everything 213 can answer ★

  In d=5 dimensions there are *5 vertices*.
  The atomic partition splits into *(3, 2)* sizes.
  Further ontology (names, meanings) is not axiom-determined. -/
theorem cosmos_existence_minimal :
    -- (3, 2) block sizes
    (((List.finRange 5).filter (fun v => inBigBlock v)).length = 3)
    ∧ (((List.finRange 5).filter (fun v => inSmallBlock v)).length = 2)
    -- Sum to 5
    ∧ (((List.finRange 5).filter (fun v => inBigBlock v)).length
       + ((List.finRange 5).filter (fun v => inSmallBlock v)).length
       = 5) := by decide

end E213.Lib.Physics.Substrate.Existence
