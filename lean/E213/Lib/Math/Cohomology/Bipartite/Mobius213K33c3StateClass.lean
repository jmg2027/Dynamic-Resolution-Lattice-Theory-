import E213.Lib.Math.Cohomology.Bipartite.V33c3
import E213.Lib.Math.Real213.Mobius213Equiv

/-!
# Mobius213K33c3StateClass — K_{3,3}^(c=3) edge cochains under Möbius P

The bipartite multigraph `K_{3,3}^(c=3)` has edge cochains
`CochE = Fin 27 → Bool` partitioned by multiplicity `m ∈ {0, 1, 2}`.

This file is the c=3 analog of `Mobius213K33StateClass` but at the
EDGE level (vertex-level is c-independent and identical to c=2).

  · `countMult m σ` — number of mult-`m` edges σ selects (∈ {0, …, 9})
  · `multCount σ := (countMult 0 σ, countMult 1 σ, countMult 2 σ)`

For the all-true edge cochain: `countMult m = 9` at each m, total 27.

The triple `(9, 9, 9)` represents the FULLY SATURATED multiplicity
distribution.  In Möbius terms: `9 = 3·3 = NS·NT`, the K_{3,3}
cross-pair count.  All three mults carry the same weight in the
saturated state.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Mobius213K33c3StateClass

open E213.Lib.Math.Cohomology.Bipartite.V33c3 (CochE)

/-! ## §1 — Special K_{3,3}^(c=3) edge cochains -/

def allTrueE : CochE := fun _ => true
def zeroE : CochE := fun _ => false

/-! ## §2 — Multiplicity counts

At c=3, mult-m edges have indices ≡ m (mod 3) in `Fin 27`.  Each
multiplicity layer has 9 edges (one per (S, T) pair). -/

/-- Count of mult-0 edges (indices 0, 3, 6, …, 24) selected by σ. -/
def countMult0 (σ : CochE) : Nat :=
  (if σ ⟨0, by decide⟩ then 1 else 0)
    + (if σ ⟨3, by decide⟩ then 1 else 0)
    + (if σ ⟨6, by decide⟩ then 1 else 0)
    + (if σ ⟨9, by decide⟩ then 1 else 0)
    + (if σ ⟨12, by decide⟩ then 1 else 0)
    + (if σ ⟨15, by decide⟩ then 1 else 0)
    + (if σ ⟨18, by decide⟩ then 1 else 0)
    + (if σ ⟨21, by decide⟩ then 1 else 0)
    + (if σ ⟨24, by decide⟩ then 1 else 0)

/-- Count of mult-1 edges (indices 1, 4, 7, …, 25). -/
def countMult1 (σ : CochE) : Nat :=
  (if σ ⟨1, by decide⟩ then 1 else 0)
    + (if σ ⟨4, by decide⟩ then 1 else 0)
    + (if σ ⟨7, by decide⟩ then 1 else 0)
    + (if σ ⟨10, by decide⟩ then 1 else 0)
    + (if σ ⟨13, by decide⟩ then 1 else 0)
    + (if σ ⟨16, by decide⟩ then 1 else 0)
    + (if σ ⟨19, by decide⟩ then 1 else 0)
    + (if σ ⟨22, by decide⟩ then 1 else 0)
    + (if σ ⟨25, by decide⟩ then 1 else 0)

/-- Count of mult-2 edges (indices 2, 5, 8, …, 26). -/
def countMult2 (σ : CochE) : Nat :=
  (if σ ⟨2, by decide⟩ then 1 else 0)
    + (if σ ⟨5, by decide⟩ then 1 else 0)
    + (if σ ⟨8, by decide⟩ then 1 else 0)
    + (if σ ⟨11, by decide⟩ then 1 else 0)
    + (if σ ⟨14, by decide⟩ then 1 else 0)
    + (if σ ⟨17, by decide⟩ then 1 else 0)
    + (if σ ⟨20, by decide⟩ then 1 else 0)
    + (if σ ⟨23, by decide⟩ then 1 else 0)
    + (if σ ⟨26, by decide⟩ then 1 else 0)

/-- The multiplicity distribution of a cochain: `(m0, m1, m2)`. -/
def multCount (σ : CochE) : Nat × Nat × Nat :=
  (countMult0 σ, countMult1 σ, countMult2 σ)

/-! ## §3 — Saturated and zero state distributions -/

theorem countMult0_allTrueE : countMult0 allTrueE = 9 := by decide
theorem countMult1_allTrueE : countMult1 allTrueE = 9 := by decide
theorem countMult2_allTrueE : countMult2 allTrueE = 9 := by decide

theorem multCount_zeroE : multCount zeroE = (0, 0, 0) := by decide

/-- ★★★★ All-true edge cochain has equal saturated count `(9, 9, 9)`
    across all three multiplicities.  `9 = NS · NT` = the K_{3,3}
    cross-pair count. -/
theorem multCount_allTrueE : multCount allTrueE = (9, 9, 9) := by decide

/-! ## §4 — Saturation symmetry: c-many independent layer slots

The three multiplicities are INDEPENDENT in the cochain space: each
contributes its own 9-edge slot.  Total cochain dim: `NS·NT·c = 27`. -/

theorem total_edge_count_at_c3 :
    countMult0 allTrueE + countMult1 allTrueE + countMult2 allTrueE = 27 := by decide

/-- The cross-pair count 9 equals the K_{3,3} cross-pair count (= NS·NT). -/
theorem layer_saturation_eq_cross_pairs :
    countMult0 allTrueE = 9
    ∧ countMult1 allTrueE = 9
    ∧ countMult2 allTrueE = 9 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Master capstone: K_{3,3}^(c=3) edge cochain state-class structure. -/
theorem multCount_master :
    -- (a) Per-layer saturation = cross-pair count
    countMult0 allTrueE = 9
    ∧ countMult1 allTrueE = 9
    ∧ countMult2 allTrueE = 9
    -- (b) Multiplicity distribution of allTrue
    ∧ multCount allTrueE = (9, 9, 9)
    -- (c) Total edge count
    ∧ countMult0 allTrueE + countMult1 allTrueE + countMult2 allTrueE = 27 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Cohomology.Bipartite.Mobius213K33c3StateClass
