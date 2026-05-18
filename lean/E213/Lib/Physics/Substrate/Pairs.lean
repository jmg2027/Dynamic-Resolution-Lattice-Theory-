import E213.Lib.Physics.Substrate.Existence

/-!
# Phase 2 Pairs — information structure of pairs

**Layer: Lib.Physics** (pair classification — same pattern as
`BlockPair, classify` in math track
`Lib/Math/Combinatorics/Simplex5.lean`).

Origin: *d=5*. Shape: *5 vertices, (3,2), 10 pairs*. Existence: *what are the 5 + classification*.
This file: *what is between those 10 pairs?*

## Pair = *order-independent* combination of two vertices

  pair (i, j) with i ≠ j.  C(5, 2) = 10 possible pairs.

  By block classification:
    - **AA pair**: both in big block (choose 2 of 3).  C(3,2)=3.
    - **BB pair**: both in small block.  C(2,2) = 1.
    - **AB pair**: cross (big × small).  3·2 = 6.

  Total: 3 + 1 + 6 = 10 ✓ (consistent with Shape.lean)

## Naturally emerging *bipartite* structure

*6 of the 10 pairs are cross (AB)*.  These 6 form the edge set of bipartite graph K_{3,2}.

  ★ Bipartite graph K_{NS,NT}^{(c=2)} is axiom-derived ★
  Simple arithmetic fact: 3 vertices × 2 vertices = 6 cross pairs.
  Phase 1 PhotonKernel work was also built on this bipartite.

## Formal propositions

  - PairAA, PairAB, PairBB classification function defined
  - Cardinality of each classification decide-checked
  - Total 10 consistency

This file is *axiom-free* — a natural consequence of Existence + Shape results.
-/

namespace E213.Lib.Physics.Substrate.Pairs

open E213.Lib.Physics.Substrate.Existence

/-- Which classification a pair of two vertices belongs to.
    AA: both big block.  BB: both small.  AB: cross. -/
inductive PairType
  | AA  -- big-big (within big block)
  | BB  -- small-small (within small block)
  | AB  -- cross (big-small or small-big)
  deriving DecidableEq, Repr

/-- Pair classification: from block information of two vertices. -/
def classifyPair (i j : Vertex) : PairType :=
  match inBigBlock i, inBigBlock j with
  | true,  true  => PairType.AA
  | false, false => PairType.BB
  | _,     _     => PairType.AB

/-- All unordered pairs (i, j) with i.val < j.val. -/
def allPairs : List (Vertex × Vertex) :=
  (List.finRange 5).flatMap (fun i =>
    (List.finRange 5).filterMap (fun j =>
      if i.val < j.val then some (i, j) else none))

/-- Total number of pairs = 10. -/
theorem total_pairs_eq_10 : allPairs.length = 10 := by decide

/-- AA pairs (big-big) count = 3. -/
theorem AA_pairs_count :
    (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AA)).length = 3 := by
  decide

/-- BB pairs (small-small) count = 1. -/
theorem BB_pairs_count :
    (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.BB)).length = 1 := by
  decide

/-- AB pairs (cross) count = 6.  Number of K_{3,2} bipartite edges. -/
theorem AB_pairs_count :
    (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AB)).length = 6 := by
  decide

/-- All pairs classified exhaustively as AA, BB, or AB. -/
theorem AA_BB_AB_sum :
    (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AA)).length
    + (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.BB)).length
    + (allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AB)).length
    = allPairs.length := by decide

/-- ★ Phase 2 Pairs — pair classification synthesis ★

  10 pairs = 3 (AA) + 1 (BB) + 6 (AB).
  The 6 AB pairs *naturally generate bipartite K_{3,2}*.

  Phase 1 PhotonKernel's K_{NS,NT}^{(c)} is also doubled over this. -/
theorem cosmos_pair_structure :
    -- AA: 3 (within big block)
    ((allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AA)).length = 3)
    -- BB: 1 (within small block)
    ∧ ((allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.BB)).length = 1)
    -- AB: 6 (bipartite edges)
    ∧ ((allPairs.filter (fun p => classifyPair p.1 p.2 = PairType.AB)).length = 6)
    -- Total 10
    ∧ (allPairs.length = 10) := by decide

end E213.Lib.Physics.Substrate.Pairs
