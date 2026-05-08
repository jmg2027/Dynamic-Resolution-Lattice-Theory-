import E213.Lib.Math.UniverseChain.RawDepthCount

/-!
# Raw bipartition by leftmost atom (∅-axiom)

The 5 canonical Raws of depth ≤ 2 split (3, 2) by leftmost atom:

  * leftmost = `a`: {a, slash a b, slash a (slash a b)} — **3**
  * leftmost = `b`: {b, slash b (slash a b)} — **2**

This is the *non-trivial* observation: the 5 = NS + NT atomicity
emerges in Raw at depth ≤ 2, AND the (3, 2) split also emerges
naturally via the canonical-form leftmost-atom rule.

NOT a claim about K_{3,2}^(c=2) graph structure — just that the
*partition cardinalities* match.
-/

namespace E213.Lib.Math.UniverseChain.RawBipartition

open E213.Theory
open E213.Theory.Internal (Tree)
open E213.Lib.Math.UniverseChain.RawDepthCount
  (depthLe2List s_ab s_a_ab s_b_ab)

/-- Leftmost atom of a Tree (true = a, false = b). -/
def leftmostAtomT : Tree → Bool
  | .a => true
  | .b => false
  | .slash x _ => leftmostAtomT x

/-- Leftmost atom of a Raw. -/
def Raw.leftmostAtom (r : Raw) : Bool := leftmostAtomT r.val

/-- ★ Leftmost atom values for the 5 depth-≤-2 inhabitants. -/
theorem leftmost_a : Raw.leftmostAtom Raw.a = true := rfl
theorem leftmost_b : Raw.leftmostAtom Raw.b = false := rfl
theorem leftmost_s_ab : Raw.leftmostAtom s_ab = true := by decide
theorem leftmost_s_a_ab : Raw.leftmostAtom s_a_ab = true := by decide
theorem leftmost_s_b_ab : Raw.leftmostAtom s_b_ab = false := by decide

/-- a-side = {Raw whose leftmost atom is true}. -/
def aSide : List Raw := depthLe2List.filter Raw.leftmostAtom

/-- b-side = {Raw whose leftmost atom is false}. -/
def bSide : List Raw := depthLe2List.filter (fun r => !Raw.leftmostAtom r)

/-- ★★ **a-side count = 3** = NS. -/
theorem aSide_count : aSide.length = 3 := by decide

/-- ★★ **b-side count = 2** = NT. -/
theorem bSide_count : bSide.length = 2 := by decide

/-- ★★ **(3, 2) bipartition** of Raw at depth ≤ 2. -/
theorem bipartition_3_2 :
    aSide.length = 3 ∧ bSide.length = 2 ∧ aSide.length + bSide.length = 5 :=
  ⟨aSide_count, bSide_count, by decide⟩

/-- ★★★ **Capstone**: depth-≤-2 Raw count + (3, 2) split match
    `(d, NS, NT) = (5, 3, 2)` from atomicity. -/
theorem raw_atomicity_geometric_match :
    depthLe2List.length = 5
    ∧ aSide.length = 3
    ∧ bSide.length = 2 :=
  ⟨RawDepthCount.depth_2_count, aSide_count, bSide_count⟩

end E213.Lib.Math.UniverseChain.RawBipartition
