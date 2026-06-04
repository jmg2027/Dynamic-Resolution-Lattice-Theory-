import E213.Lib.Math.Foundations.UniverseChain.RawDepthCount

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

namespace E213.Lib.Math.Foundations.UniverseChain.RawBipartition

open E213.Theory
open E213.Term.Internal (Tree)
open E213.Lib.Math.Foundations.UniverseChain.RawDepthCount
  (depthLe2List s_ab s_a_ab s_b_ab)

/-- Leftmost atom of a Tree (true = a, false = b). -/
def leftmostAtomT : Tree → Bool
  | .a => true
  | .b => false
  | .slash x _ => leftmostAtomT x

/-- Leftmost atom of a Raw. -/
def Raw.leftmostAtom (r : Raw) : Bool := leftmostAtomT r.val

/-- a-side = {Raw whose leftmost atom is true}. -/
def aSide : List Raw := depthLe2List.filter Raw.leftmostAtom

/-- b-side = {Raw whose leftmost atom is false}. -/
def bSide : List Raw := depthLe2List.filter (fun r => !Raw.leftmostAtom r)

/-- ★★★ **Bipartition capstone**: depth-≤-2 Raw count (= 5) splits
    `(3, 2)` by leftmost-atom rule, matching `(d, NS, NT) = (5, 3, 2)`.

    Bundles per-element leftmost values, per-side counts, the
    full (3 + 2 = 5) identity, and the atomicity geometric match. -/
theorem raw_atomicity_geometric_match :
    -- Per-element leftmost atoms
    Raw.leftmostAtom Raw.a = true
    ∧ Raw.leftmostAtom Raw.b = false
    ∧ Raw.leftmostAtom s_ab = true
    ∧ Raw.leftmostAtom s_a_ab = true
    ∧ Raw.leftmostAtom s_b_ab = false
    -- Side counts
    ∧ aSide.length = 3
    ∧ bSide.length = 2
    -- Full identity 3 + 2 = depthLe2List.length = 5
    ∧ aSide.length + bSide.length = 5
    ∧ depthLe2List.length = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  <;> first | rfl | decide

end E213.Lib.Math.Foundations.UniverseChain.RawBipartition
