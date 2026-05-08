import E213.Lib.Math.UniverseChain.RawBipartition

/-!
# Raw inhabitants at depth ≤ 3 (∅-axiom)

Mingu's description:
> "점 두개 → 선 → 점 → 다른 점들과 연결 → 또 점 → ..."

Raw at depth ≤ 3: 12 canonical inhabitants.

Generation rule (Mingu's intuition formalised):
  each unordered pair of distinct Raws (x, y) becomes a new Raw
  `slash x y`.  New Raws can re-pair, producing yet more.

depth-3 elements (7) come from:
  * 1 pair of the two depth-2 elements: C(2, 2) = 1
  * 2 depth-2 × 3 depth-≤-1 pairs:    2 × 3 = 6
  Total: 7
-/

namespace E213.Lib.Math.UniverseChain.RawDepth3

open E213.Theory
open E213.Lib.Math.UniverseChain.RawDepthCount
  (s_ab s_a_ab s_b_ab depthLe2List)
open E213.Lib.Math.UniverseChain.RawBipartition (Raw.leftmostAtom)

/-! ## Depth-3 elements -/
def t1 : Raw := Raw.slash s_a_ab s_b_ab (by decide)
def t2 : Raw := Raw.slash Raw.a s_a_ab (by decide)
def t3 : Raw := Raw.slash Raw.b s_a_ab (by decide)
def t4 : Raw := Raw.slash s_ab s_a_ab (by decide)
def t5 : Raw := Raw.slash Raw.a s_b_ab (by decide)
def t6 : Raw := Raw.slash Raw.b s_b_ab (by decide)
def t7 : Raw := Raw.slash s_ab s_b_ab (by decide)

/-- All canonical Raws of depth ≤ 3. -/
def depthLe3List : List Raw := depthLe2List ++ [t1, t2, t3, t4, t5, t6, t7]

/-- ★ Count at depth ≤ 3: 12. -/
theorem depth_3_count : depthLe3List.length = 12 := by decide

/-- ★ All 12 distinct. -/
theorem depth_3_distinct : depthLe3List.Nodup := by decide

/-- ★ Each depth-3 element has depth = 3. -/
theorem depth_3_witnesses :
    t1.depth = 3 ∧ t2.depth = 3 ∧ t3.depth = 3 ∧ t4.depth = 3
    ∧ t5.depth = 3 ∧ t6.depth = 3 ∧ t7.depth = 3 :=
  ⟨by decide, by decide, by decide, by decide,
   by decide, by decide, by decide⟩

/-! ## Bipartition by leftmost atom at depth ≤ 3 -/

/-- a-side at depth ≤ 3. -/
def aSide3 : List Raw := depthLe3List.filter Raw.leftmostAtom

/-- b-side at depth ≤ 3. -/
def bSide3 : List Raw := depthLe3List.filter (fun r => !Raw.leftmostAtom r)

/-- ★ a-side count at depth ≤ 3: 8 (= 3 + 5). -/
theorem aSide3_count : aSide3.length = 8 := by decide

/-- ★ b-side count at depth ≤ 3: 4 (= 2 + 2). -/
theorem bSide3_count : bSide3.length = 4 := by decide

/-- ★ At depth ≤ 3 the (3, 2) ratio breaks: (8, 4) = 2:1. -/
theorem ratio_breaks :
    aSide3.length = 8 ∧ bSide3.length = 4
    ∧ ¬ (3 * bSide3.length = 2 * aSide3.length) :=
  ⟨aSide3_count, bSide3_count, by decide⟩

/-- ★★★ **Depth-3 capstone**: 12 inhabitants, (8, 4) bipartition. -/
theorem raw_depth_3_witness :
    depthLe3List.length = 12
    ∧ depthLe3List.Nodup
    ∧ aSide3.length = 8
    ∧ bSide3.length = 4 :=
  ⟨depth_3_count, depth_3_distinct, aSide3_count, bSide3_count⟩

end E213.Lib.Math.UniverseChain.RawDepth3
