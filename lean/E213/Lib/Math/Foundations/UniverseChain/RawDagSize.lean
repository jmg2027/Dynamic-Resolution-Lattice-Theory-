import E213.Lib.Math.Foundations.UniverseChain.RawDepth3

/-!
# dagSize: the event-cost fold and where sharing begins (∅-axiom)

The growth system creates each term **once**, so an object's history
is a DAG, not a tree: `Raw.leaves` (tree fold) overcounts shared
history and has no event-cost meaning.  The asynchronous-native
per-object stratum is `dagSize` = the number of *distinct* composite
subterms — the fused event cost of constructing the term.

One fold structure, three algebras: `depth` (max-plus), `leaves`
(additive), and `dagSize` (subterm-set algebra read through the
cardinality Lens).  Census over all 12 terms of depth ≤ 3:

  `depth ≤ dagSize ≤ leaves − 1`,

with the right inequality strict exactly where sharing occurs —
first at depth 3, at exactly the 3 terms that reuse `a/b` twice
(`(a/(a/b))/(b/(a/b))`, `(a/b)/(a/(a/b))`, `(a/b)/(b/(a/b))`).
-/

namespace E213.Lib.Math.Foundations.UniverseChain.RawDagSize

open E213.Theory
open E213.Term.Internal (Tree)
open E213.Lib.Math.Foundations.UniverseChain.RawDepthCount
  (depthLe2List s_ab s_a_ab s_b_ab)
open E213.Lib.Math.Foundations.UniverseChain.RawDepth3
  (depthLe3List t1 t2 t3 t4 t5 t6 t7)

-- Self-contained Bool membership / union (the core `∈`-decidability
-- instance for lists routes through propext; these stay PURE).

def memB (t : Tree) : List Tree → Bool
  | [] => false
  | x :: l => decide (t = x) || memB t l

def insertU (t : Tree) (l : List Tree) : List Tree :=
  if memB t l then l else t :: l

def unionU : List Tree → List Tree → List Tree
  | [], r => r
  | x :: l, r => insertU x (unionU l r)

/-- Distinct composite subterms of a Tree. -/
def compSubs : Tree → List Tree
  | .a => []
  | .b => []
  | .slash x y => insertU (.slash x y) (unionU (compSubs x) (compSubs y))

/-- The event-cost fold: number of distinct composite subterms =
    number of fused fire events any run needs to construct the term. -/
def dagSize (r : Raw) : Nat := (compSubs r.val).length

/-- ★ **dagSize census, depth ≤ 3** (values): no sharing through
    depth 2 (`dagSize` = composite-position count); at depth 3 the
    full join costs 4 (not 5) and the `a/b`-reusing terms cost 3
    (not 4). -/
theorem dag_census :
    dagSize Raw.a = 0 ∧ dagSize Raw.b = 0
    ∧ dagSize s_ab = 1 ∧ dagSize s_a_ab = 2 ∧ dagSize s_b_ab = 2
    ∧ dagSize t1 = 4
    ∧ dagSize t2 = 3 ∧ dagSize t3 = 3 ∧ dagSize t4 = 3
    ∧ dagSize t5 = 3 ∧ dagSize t6 = 3 ∧ dagSize t7 = 3 := by decide

/-- ★★ **The fold sandwich** over every term of depth ≤ 3:
    `depth ≤ dagSize ≤ leaves − 1` (stated additively). -/
theorem dag_sandwich_le3 :
    depthLe3List.all (fun r =>
      decide (r.depth ≤ dagSize r)
      && decide (dagSize r + 1 ≤ r.leaves)) = true := by decide

/-- ★★ **Sharing starts at depth 3, at exactly three terms**: the
    strict gap `dagSize + 1 < leaves` filters `depthLe3List` to the
    three terms reusing `a/b` — the full join `t1` and the two
    `(a/b)`-against-depth-2 contrasts `t4`, `t7`.  Through depth 2
    the tree-Lens and the DAG-Lens agree; from depth 3 they split,
    and `leaves` stops measuring event cost. -/
theorem sharing_starts_at_depth3 :
    depthLe3List.filter (fun r => decide (dagSize r + 2 ≤ r.leaves))
      = [t1, t4, t7] := by decide

end E213.Lib.Math.Foundations.UniverseChain.RawDagSize
