import E213.Lib.Math.Foundations.UniverseChain.RawDepth3

/-!
# Past-completeness: what distinguishes depth ≤ 2 (∅-axiom)

No run of the asynchronous growth system is forced through the
5-element depth-≤2 census as a snapshot (a run may build a depth-3
term before completing depth 2).  What *does* distinguish the
depth-≤2 downset is **order-internal**: every term of depth 1 and 2
contains the whole previous depth-downset in its causal past
(= subterm closure), while at depth 3 this fails for 6 of the 7
terms — the sole exception being the full join
`(a/(a/b)) / (b/(a/b))`.

So "forcing ends at level 2" is a property of the ancestor order,
not of any run or any privileged truncation depth.  At the largest
past-complete depth-downset the population is the census value 5,
and the chart-Lens coordinate readout (population minus the one
connected component) is 4 — the same 5 → 4 reading as the
self-pointing-axis omission of the geometrization ansatz.
-/

namespace E213.Lib.Math.Foundations.UniverseChain.RawPastCompleteness

open E213.Theory
open E213.Term.Internal (Tree)
open E213.Lib.Math.Foundations.UniverseChain.RawDepthCount
  (depthLe2List s_ab s_a_ab s_b_ab)
open E213.Lib.Math.Foundations.UniverseChain.RawDepth3
  (t1 t2 t3 t4 t5 t6 t7)

/-- Reflexive subterm test on the Tree carrier. -/
def subtermT (s : Tree) : Tree → Bool
  | .a => decide (s = .a)
  | .b => decide (s = .b)
  | .slash x y =>
      decide (s = .slash x y) || subtermT s x || subtermT s y

/-- Reflexive subterm test on Raw: `s` lies in the causal past of
    `t` (the reflexive-transitive closure of `Lambek.IsPart`). -/
def subtermR (s t : Raw) : Bool := subtermT s.val t.val

/-- `t` is past-complete over `prev`: every element of `prev` lies
    in `t`'s causal past. -/
def pastOf (prev : List Raw) (t : Raw) : Bool :=
  prev.all (fun s => subtermR s t)

/-- ★ **Depth ≤ 2 is past-complete**: each depth-1/2 term contains
    the entire previous depth-downset among its subterms. -/
theorem depthLe2_past_complete :
    pastOf [Raw.a, Raw.b] s_ab = true
    ∧ pastOf [Raw.a, Raw.b, s_ab] s_a_ab = true
    ∧ pastOf [Raw.a, Raw.b, s_ab] s_b_ab = true := by decide

/-- ★★ **Past-completeness fails at depth 3, with one exception**:
    among the 7 depth-3 terms, exactly the full join
    `t1 = (a/(a/b)) / (b/(a/b))` contains the whole depth-≤2
    downset; the other six each miss one of the two depth-2 swap
    partners (witnesses bundled). -/
theorem depth3_boundary :
    ([t1, t2, t3, t4, t5, t6, t7].filter (pastOf depthLe2List)) = [t1]
    -- the six failures, each with its missing depth-2 term
    ∧ subtermR s_b_ab t2 = false ∧ subtermR s_b_ab t3 = false
    ∧ subtermR s_b_ab t4 = false ∧ subtermR s_a_ab t5 = false
    ∧ subtermR s_a_ab t6 = false ∧ subtermR s_a_ab t7 = false := by
  decide

/-- The boundary in one line: the largest past-complete
    depth-downset has population 5 (the census value), and its
    chart readout is `5 − 1 = 4`. -/
theorem past_complete_boundary_population :
    depthLe2List.length = 5 ∧ depthLe2List.length - 1 = 4 := by decide

end E213.Lib.Math.Foundations.UniverseChain.RawPastCompleteness
