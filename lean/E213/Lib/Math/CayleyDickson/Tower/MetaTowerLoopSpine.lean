import E213.Lib.Math.CayleyDickson.Tower.UniversalOrderGrowth
import E213.Lib.Math.CayleyDickson.Tower.UniversalOrderGrowthC
import E213.Lib.Math.CayleyDickson.Tower.AlgebraTowerAsymptote

/-!
# Meta-CD-tower loop spine

The classical Cayley–Dickson tower (Type A: `ZI → Lipschitz → Cayley →
Sedenion → …`, dims `2,4,8,16,…`) is one column of a wider family of
parallel towers (Type A over `ℤ[i]`, Type B over `ℤ[√-2]`, Type C over
`ℤ[ω]`).  The invariant tracked here is the **±basis-doubling Moufang
loop** of each cell — the loop `cay_units := lip_units.map cay_left ++
lip_units.map cay_right` and its analogues, read through the order
distribution.  (This is the canonical doubled-basis loop, *not* the full
arithmetic unit group — e.g. the integer octonions have 240 units, while
the basis loop here has 16; the statements below are about the basis
loop, which is exactly what the CD doubling generates.)

Three structural facts, all naming-free at the level of *which loop
appears* (order distribution) and *at what dimension*:

  * **loop class ≠ dimension.**  The same basis loop occurs at different
    dimensions across columns: `{1,1,14}` (order-4 count 14) is the loop
    of `Cayley` (Type A, dim 8) and of `L5T` (Type B, dim 16); `{1,1,30}`
    is the loop of `Sedenion` (Type A, dim 16) and of `L6T` (Type B, dim
    32).  Type B realises each loop at double the dimension of Type A.

  * **Type A is a sparse section.**  At *equal* dimension the columns
    carry *different* loops: at dim 8, `Cayley` ({1,1,14}) ≠ `L4T`
    ({1,1,6}); at dim 16, `Sedenion` ({1,1,30}) ≠ `L5T` ({1,1,14}).  The
    loop classes realised by Type A are a *proper subset* of those
    realised by Type B — Type A omits the bottom rung that Type B's
    `ℤ[√-2]` (units `{±1}`) supplies.  (The further gloss "constant `+1`
    level offset / `n ↦ n+1`" is a *description* of this single
    equal-dimension gap; it is not an extra fact, and it depends on the
    arbitrary level labels — the dimension-indexed statement above is the
    naming-free content.)

  * **the spine branches.**  Type C (Eisenstein, seed `ℤ[ω]`,
    `ω²+ω+1=0`) carries 3-torsion (order-3 units) that the dyadic columns
    (Types A/B) do not, *and* a different order-4 count sequence
    (`6,18,42` vs dyadic `6,14,30`).  So the loop family is not a single
    chain but branches by base discriminant (dyadic `Z₂,Z₄,Q₈,…` vs
    Eisenstein `Z₆,Dic₃,…`).

These reads are bundled as ∅-axiom theorems, assembled from the per-level
order distributions without re-deciding the expensive carriers.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.MetaTowerLoopSpine

open E213.Lib.Math.CayleyDickson.ZSqrtMinus2
open E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Lib.Math.CayleyDickson.Levels.Cayley
open E213.Lib.Math.CayleyDickson.Levels.Sedenion
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad

/-- ★ **Meta-CD-tower loop-spine structure.**  Type A's basis-loop
    classes are a proper, branch-restricted subset of Type B's:

    1. Type B realises Type A's basis loop at double the dimension, on
       three loop classes: `Lipschitz`(dim4) and `L4T`(dim8) share count
       6; `Cayley`(dim8) and `L5T`(dim16) share 14; `Sedenion`(dim16) and
       `L6T`(dim32) share 30.  The same relation across three classes
       excludes a non-linear (e.g. Fibonacci) re-indexing.
    2. At *equal* dimension the columns carry *different* loops: dim 8,
       `Cayley`(14) ≠ `L4T`(6); dim 16, `Sedenion`(30) ≠ `L5T`(14).  So
       Type A omits the bottom loop rung that Type B supplies.
    3. The dyadic column (here `Cayley`) has no 3-torsion, while the
       Eisenstein column (`ZOmegaDouble`) does — the loop family branches
       by base discriminant. -/
theorem meta_tower_loop_spine :
    -- (1) SHIFT alignment over three rungs — same loop, B one doubling above A.
    (lip_units.countP (fun u => lip_orderOf u = 4)
       = L4T_units.countP (fun u => L4T_orderOf u = 4))
    ∧ (cay_units.countP (fun u => cay_orderOf u = 4)
       = L5T_units.countP (fun u => L5T_orderOf u = 4))
    ∧ (sed_units.countP (fun u => sed_orderOf u = 4)
       = L6T_units.countP (fun u => L6T_orderOf u = 4))
    -- (2) exact +1 offset — equal dimension, different loop (two witnesses).
    ∧ (cay_units.countP (fun u => cay_orderOf u = 4)
       ≠ L4T_units.countP (fun u => L4T_orderOf u = 4))
    ∧ (sed_units.countP (fun u => sed_orderOf u = 4)
       ≠ L5T_units.countP (fun u => L5T_orderOf u = 4))
    -- (3) branching — dyadic spine has no 3-torsion, Eisenstein does.
    ∧ (cay_units.countP (fun u => cay_orderOf u = 3) = 0)
    ∧ (zod_units.countP (fun u => zod_orderOf u = 3) ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (lip_order_distribution.2.2.1).trans (L4T_order_distribution.2.2.1).symm
  · exact (cay_order_distribution.2.2.1).trans (L5T_order_distribution.2.2.1).symm
  · exact (sed_order_distribution.2.2.1).trans (L6T_order_distribution.2.2.1).symm
  · rw [cay_order_distribution.2.2.1, L4T_order_distribution.2.2.1]; decide
  · rw [sed_order_distribution.2.2.1, L5T_order_distribution.2.2.1]; decide
  · decide
  · decide

/-- ★ **No dyadic ↔ Eisenstein basis-loop isomorphism.**  The order-3
    count is an isomorphism invariant of a finite loop: any
    `orderOf`-preserving bijection equalises it.  It vanishes on the
    dyadic basis loops (`Lipschitz`, `Cayley`) and equals `2` on the
    Eisenstein ones (`ZOmegaDouble`, `ZOmegaQuad`), so no dyadic basis
    loop is isomorphic to any Eisenstein one — the two branches share no
    cell.  This is the named obstruction behind "the loop family branches
    by base discriminant". -/
theorem no_cross_branch_loop_iso :
    (lip_units.countP (fun u => lip_orderOf u = 3) = 0)
    ∧ (cay_units.countP (fun u => cay_orderOf u = 3) = 0)
    ∧ (zod_units.countP (fun u => zod_orderOf u = 3) = 2)
    ∧ (zoq_units.countP (fun u => zoq_orderOf u = 3) = 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

open E213.Lib.Math.CayleyDickson.Tower.AlgebraTowerAsymptote

/-- ★ **The `ℤ[√5]` asymptote classifies the branch, not the column.**
    `asymptote_ab` is *constant* on the dyadic branch — `A = B = (2,0)`,
    blind to the `A ↔ B` within-branch column shift — and *distinct*
    across the three branch classes `{A,B}`, `{C}`, `{D}`.  So the
    asymptote is a branch (base-discriminant-class) invariant; it does
    not see the loop-spine offset between Type A and Type B.

    (The verified classifier is the rank `ω(unitOrder) − 1 + nonAbelian`
    behind `asymptote_ab`, *not* a base discriminant fed through the
    Möbius `disc P = 5`; `cd_mobius_bridge_master` ties only the `C`/`D`
    asymptotes to `P`-invariants, never the dyadic `(2,0)`.) -/
theorem asymptote_classifies_branch :
    asymptote_ab .A = asymptote_ab .B
    ∧ asymptote_ab .A ≠ asymptote_ab .C
    ∧ asymptote_ab .A ≠ asymptote_ab .D
    ∧ asymptote_ab .C ≠ asymptote_ab .D := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Tower.MetaTowerLoopSpine
