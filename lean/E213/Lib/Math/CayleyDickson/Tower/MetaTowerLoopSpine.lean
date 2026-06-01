import E213.Lib.Math.CayleyDickson.Tower.UniversalOrderGrowth
import E213.Lib.Math.CayleyDickson.Tower.UniversalOrderGrowthC

/-!
# Meta-CD-tower loop spine

The classical Cayley–Dickson tower (Type A: `ZI → Lipschitz → Cayley →
Sedenion → …`, dims `2,4,8,16,…`) is one column of a wider family of
parallel towers (Type A over `ℤ[i]`, Type B over `ℤ[√-2]`, Type C over
`ℤ[ω]`).  Aligning cells `(Type, level)` by their **unit-loop class**
(the finite Moufang loop of ±basis units, read off the order
distribution) exhibits three structural facts:

  * **spine ≠ dimension.**  The *same* unit loop occurs at *different*
    dimensions across columns: the octonion loop `M₁₆` (order
    distribution `{1,1,14}`) is the unit loop of `Cayley` (Type A, dim 8)
    and of `L5T` (Type B, dim 16); `M₃₂` (`{1,1,30}`) is the unit loop of
    `Sedenion` (Type A, dim 16) and of `L6T` (Type B, dim 32).  Type B
    carries each loop one doubling above Type A — a constant `+1` offset
    over two independent rungs (the offset is linear, not Fibonacci).

  * **Type A is a sparse section.**  Hence at *equal* dimension the two
    columns carry *different* loops: at dim 16, `Sedenion` (Type A) is
    `M₃₂` while `L5T` (Type B) is `M₁₆`.  Type A is one loop-step ahead at
    every dimension; equivalently Type B carries the bottom `Z₂` rung
    (`ℤ[√-2]`, units `{±1}`) that Type A's `ℤ[i]` start does not.  So
    Type A realises the loop spine at the index positions `n ↦ n+1`.

  * **the spine branches.**  Type C (Eisenstein, seed `ℤ[ω]`,
    `ω²+ω+1=0`) carries 3-torsion (cyclotomic order-3 units) that the
    dyadic columns (Types A/B) do not.  The unit-loop spine is therefore
    not a single chain but a branching family indexed by base
    discriminant (dyadic `Z₂,Z₄,Q₈,M₁₆,…` vs Eisenstein
    `Z₆,Dic₃,M₂₄,…`).

This capstone bundles the three reads as one ∅-axiom theorem, assembled
from the per-level order distributions without re-deciding the expensive
carriers.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.MetaTowerLoopSpine

open E213.Lib.Math.CayleyDickson.ZSqrtMinus2
open E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Lib.Math.CayleyDickson.Levels.Cayley
open E213.Lib.Math.CayleyDickson.Levels.Sedenion
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble

/-- ★ **Meta-CD-tower loop-spine structure.**  Type A is a sparse,
    branch-restricted section of the unit-loop spine:

    1. Three independent SHIFT rungs align Type A with Type B at the
       unit-loop level, each with a constant `+1` dimension-doubling
       offset (B one doubling above A): `Lipschitz ≅ L4T` (`Q₈`, count
       6), `Cayley ≅ L5T` (`M₁₆`, 14), `Sedenion ≅ L6T` (`M₃₂`, 30).
       Three equal rungs over the measured range exclude any non-linear
       (e.g. Fibonacci) re-indexing.
    2. At *equal* dimension the columns carry *different* loops (two
       witnesses): at dim 8 `Cayley` (`M₁₆`, 14) ≠ `L4T` (`Q₈`, 6); at
       dim 16 `Sedenion` (`M₃₂`, 30) ≠ `L5T` (`M₁₆`, 14).  So Type A's
       index into the spine is `n ↦ n+1` — it skips the bottom rung.
    3. The dyadic spine (Type A, here `Cayley`) has no 3-torsion, while
       the Eisenstein spine (Type C, `ZOmegaDouble`) does — the spine
       branches by base discriminant. -/
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

end E213.Lib.Math.CayleyDickson.Tower.MetaTowerLoopSpine
