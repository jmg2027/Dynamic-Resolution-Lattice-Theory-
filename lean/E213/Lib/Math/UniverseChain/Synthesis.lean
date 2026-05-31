import E213.Lib.Math.UniverseChain.Atomicity
import E213.Lib.Math.UniverseChain.Decomposition
import E213.Lib.Math.UniverseChain.PairAxes
import E213.Lib.Math.UniverseChain.Recursion
import E213.Lib.Math.UniverseChain.Universe
import E213.Lib.Math.Cohomology.Fractal.ConfigCount

/-!
# Synthesis — Atomicity to the level-2 configuration count (∅-axiom)

Five steps, each ∅-axiom, composed in order:

| Step | Statement                                                   |
|------|-------------------------------------------------------------|
| 1    | Atomic n ⟺ n = 5                                            |
| 2    | 5 = 2·1 + 3·1, alive decomp unique with `(a, b) = (1, 1)`  |
| 3    | Two axes: NS = 3, NT = 2, with `NS + NT = d = 5`            |
| 4    | Each vertex itself a Δ⁴ (recursion); self-ref level `L = d²`|
| 5    | Each leaf carries d states ⇒ total = `d^(d²) = 5²⁵ = configCount 2` |

Every step's witness is `rfl` or `decide`; no axiom dependency.
-/

namespace E213.Lib.Math.UniverseChain.Synthesis

open E213.Lib.Math.UniverseChain.Atomicity (Atomic atomic_iff_five)
open E213.Lib.Math.UniverseChain.Decomposition
  (decomp_five_one_one one_one_alive unique_alive_decomp)
open E213.Lib.Math.UniverseChain.PairAxes (axes_sum_eq_total)
open E213.Lib.Math.Cohomology.Fractal.Level (numV)
open E213.Lib.Math.UniverseChain.Recursion (numV_at_d_squared)
open E213.Lib.Math.Cohomology.Fractal.ConfigCount (configCount configCount_two)
open E213.Lib.Physics.Simplex.Counts (d NS NT)

/-- ★★ Step 1 ⇒ Step 2: atomicity → unique (1, 1) shape. -/
theorem step1_to_step2 :
    Atomic 5 ∧ ∀ a b, E213.Theory.Atomicity.Five.Decomp 5 a b
                       ∧ E213.Theory.Atomicity.Five.IsAlive a b
                     → a = 1 ∧ b = 1 :=
  ⟨E213.Theory.Atomicity.Five.atomic_five, unique_alive_decomp⟩

/-- ★★ Step 2 ⇒ Step 3: (1, 1) labels two pieces of sizes 3, 2. -/
theorem step2_to_step3 : NS = 3 ∧ NT = 2 ∧ NS + NT = d :=
  ⟨rfl, rfl, axes_sum_eq_total⟩

/-- ★★ Step 3 ⇒ Step 4: total `d` recurses to `d^L` vertices at
    level `n = d * d`. -/
theorem step3_to_step4 :
    (d * d : Nat) = 25 ∧ numV (d * d) = d ^ (d * d) := by
  refine ⟨rfl, ?_⟩
  show 5 ^ (d * d) = d ^ (d * d)
  rfl

/-- ★★ Step 4 ⇒ Step 5: each vertex d-stated → `configCount 2 = d^(d²)`. -/
theorem step4_to_step5 :
    configCount 2 = d ^ (d * d) ∧ configCount 2 = 298023223876953125 := by
  refine ⟨?_, configCount_two⟩
  decide

/-- ★★★ **Full chain**: atomicity ⇒ `configCount 2 = 5²⁵`. -/
theorem universe_chain :
    (∀ n, Atomic n ↔ n = 5)
    ∧ (NS = 3 ∧ NT = 2 ∧ NS + NT = d)
    ∧ (d * d : Nat) = 25
    ∧ configCount 2 = d ^ (d * d)
    ∧ configCount 2 = 298023223876953125 := by
  refine ⟨atomic_iff_five, ?_, rfl, ?_, configCount_two⟩
  · exact ⟨rfl, rfl, axes_sum_eq_total⟩
  · decide

end E213.Lib.Math.UniverseChain.Synthesis
