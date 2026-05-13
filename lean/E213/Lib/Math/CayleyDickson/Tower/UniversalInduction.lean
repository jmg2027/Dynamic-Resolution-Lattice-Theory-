import E213.Theory.CDDouble.UniversalOrder4
import E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzOrder4Monopoly
import E213.Lib.Math.CayleyDickson.Levels.CayleyOrder4Monopoly
import E213.Lib.Math.CayleyDickson.Tower.Order4Monopoly_L4T
import E213.Lib.Math.CayleyDickson.Tower.Order4Monopoly_L5T
import E213.Lib.Math.CayleyDickson.Tower.Order4Monopoly_L6T

/-!
# Universal CDDouble Induction — explicit ∀-quantified per layer pair

The generic `cdd_lift_squared` theorem applies at any layer; this module
provides explicit per-layer-pair ∀-statements as decidable witnesses.

Each statement: "for ALL units of layer L_{n-1}, the lifted (0, u) at
layer L_n has order 4". Decidable via finite list enumeration.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.UniversalInduction

open E213.Lib.Math.CayleyDickson.ZSqrtMinus2
open E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Lib.Math.CayleyDickson.Levels.Cayley

/-- ★ Type A L3 → L4: every Lipschitz unit lifted to Cayley right has
    its image squaring to -1 (= cay_minus_one). -/
theorem typeA_L3_L4_lift_mechanism :
    ∀ u ∈ lip_units, cay_right u * cay_right u = cay_minus_one := by decide

/-- ★ Type B L4 → L5: every L4T unit lifted to L5T right squares to -1. -/
theorem typeB_L4_L5_lift_mechanism :
    ∀ u ∈ L4T_units, L5T_right u * L5T_right u = L5T_minus_one := by decide

set_option maxHeartbeats 4000000 in
/-- ★ Type B L5 → L6: every L5T unit lifted to L6T right squares to -1. -/
theorem typeB_L5_L6_lift_mechanism :
    ∀ u ∈ L5T_units, L6T_right u * L6T_right u = L6T_minus_one := by decide

/-- ★★ INDUCTION SUMMARY: across multiple Type/layer combinations, the
    cdd_lift_squared mechanism is concretely instantiated. The ∀ n
    proof is the universal cdd_lift_squared (Theory/CDDouble/Universal
    Order4); these per-layer theorems are its concrete witnesses. -/
theorem CDDouble_inductive_summary :
    (∀ u ∈ lip_units, cay_right u * cay_right u = cay_minus_one) ∧
    (∀ u ∈ L4T_units, L5T_right u * L5T_right u = L5T_minus_one) :=
  ⟨typeA_L3_L4_lift_mechanism, typeB_L4_L5_lift_mechanism⟩

end E213.Lib.Math.CayleyDickson.Tower.UniversalInduction
