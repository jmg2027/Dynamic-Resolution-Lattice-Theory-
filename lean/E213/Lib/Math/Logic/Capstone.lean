import E213.Lib.Math.Logic.DiagonalBase
import E213.Lib.Math.Logic.ChildSelection

/-!
# Reverse Mathematics 213 — Phase GD: the ledger capstone

Marathon field 17, Phase GD (`blueprints/math/17_reverse_math_213.md`).

The 213-native reverse-mathematics ledger: each theorem calibrated by the omniscience
decision it costs, on the residue's own carriers.  The spine, as one ∅-axiom witness:

| rung | result | cost |
|---|---|---|
| **free interior** | `cantor_stream_not_enumerable` (Cantor diagonal); `object1_not_surjective` | **none** |
| **omniscience base** | `lpo_imp_wlpo`, `lpo_imp_mp` (LPO ⟹ WLPO, MP) | structural |
| **Π⁰₁ decision** | `lpo_decides_pi01` — deciding "infinite-below" | **LPO** |
| **König selection** | `lpo_infChildExistsN` — an infinite node has an infinite child (downward-closed tree) | **LPO** (LLPO suffices) |

This reproduces the reverse-math calibration spirit (Simpson SOSOA; the omniscience
hierarchy) **inside the residue**, ∅-axiom — the legibility bridge to recognized
mathematical logic.  Companions: the compactness ↔ König local identity
(`Lib/Math/Combinatorics/KonigConditional.infChildExists_iff_finiteSubcover`), the p-adic /
2-adic escapes (`Padic/NuEscape`), and the essay `theory/essays/foundations/the_one_diagonal.md`.
-/

namespace E213.Lib.Math.Logic

/-- ★★★ **The reverse-math ledger spine, ∅-axiom.**  Bundles the cost-0 diagonal base, the
    omniscience-base implications, the LPO Π⁰₁-decision, and the LPO König child-selection
    (under tree-monotonicity) into one witness. -/
theorem reverse_math_ledger :
    (∀ e : Nat → Nat → Bool, ∃ d : Nat → Bool, ∀ k, ∃ n, d n ≠ e k n)
    ∧ (LPO → WLPO)
    ∧ (LPO → MP)
    ∧ (∀ h : Nat → Bool, LPO → (∀ n, h n = true) ∨ ¬ (∀ n, h n = true))
    ∧ (∀ T : List Bool → Bool, LPO → LevelAntitone T → ∀ s, InfB T s →
        InfB T (s ++ [false]) ∨ InfB T (s ++ [true])) :=
  ⟨cantor_stream_not_enumerable,
   lpo_imp_wlpo,
   lpo_imp_mp,
   fun h hlpo => lpo_decides_pi01 hlpo h,
   fun T hlpo hmono s hs => lpo_infChildExistsN hlpo T hmono s hs⟩

end E213.Lib.Math.Logic
