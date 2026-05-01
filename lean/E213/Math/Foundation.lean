import E213.Research.Real213.Core
import E213.Research.Real213.Equiv
import E213.Research.Real213.Const
import E213.Research.Real213.Order
import E213.Research.Real213.OrderExtra
import E213.Research.Real213.Sign

/-!
# E213.Math.Foundation: Real213 type-level foundation (Phase A)

Real213 type, equivalence, constant embedding, order, sign.

## Library status: STABLE

- Real213 type definition.
- Equivalence (refl/symm/trans + Setoid instance).
- Constant Raw embedding.
- Order (le, lt, antisymm via Bool case-analysis).
- Sign (zero, positive).

All ≤ propext.  Type-level foundation of 213-native ℝ.
-/
