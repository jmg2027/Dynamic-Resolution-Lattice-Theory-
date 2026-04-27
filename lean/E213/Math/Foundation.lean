import E213.Research.Real213
import E213.Research.Real213Equiv
import E213.Research.Real213Const
import E213.Research.Real213Order
import E213.Research.Real213OrderExtra
import E213.Research.Real213Sign

/-!
# E213.Math.Foundation: Real213 type-level foundation (Phase A)

Real213 type, equivalence, constant embedding, order, sign.

## Library status: STABLE

- Real213 type definition.
- Equivalence (refl/symm/trans + Setoid instance).
- Constant Raw embedding.
- Order (le, lt, antisymm via Bool case-analysis).
- Sign (zero, positive).

모두 ≤ propext.  213-native ℝ 의 type-level foundation.
-/
