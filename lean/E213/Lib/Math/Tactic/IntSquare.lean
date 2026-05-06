import E213.Lib.Math.NatHelpers.IntHelpers

/-!
# Tactic: `int_square`

Convenience macro that closes integer-self-multiplication
goals via `IntHelpers`:
- `0 ≤ a * a`
- `a * a = 0 ↔ a = 0`

Pure dispatch wrapper; no new mathematical content.

## Usage

```
open E213.Tactic
example (a : Int) : 0 ≤ a * a := by int_square
example (a : Int) : a * a = 0 ↔ a = 0 := by int_square
```
-/

namespace E213.Tactic

scoped macro "int_square" : tactic => `(tactic|
  first
    | exact E213.Lib.Math.NatHelpers.IntHelpers.mul_self_nonneg _
    | exact E213.Lib.Math.NatHelpers.IntHelpers.mul_self_eq_zero)

end E213.Tactic
