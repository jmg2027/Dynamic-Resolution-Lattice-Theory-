import E213.Tactic.QuadExtension
import E213.Tactic.VerifyR4

/-!
# Tests: `quad_extension D` parametric macro + `#verify_r4`

Each `quad_extension N` registers `R4Codomain (ZSqrt N)`.
We verify with both strong checks:
- `example : _ := inferInstance` (term-level synthesis)
- `#verify_r4` (command-level diagnostic, after fix)
-/

open E213.Tactic E213.Research

quad_extension 11
quad_extension 13
quad_extension 17

-- inferInstance forces full term-level elaboration + synthesis.
example : E213.Meta.R4Codomain (ZSqrt 11) := inferInstance
example : E213.Meta.R4Codomain (ZSqrt 13) := inferInstance
example : E213.Meta.R4Codomain (ZSqrt 17) := inferInstance

-- `#verify_r4` should now also succeed (see VerifyR4 bugfix).
#verify_r4 (ZSqrt 11)
#verify_r4 (ZSqrt 13)
#verify_r4 (ZSqrt 17)
