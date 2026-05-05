import E213.Math.Tactic.QuadExtension
import E213.Meta.Tactic.VerifyConjugation

/-!
# Tests: `quad_extension D` parametric macro + `#verify_conjugation`

Each `quad_extension N` registers `ConjugationCodomain (ZSqrt N)`.
We verify with both strong checks:
- `example : _ := inferInstance` (term-level synthesis)
- `#verify_conjugation` (command-level diagnostic)
-/

open E213.Tactic E213.Research

quad_extension 11
quad_extension 13
quad_extension 17

-- inferInstance forces full term-level elaboration + synthesis.
example : E213.Meta.ConjugationCodomain (ZSqrt 11) := inferInstance
example : E213.Meta.ConjugationCodomain (ZSqrt 13) := inferInstance
example : E213.Meta.ConjugationCodomain (ZSqrt 17) := inferInstance

-- `#verify_conjugation` should succeed for each registered instance.
#verify_conjugation (ZSqrt 11)
#verify_conjugation (ZSqrt 13)
#verify_conjugation (ZSqrt 17)
