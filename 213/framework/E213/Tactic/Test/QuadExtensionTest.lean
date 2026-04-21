import E213.Tactic.QuadExtension

/-!
# Tests: `quad_extension D` parametric macro

Each `quad_extension N` registers `R4Codomain (ZSqrt N)`
for the natural `N > 0`.  The subsequent `example`s exercise
Lean's typeclass synthesis on those newly-registered instances
— a stronger check than the environment-level
`synthInstance?` used by `#verify_r4`.
-/

open E213.Tactic

quad_extension 11
quad_extension 13
quad_extension 17

-- inferInstance forces full term-level elaboration + synthesis.
example : E213.Meta.R4Codomain (E213.Research.ZSqrt 11) := inferInstance
example : E213.Meta.R4Codomain (E213.Research.ZSqrt 13) := inferInstance
example : E213.Meta.R4Codomain (E213.Research.ZSqrt 17) := inferInstance
