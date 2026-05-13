import E213.Meta.SelfRecognising
import E213.Lib.Math.CayleyDickson.Integer.ZI
import E213.Lib.Math.CayleyDickson.Integer.ZIDomain
import E213.Lib.Math.CayleyDickson.Integer.ZIHom
import E213.Meta.Tactic.DeriveConjugationCodomain

/-!
# `ZI` as `ConjugationCodomain` instance

The instance is **derived** by the `derive_conjugation_codomain`
elab (1).  By naming convention, the elab finds:
- `ZI.I`, `ZI.negI` (bases)
- `ZI.mul`, `ZI.conj`
- `ZI.mul_comm`, `ZI.no_zero_div`,
  `ZI.conj_conj`, `ZI.conj_ne_id`, `ZI.conj_mul`,
  `ZI.conj_I`, `ZI.conj_negI`

and synthesises the 13-field `instance`.
-/

open E213.Tactic
open E213.Lib.Math.CayleyDickson.Integer.ZI
open E213.Lib.Math.CayleyDickson.Integer.ZI.ZI

derive_conjugation_codomain ZI with_bases I negI
