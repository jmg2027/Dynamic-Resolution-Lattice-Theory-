import E213.Meta.SelfRecognising
import E213.Math.CayleyDickson.ZI
import E213.Math.CayleyDickson.ZIDomain
import E213.Math.CayleyDickson.ZIHom
import E213.Meta.Tactic.DeriveConjugationCodomain

/-!
# Research: `ZI` as `ConjugationCodomain` instance

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

derive_conjugation_codomain ZI with_bases I negI
