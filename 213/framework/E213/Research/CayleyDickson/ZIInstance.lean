import E213.Meta.SelfRecognising
import E213.Research.CayleyDickson.ZI
import E213.Research.CayleyDickson.ZIDomain
import E213.Research.CayleyDickson.ZIHom
import E213.Tactic.DeriveR4Codomain

/-!
# Research: `ZI` as `R4Codomain` instance

The instance is **derived** by the `derive_r4_codomain` elab
(Phase B1).  By naming convention, the elab finds:
- `ZI.I`, `ZI.negI` (bases)
- `ZI.mul`, `ZI.conj`
- `ZI.mul_comm`, `ZI.no_zero_div`,
  `ZI.conj_conj`, `ZI.conj_ne_id`, `ZI.conj_mul`,
  `ZI.conj_I`, `ZI.conj_negI`

and synthesises the 13-field `instance`.
-/

open E213.Tactic E213.Research

derive_r4_codomain ZI with_bases I negI
