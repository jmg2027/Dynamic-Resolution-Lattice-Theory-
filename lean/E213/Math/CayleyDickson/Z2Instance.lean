import E213.Meta.SelfRecognising
import E213.Math.CayleyDickson.ZSqrt2
import E213.Math.CayleyDickson.ZSqrt2Domain
import E213.Meta.Tactic.DeriveConjugationCodomain

/-!
# `Z2 = ℤ[√-2]` as `ConjugationCodomain` instance

Same `derive_conjugation_codomain` elab as ZIInstance.  The
naming convention finds Z2.I, Z2.negI, Z2.mul, Z2.conj plus the
required `mul_comm`, `no_zero_div`, `conj_*` lemmas.
-/

open E213.Tactic
open E213.Math.CayleyDickson.ZSqrt2
open E213.Math.CayleyDickson.ZSqrt2.Z2

derive_conjugation_codomain Z2 with_bases I negI
