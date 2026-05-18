import E213.Meta.Tactic.VerifyConjugation
import E213.Lib.Math.CayleyDickson.Integer.ConjugationInstances

/-!
# Tests: `#verify_conjugation` scans all six ConjugationCodomain witnesses.

After importing `ConjugationInstances` (which bundles ZI / Z2 /
ZOmega / ZSqrt witnesses), `#verify_conjugation` should succeed
for each registered type.  Verifies that typeclass synthesis
reaches every instance.

NB: depends transitively on `Theory.Raw` (for `Raw.fold_swap_hom`).
Full verification therefore requires the Raw build.
-/

open E213.Tactic
open E213.Lib.Math.CayleyDickson.Integer.ZI
open E213.Lib.Math.CayleyDickson.Integer.ZSqrt2
open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Integer.ZSqrt

-- Three concrete witnesses
#verify_conjugation ZI
#verify_conjugation Z2
#verify_conjugation ZOmega

-- Three parametric instances
#verify_conjugation (ZSqrt 3)
#verify_conjugation (ZSqrt 5)
#verify_conjugation (ZSqrt 7)
