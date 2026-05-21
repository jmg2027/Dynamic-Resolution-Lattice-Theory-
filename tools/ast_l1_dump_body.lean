/-
Dumps the Expr body of the four L1 LeibnizAlgLift siblings
+ LeibnizAlgLift21 (5th, the smaller variant) for structural
diffing.  Emits first 4000 chars of each Expr.dbgToString to
stdout.
-/

open Lean Meta

namespace E213.AstL1Dump

def TARGETS : List Name :=
  [`E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift.leibniz_via_β_decomp_lens,
   `E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21Alpha.leibniz_via_α_decomp_21,
   `E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22.leibniz_via_β_decomp_22,
   `E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22Alpha.leibniz_via_α_decomp_22,
   `E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21.leibniz_via_β_decomp_21]

partial def normSkel : Expr → Expr
  | .mdata _ e        => normSkel e
  | .app f a          => .app (normSkel f) (normSkel a)
  | .lam _ t b bi     => .lam `_ (normSkel t) (normSkel b) bi
  | .forallE _ t b bi => .forallE `_ (normSkel t) (normSkel b) bi
  | .letE _ t v b nd  => .letE `_ (normSkel t) (normSkel v) (normSkel b) nd
  | .proj s i e       => .proj s i (normSkel e)
  | .const n _        => .const n []
  | .fvar _           => .const `_F []
  | .mvar _           => .const `_M []
  | .sort _           => .sort .zero
  | e@(.bvar _)       => e
  | e@(.lit _)        => e

def runScan : MetaM Unit := do
  let env ← getEnv
  IO.println s!"=== L1-DUMP-BEGIN ==="
  for name in TARGETS do
    let some info := env.constants.find? name | continue
    let some val := info.value? | continue
    let normalised := normSkel val
    let s := normalised.dbgToString
    IO.println s!"--- {name} (length {s.length}) ---"
    IO.println (s.take 1500)
    IO.println s!"--- (truncated; full length = {s.length}) ---"
  IO.println s!"=== L1-DUMP-END ==="

end E213.AstL1Dump

#eval E213.AstL1Dump.runScan
