/-
Type-signature dependency + sort/universe extractor for E213.*

For every E213.* constant, walks its TYPE Expr (not value) and
collects every Expr.const reference there.  Outputs one row per
(caller, callee_in_type, count_in_type) edge, plus a separate
summary row per caller with its sort classification.

This closes the encapsulation gap in G103 §1: every derivation
from Raw transits through CARRIER TYPES (Lens, Cochain, ...) even
when the proof body doesn't reference Raw atoms directly.  By
walking type Exprs we expose the structural dependency.
-/

open Lean Meta

namespace E213.AstTypeSig

partial def collectConsts (e : Expr) (acc : Std.HashMap Name Nat) :
    Std.HashMap Name Nat :=
  match e with
  | .const n _      => acc.insert n ((acc.get? n |>.getD 0) + 1)
  | .app f a        => collectConsts a (collectConsts f acc)
  | .lam _ t b _    => collectConsts b (collectConsts t acc)
  | .forallE _ t b _ => collectConsts b (collectConsts t acc)
  | .letE _ t v b _ => collectConsts b (collectConsts v (collectConsts t acc))
  | .proj _ _ inner => collectConsts inner acc
  | .mdata _ inner  => collectConsts inner acc
  | _ => acc

def isE213 (n : Name) : Bool := n.getRoot == `E213

/-- Classify a type's top sort: "Prop", "Type", "Sort", or "Other". -/
def classifyType (t : Expr) : String :=
  -- Find the codomain of the top forall-chain.
  let rec walkCodomain : Expr → Expr
    | .forallE _ _ b _ => walkCodomain b
    | e => e
  match walkCodomain t with
  | .sort .zero       => "Prop"
  | .sort (.succ .zero) => "Type"
  | .sort _           => "Sort"
  | _                 => "Other"

def runScan : MetaM Unit := do
  let env ← getEnv
  IO.println s!"=== AST-TYPESIG-BEGIN ==="
  for (name, info) in env.constants.toList do
    unless isE213 name do continue
    let t := info.type
    let counts := collectConsts t {}
    let sortClass := classifyType t
    -- Per-edge rows
    for (callee, count) in counts.toList do
      IO.println s!"T\t{name}\t{callee}\t{count}"
    -- Sort row
    IO.println s!"K\t{name}\t{sortClass}"
  IO.println s!"=== AST-TYPESIG-END ==="

end E213.AstTypeSig

#eval E213.AstTypeSig.runScan
