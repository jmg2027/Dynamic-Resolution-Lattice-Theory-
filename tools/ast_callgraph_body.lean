/-
Expr-level call-graph extractor for E213.*
Auto-included by tools/ast_callgraph_scan.py after the import block.
For every E213.* constant with a `value?`, walks its elaborated Expr
and emits one row per (caller, callee_const_name, count).
-/

open Lean Meta

namespace E213.AstCallGraph

partial def collectConsts (e : Expr) (acc : Std.HashMap Name Nat) :
    Std.HashMap Name Nat :=
  match e with
  | .const n _ =>
    acc.insert n ((acc.get? n |>.getD 0) + 1)
  | .app f a =>
    collectConsts a (collectConsts f acc)
  | .lam _ t b _ =>
    collectConsts b (collectConsts t acc)
  | .forallE _ t b _ =>
    collectConsts b (collectConsts t acc)
  | .letE _ t v b _ =>
    collectConsts b (collectConsts v (collectConsts t acc))
  | .proj _ _ inner =>
    collectConsts inner acc
  | .mdata _ inner =>
    collectConsts inner acc
  | _ => acc

def isE213 (n : Name) : Bool := n.getRoot == `E213

def runScan : MetaM Unit := do
  let env ← getEnv
  let mut nDecls : Nat := 0
  let mut nEdges : Nat := 0
  IO.println s!"=== AST-CALLGRAPH-BEGIN ==="
  for (name, info) in env.constants.toList do
    unless isE213 name do continue
    let some val := info.value? | continue
    nDecls := nDecls + 1
    let counts := collectConsts val {}
    for (callee, count) in counts.toList do
      IO.println s!"E\t{name}\t{callee}\t{count}"
      nEdges := nEdges + 1
  IO.println s!"# decls\t{nDecls}"
  IO.println s!"# edges\t{nEdges}"
  IO.println s!"=== AST-CALLGRAPH-END ==="

end E213.AstCallGraph

#eval E213.AstCallGraph.runScan
