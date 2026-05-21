/-
Expr-shape density extractor for E213.* declarations.

For every E213.* constant with a `value?` body, walks the
elaborated Expr and counts occurrences of each Expr constructor:
  · .app, .lam, .forallE, .letE, .proj, .mdata, .bvar,
    .fvar, .mvar, .const, .sort, .lit

Plus secondary metrics:
  · max depth of the Expr tree
  · total node count

Emits one TSV row per (caller, constructor, count) plus
a separate summary row per caller with depth + total.
-/

open Lean Meta

namespace E213.AstShape

structure Counts where
  app      : Nat := 0
  lam      : Nat := 0
  forallE  : Nat := 0
  letE     : Nat := 0
  proj     : Nat := 0
  mdata    : Nat := 0
  bvar     : Nat := 0
  fvar     : Nat := 0
  mvar     : Nat := 0
  const    : Nat := 0
  sort     : Nat := 0
  lit      : Nat := 0
  total    : Nat := 0
  maxDepth : Nat := 0

partial def walk (e : Expr) (depth : Nat) (c : Counts) : Counts :=
  let c := { c with total := c.total + 1,
                    maxDepth := Nat.max c.maxDepth depth }
  match e with
  | .app f a       => walk a (depth+1) (walk f (depth+1) { c with app := c.app + 1 })
  | .lam _ t b _   => walk b (depth+1) (walk t (depth+1) { c with lam := c.lam + 1 })
  | .forallE _ t b _ => walk b (depth+1) (walk t (depth+1) { c with forallE := c.forallE + 1 })
  | .letE _ t v b _ => walk b (depth+1) (walk v (depth+1) (walk t (depth+1) { c with letE := c.letE + 1 }))
  | .proj _ _ inner => walk inner (depth+1) { c with proj := c.proj + 1 }
  | .mdata _ inner => walk inner (depth+1) { c with mdata := c.mdata + 1 }
  | .bvar _        => { c with bvar := c.bvar + 1 }
  | .fvar _        => { c with fvar := c.fvar + 1 }
  | .mvar _        => { c with mvar := c.mvar + 1 }
  | .const _ _     => { c with const := c.const + 1 }
  | .sort _        => { c with sort := c.sort + 1 }
  | .lit _         => { c with lit := c.lit + 1 }

def isE213 (n : Name) : Bool := n.getRoot == `E213

def runScan : MetaM Unit := do
  let env ← getEnv
  IO.println s!"=== AST-SHAPE-BEGIN ==="
  for (name, info) in env.constants.toList do
    unless isE213 name do continue
    let some val := info.value? | continue
    let c := walk val 0 {}
    IO.println s!"S\t{name}\t{c.total}\t{c.maxDepth}\t{c.app}\t{c.lam}\t{c.forallE}\t{c.letE}\t{c.proj}\t{c.mdata}\t{c.bvar}\t{c.fvar}\t{c.mvar}\t{c.const}\t{c.sort}\t{c.lit}"
  IO.println s!"=== AST-SHAPE-END ==="

end E213.AstShape

#eval E213.AstShape.runScan
