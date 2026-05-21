open Lean Meta

namespace E213.AstFoldScan

def foldTag : Name → Option String
  | `List.foldl     => some "List.foldl"
  | `List.foldr     => some "List.foldr"
  | `List.foldlM    => some "List.foldlM"
  | `List.foldrM    => some "List.foldrM"
  | `List.rec       => some "List.rec"
  | `List.recOn     => some "List.recOn"
  | `Nat.rec        => some "Nat.rec"
  | `Nat.recAux     => some "Nat.recAux"
  | `Nat.recOn      => some "Nat.recOn"
  | `Nat.brecOn     => some "Nat.brecOn"
  | `Nat.fold       => some "Nat.fold"
  | `Nat.foldRev    => some "Nat.foldRev"
  | `Fin.foldl      => some "Fin.foldl"
  | `Fin.foldr      => some "Fin.foldr"
  | `Fin.foldlM     => some "Fin.foldlM"
  | `Fin.foldrM     => some "Fin.foldrM"
  | `Array.foldl    => some "Array.foldl"
  | `Array.foldr    => some "Array.foldr"
  | `Array.foldlM   => some "Array.foldlM"
  | `Array.foldrM   => some "Array.foldrM"
  | _               => none

partial def normSkel : Expr → Expr
  | .mdata _ e          => normSkel e
  | .app f a            => .app (normSkel f) (normSkel a)
  | .lam _ t b bi       => .lam `_ (normSkel t) (normSkel b) bi
  | .forallE _ t b bi   => .forallE `_ (normSkel t) (normSkel b) bi
  | .letE _ t v b nd    => .letE `_ (normSkel t) (normSkel v) (normSkel b) nd
  | .proj s i e         => .proj s i (normSkel e)
  | .const n _          => .const n []
  | .fvar _             => .const `_F []
  | .mvar _             => .const `_M []
  | .sort _             => .sort .zero
  | e@(.bvar _)         => e
  | e@(.lit _)          => e

structure Site where
  decl    : Name
  uid     : Nat
  tag     : String
  argIdx  : Nat
  argSkel : String
  deriving Inhabited

partial def walk (decl : Name)
    (e : Expr)
    (sites : IO.Ref (Array Site))
    (counter : IO.Ref Nat) :
    IO Unit := do
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const n _ := f then
      if let some tag := foldTag n then
        let uid ← counter.get
        counter.set (uid + 1)
        for h : i in [:args.size] do
          let a := args[i]
          let skel := (normSkel a).dbgToString
          let safe := skel.replace "\t" "  " |>.replace "\n" " " |>.take 600
          sites.modify (·.push ⟨decl, uid, tag, i, safe⟩)
        -- Recurse into args only; skip spine (avoid duplicate emissions).
        for a in args do walk decl a sites counter
        return
    -- Generic application: walk spine head and all args.
    walk decl f sites counter
    for a in args do walk decl a sites counter
  | .lam _ t b _      => walk decl t sites counter; walk decl b sites counter
  | .forallE _ t b _  => walk decl t sites counter; walk decl b sites counter
  | .letE _ t v b _   => walk decl t sites counter
                         walk decl v sites counter
                         walk decl b sites counter
  | .proj _ _ inner   => walk decl inner sites counter
  | .mdata _ inner    => walk decl inner sites counter
  | _                 => pure ()

def isE213 (n : Name) : Bool := n.getRoot == `E213

def runScan : MetaM Unit := do
  let env ← getEnv
  let sites ← IO.mkRef (#[] : Array Site)
  let counter ← IO.mkRef 0
  let mut nDecls : Nat := 0
  for (name, info) in env.constants.toList do
    unless isE213 name do continue
    let some val := info.value? | continue
    nDecls := nDecls + 1
    walk name val sites counter
  let arr ← sites.get
  let nSites ← counter.get
  IO.println s!"=== AST-FOLD-SCAN-BEGIN ==="
  IO.println s!"# scanned-decls\t{nDecls}"
  IO.println s!"# sites\t{nSites}"
  IO.println s!"# rows\t{arr.size}"
  for s in arr do
    IO.println s!"R\t{s.decl}\t{s.uid}\t{s.tag}\t{s.argIdx}\t{s.argSkel}"
  IO.println s!"=== AST-FOLD-SCAN-END ==="

end E213.AstFoldScan

#eval E213.AstFoldScan.runScan
