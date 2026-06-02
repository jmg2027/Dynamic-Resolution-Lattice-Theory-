import E213.Meta.Nat.PolyNatM
import Lean

/-!
# `ring_nat` — an auto-reifying tactic front-end for `PolyNatM.poly_idM`

`Meta/Nat/PolyNatM` proves multivariate `Nat` polynomial identities by reflection, but the
user must hand-write the `PE` syntax trees and the variable environment.  This file adds the
elaboration tactic **`ring_nat`** that reads a goal `lhs = rhs` (`lhs rhs : Nat`), reifies both
sides automatically (numerals → `PE.C`, `+`/`*` → `PE.add`/`PE.mul`, every other sub-term an
indexed `PE.var`), and discharges it with `poly_idM … rfl …`.  It is the ∅-axiom `ring` for
`Nat` (Lean-core `ring`/`ac_rfl` pull `propext`/`Quot.sound`).

```lean
example (x y z : Nat) : (x + y) * z = z * x + y * z := by ring_nat
example (a b : Nat)   : (a + b) * (a + b) = a*a + 2*(a*b) + b*b := by ring_nat
```

Closes the goal iff it is a true polynomial identity over `Nat` (no subtraction); otherwise it
fails (the normal forms differ, `rfl` does not fire).  All zero-axiom — the produced proof is a
`poly_idM` application, which is PURE.
-/

namespace E213.Meta.Nat.PolyNatM

open Lean Meta Elab Tactic

/-- Reify a `Nat` expression into a `PolyNatM.PE` value (as an `Expr`), threading the array of
    discovered atom sub-terms (each becomes `PE.var <index>`). -/
partial def reifyPE (atoms : Array Expr) (e : Expr) : MetaM (Expr × Array Expr) := do
  -- numeral leaf → PE.C
  match (← getNatValue? e) with
  | some n =>
      return (mkApp (mkConst ``PE.C) (mkNatLit n), atoms)
  | none =>
    match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
        let (pa, atoms) ← reifyPE atoms a
        let (pb, atoms) ← reifyPE atoms b
        return (mkApp2 (mkConst ``PE.add) pa pb, atoms)
    | (``HMul.hMul, #[_, _, _, _, a, b]) =>
        let (pa, atoms) ← reifyPE atoms a
        let (pb, atoms) ← reifyPE atoms b
        return (mkApp2 (mkConst ``PE.mul) pa pb, atoms)
    | _ =>
        -- atom → PE.var (reuse index if already seen, up to syntactic equality)
        match atoms.findIdx? (fun a => a == e) with
        | some i => return (mkApp (mkConst ``PE.var) (mkNatLit i), atoms)
        | none =>
            let i := atoms.size
            return (mkApp (mkConst ``PE.var) (mkNatLit i), atoms.push e)
where
  /-- Concrete `Nat` numeral value of `e` (handles `OfNat`/literals), else `none`. -/
  getNatValue? (e : Expr) : MetaM (Option Nat) := do
    match e.nat? with
    | some n => return some n
    | none   => return none

/-- ★★★ **`ring_nat`** — discharge a `Nat` polynomial identity goal by auto-reified
    `poly_idM`. -/
elab "ring_nat" : tactic => do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  let some (α, lhs, rhs) := ty.eq? |
    throwError "ring_nat: goal is not an equality"
  unless (← isDefEq α (mkConst ``Nat)) do
    throwError "ring_nat: goal is not an equality of `Nat`"
  let (peL, atoms) ← reifyPE #[] lhs
  let (peR, atoms) ← reifyPE atoms rhs
  let env ← mkListLit (mkConst ``Nat) atoms.toList
  -- h : peL.norm = peR.norm  (closed `List (List Nat × Nat)`, equal by rfl when the identity holds)
  let normL := mkApp (mkConst ``PE.norm) peL
  let refl ← mkEqRefl normL
  let pf ← mkAppM ``poly_idM #[peL, peR, refl, env]
  goal.assign pf

end E213.Meta.Nat.PolyNatM

namespace E213.Meta.Nat.PolyNatM.Test
/-- test: distributivity / commutativity -/
example (x y z : Nat) : (x + y) * z = z * x + y * z := by ring_nat
/-- test: square expansion with a numeral coefficient -/
example (a b : Nat) : (a + b) * (a + b) = a*a + 2*(a*b) + b*b := by ring_nat
/-- test: the cube_reorder identity (3 variables, the DepthCubicGeneric blocker) -/
example (T2 T3 n : Nat) :
    6*T3 + 6*T2 + n + 3*(2*T2 + n) + 3*n + 1 = 6*(T2 + T3) + 6*(n + T2) + (n+1) := by ring_nat
/-- test: a 4-variable degree-2 identity -/
example (a b c d : Nat) : (a + b) * (c + d) = a*c + a*d + b*c + b*d := by ring_nat
end E213.Meta.Nat.PolyNatM.Test
