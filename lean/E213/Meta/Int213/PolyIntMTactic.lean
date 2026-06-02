import E213.Meta.Int213.PolyIntM
import Lean

/-!
# `ring_intZ` — auto-reifying tactic front-end for `PolyIntM.poly_idMZ`

The `ℤ` analog of `Meta.Nat.PolyNatMTactic.ring_nat`: reads a goal `lhs = rhs` (`lhs rhs :
ℤ`), reifies both sides (numerals → `PE.C`, `+`/`*` → `PE.add`/`PE.mul`, `-` → `add ∘ neg`,
`Neg` → `PE.neg`, else indexed `PE.var`), and discharges with `poly_idMZ … rfl …`.  The
∅-axiom `ring` for `ℤ` — and unlike the `ℕ` version it handles **signed cancellation**
(`(a−b)·(a+b) = a²−b²`) via the zero-drop normal form.

```lean
example (a b : Int) : (a - b) * (a + b) = a*a - b*b := by ring_intZ
example (a b : Int) : a - b + b = a := by ring_intZ
```

All zero-axiom (the produced proof is a `poly_idMZ` application).
-/

namespace E213.Meta.Int213.PolyIntM

open Lean Meta Elab Tactic

/-- Reify an `Int` expression into a `PolyIntM.PE` value, threading discovered atoms. -/
partial def reifyPEZ (atoms : Array Expr) (e : Expr) : MetaM (Expr × Array Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      let (pa, atoms) ← reifyPEZ atoms a
      let (pb, atoms) ← reifyPEZ atoms b
      return (mkApp2 (mkConst ``PE.add) pa pb, atoms)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      let (pa, atoms) ← reifyPEZ atoms a
      let (pb, atoms) ← reifyPEZ atoms b
      return (mkApp2 (mkConst ``PE.mul) pa pb, atoms)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      let (pa, atoms) ← reifyPEZ atoms a
      let (pb, atoms) ← reifyPEZ atoms b
      return (mkApp2 (mkConst ``PE.add) pa (mkApp (mkConst ``PE.neg) pb), atoms)
  | (``Neg.neg, #[_, _, a]) =>
      let (pa, atoms) ← reifyPEZ atoms a
      return (mkApp (mkConst ``PE.neg) pa, atoms)
  | (``OfNat.ofNat, _) =>
      return (mkApp (mkConst ``PE.C) e, atoms)
  | _ =>
      match atoms.findIdx? (fun a => a == e) with
      | some i => return (mkApp (mkConst ``PE.var) (mkNatLit i), atoms)
      | none   => return (mkApp (mkConst ``PE.var) (mkNatLit atoms.size), atoms.push e)

/-- ★★★ **`ring_intZ`** — discharge an `Int` polynomial identity by auto-reified
    `poly_idMZ`. -/
elab "ring_intZ" : tactic => do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  let some (α, lhs, rhs) := ty.eq? |
    throwError "ring_intZ: goal is not an equality"
  unless (← isDefEq α (mkConst ``Int)) do
    throwError "ring_intZ: goal is not an equality of `Int`"
  let (peL, atoms) ← reifyPEZ #[] lhs
  let (peR, atoms) ← reifyPEZ atoms rhs
  let env ← mkListLit (mkConst ``Int) atoms.toList
  let normL := mkApp (mkConst ``PE.norm) peL
  let refl ← mkEqRefl normL
  let pf ← mkAppM ``poly_idMZ #[peL, peR, refl, env]
  goal.assign pf

end E213.Meta.Int213.PolyIntM

namespace E213.Meta.Int213.PolyIntM.Test
example (a b c : Int) : (a + b) * c = a * c + b * c := by ring_intZ
example (a b : Int) : (a - b) * (a + b) = a * a - b * b := by ring_intZ
example (a b : Int) : a - b + b = a := by ring_intZ
example (a b : Int) : (a + b) * (a + b) = a*a + 2*(a*b) + b*b := by ring_intZ
example (x y z : Int) : x * (y - z) = x*y - x*z := by ring_intZ
end E213.Meta.Int213.PolyIntM.Test
