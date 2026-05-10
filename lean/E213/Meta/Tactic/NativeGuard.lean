import Lean

namespace E213.Meta.Tactic.NativeGuard

open Lean Elab Command

/-!
# `213-native` guard — non-E213 dependencies are sorry-class

Per Mingu directive: enforce that 213-native declarations reference
ONLY the E213.* namespace + a small whitelist of Lean Init kernel
primitives.  Anything else (Mathlib, Std4, Classical.*, HEq, etc.)
fails elaboration — direct kernel-level analogue of the ∅-pure
guard, but at the *vocabulary* level rather than the *axiom* level.

Two axes of strictness:
  · `PureGuard.lean`    — no axiom dependencies (∅-axiom)
  · `NativeGuard.lean`  — no non-213 vocabulary dependencies

A truly "213-pure" theorem passes BOTH guards.
-/

/-- Default allow-list of Lean kernel primitive *prefixes*. -/
def defaultAllowList : Array String := #[
  "E213",
  "Nat", "Bool", "Prop", "Type", "Sort", "String", "Char",
  "True", "False", "And", "Or", "Not", "Eq", "Iff", "Exists",
  "Prod", "PProd", "Subtype", "Sum", "Option",
  "Decidable", "decide",
  "OfNat", "Mul", "Add", "Sub", "Div", "Mod", "Pow", "Neg",
  "HMul", "HAdd", "HSub", "HDiv", "HMod", "HPow",
  "LE", "LT", "BEq", "DecidableEq", "Min", "Max", "Ne",
  "id", "Function",
  "Inhabited", "Nonempty",
  "rfl", "WellFoundedRecursion",
  "Repr", "ToString", "Coe",
  "Unit", "PUnit",
  -- Init utilities for equality / let elaboration
  "congrArg", "congrFun", "letFun", "cond"
]

/-- Raw substring prefixes (no dot semantics).  Used for Lean's
    auto-generated names like `instOfNatNat`, `_auxLemma_3`, etc.
    These don't follow namespace conventions. -/
def rawPrefixes : Array String := #[
  "inst",          -- typeclass instances elaborator-generated
  "_aux",          -- auxiliary lemmas
  "_private",      -- private helpers
  "_eqn"           -- equation lemmas
]

/-- Check if a constant name is 213-native.  Matches either by
    namespace-prefix (dot semantics) against `allow` or by raw
    substring prefix against `rawPrefixes`. -/
def isNative (allow : Array String) (n : Name) : Bool :=
  let s := n.toString
  allow.any (fun p => s == p || s.startsWith (p ++ ".")) ||
  rawPrefixes.any (fun p => s.startsWith p)

/-- Collect all constants referenced in an expression. -/
partial def collectUsedConsts : Expr → NameSet → NameSet
  | .const n _,        s => s.insert n
  | .app f a,          s => collectUsedConsts a (collectUsedConsts f s)
  | .lam _ t b _,      s => collectUsedConsts b (collectUsedConsts t s)
  | .forallE _ t b _,  s => collectUsedConsts b (collectUsedConsts t s)
  | .letE _ t v b _,   s => collectUsedConsts b
                              (collectUsedConsts v (collectUsedConsts t s))
  | .mdata _ e,        s => collectUsedConsts e s
  | .proj _ _ e,       s => collectUsedConsts e s
  | _,                 s => s

/-- Direct (one-level) constants used by a declaration's type + value. -/
def directConsts (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | none => {}
  | some info =>
    let s := collectUsedConsts info.type {}
    match info.value? with
    | some v => collectUsedConsts v s
    | none   => s

/-- `#guard_native <name>` — fail elaboration if any directly-used
    constant in `<name>`'s type or value is non-213-native.

    Uses `defaultAllowList`. -/
elab "#guard_native " name:ident : command => do
  let constName := name.getId
  let env ← getEnv
  unless env.contains constName do
    throwError "guard_native: unknown declaration '{constName}'"
  let used := directConsts env constName
  let bad := used.toList.filter (fun n => !isNative defaultAllowList n)
  if bad.isEmpty then
    logInfo m!"✓ '{constName}' is 213-native"
  else
    throwError "guard_native: '{constName}' references non-native: {bad}"

/-- `#guard_native_with <name> allowing [p1, p2, ...]` — like
    `#guard_native` but extends the default allow-list with
    additional namespace prefixes (string literals).  Useful for
    sealed cases that legitimately reference one specific external
    namespace. -/
elab "#guard_native_with " name:ident " allowing " "[" ws:str,* "]"
    : command => do
  let constName := name.getId
  let env ← getEnv
  unless env.contains constName do
    throwError "guard_native_with: unknown declaration '{constName}'"
  let extra := ws.getElems.map (·.getString) |>.toList
  let allowAll := defaultAllowList.append extra.toArray
  let used := directConsts env constName
  let bad := used.toList.filter (fun n => !isNative allowAll n)
  if bad.isEmpty then
    logInfo m!"✓ '{constName}' is 213-native (with extras {extra})"
  else
    throwError "guard_native_with: '{constName}' references non-native: {bad}"

/-- `@[native213]` attribute: declaration-time 213-native enforcement.
    Equivalent to `#guard_native` attached to the def. -/
initialize Lean.registerBuiltinAttribute {
  name := `native213
  descr := "Assert 213-native: declaration must reference only E213.* + Lean Init"
  applicationTime := AttributeApplicationTime.afterCompilation
  add := fun decl _ _ => do
    let env ← getEnv
    let used := directConsts env decl
    let bad := used.toList.filter (fun n => !isNative defaultAllowList n)
    if bad.isEmpty then
      pure ()
    else
      throwError "@[native213]: '{decl}' references non-native: {bad}"
}

end E213.Meta.Tactic.NativeGuard
