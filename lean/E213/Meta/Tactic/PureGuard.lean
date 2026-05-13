import Lean

namespace E213.Meta.Tactic.PureGuard

open Lean Elab Command

/-!
# `∅-pure` guard — sorry-class equivalence at compile time

Per Mingu directive: treat any theorem with non-empty axiom dependency
as functionally equivalent to `sorry`, and have Lean **enforce** this
at elaboration time rather than via post-hoc Python audit.

This file lives in `Meta/Tactic/` (NOT `Term/`) because it is a
meta-tool: it inspects axiom dependencies and is therefore allowed to
mention the `axiom`-related machinery from Lean core.  Kernel-tier
files remain literally axiom-free; `Meta/` may discuss them.

The kernel's `Lean.CollectAxioms.collect` walks the declaration's
proof term and returns the set of axiom dependencies.  When the set
is non-empty, we `throwError` to fail elaboration — this is the
direct kernel-level analogue of `sorry`'s warning behavior.
-/

/-- Internal: collect axiom dependencies of a declaration. -/
private def axiomsOf (env : Environment) (constName : Name) : List Name :=
  let (_, s) := ((Lean.CollectAxioms.collect constName).run env).run {}
  s.axioms.toList

/-- `#guard_pure <name>` succeeds iff `<name>` has zero kernel
    dependencies.  Throws an elaboration error otherwise.

    Use immediately after a theorem definition to enforce ∅-pure
    status.  Functionally equivalent to detecting a `sorry` and
    refusing to compile. -/
elab "#guard_pure " name:ident : command => do
  let constName := name.getId
  let env ← getEnv
  unless env.contains constName do
    throwError "guard_pure: unknown declaration '{constName}'"
  let deps := axiomsOf env constName
  if deps.isEmpty then
    logInfo m!"✓ '{constName}' is ∅-pure"
  else
    throwError "guard_pure: '{constName}' depends on: {deps}"

/-- `#guard_sealed <name> with [a1, a2, ...]` succeeds iff `<name>`'s
    kernel dependencies are a *subset* of the explicitly-listed
    "sealed" identifiers.  Use for legitimately-sealed theorems
    (e.g. funext-by-design Lens equality, Cantor's Iff) where the
    dependency set is documented and frozen.  Anything outside the
    list triggers an error — catches unintentional leaks. -/
elab "#guard_sealed " name:ident " with " "[" ws:ident,* "]" : command => do
  let constName := name.getId
  let env ← getEnv
  unless env.contains constName do
    throwError "guard_sealed: unknown declaration '{constName}'"
  let allowed := ws.getElems.map (·.getId) |>.toList
  let deps := axiomsOf env constName
  let unexpected := deps.filter (fun a => !allowed.contains a)
  if unexpected.isEmpty then
    logInfo m!"✓ '{constName}' sealed-OK (deps ⊆ {allowed})"
  else
    throwError
      "guard_sealed: '{constName}' uses unsealed: {unexpected}\n  (allowed: {allowed}; full deps: {deps})"

/-- `@[pure213]` attribute: declaration-time ∅-pure enforcement.
    Attaches directly to a `def`/`theorem`; if the declaration has
    any kernel dependency the attribute application throws. -/
initialize Lean.registerBuiltinAttribute {
  name := `pure213
  descr := "Assert ∅-pure: declaration must have zero kernel dependencies"
  applicationTime := AttributeApplicationTime.afterCompilation
  add := fun decl _ _ => do
    let env ← getEnv
    let deps := axiomsOf env decl
    if deps.isEmpty then
      pure ()
    else
      throwError "@[pure213]: '{decl}' depends on: {deps}"
}

end E213.Meta.Tactic.PureGuard
