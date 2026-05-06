/-!
# Cascade-Delete Calculus (minimal model, seed)

213-internal formalization of the *cascade-delete pattern* used in
the propext-extermination work of branch
`claude/fix-propext-constraints-Rdn1r`.

## Idea

A codebase is a directed graph (nodes = files/theorems, edges =
"uses").  Each node carries a status: PURE, DIRTY, or SEALED.

A *cascade-delete step* removes a DIRTY node whose consumer set
is empty, OR turns a node DIRTY when one of its dependencies is.

This file is the minimal seed.  All defs stay 213-pure (no `List`,
no `simp [iff]`, only Bool + Nat structural recursion).
-/

namespace E213.Lib.Math.CascadeCalculus.Core

/-- Three labels a node can carry. -/
inductive Status where
  | pure
  | dirty
  | sealed
  deriving DecidableEq, Repr

/-- Equality test on Status (Bool, decidable). -/
def Status.eqb : Status → Status → Bool
  | .pure,   .pure   => true
  | .dirty,  .dirty  => true
  | .sealed, .sealed => true
  | _, _ => false

/-- Dependency graph as characteristic function: `g n d = true`
    means "node n directly depends on node d".  Avoids `List`. -/
abbrev DepGraph := Nat → Nat → Bool

/-- Label assignment over nodes. -/
abbrev Labeling := Nat → Status

/-- "No DIRTY consumer ≤ N depends on n" — direct Nat recursion.
    PURE consumers are inert (they don't propagate DIRTY). -/
def hasNoDirtyConsumerUpTo (g : DepGraph) (l : Labeling) :
    Nat → Nat → Bool
  | 0,     n => !(g 0 n && Status.eqb (l 0) .dirty)
  | N + 1, n => !(g (N+1) n && Status.eqb (l (N+1)) .dirty)
                && hasNoDirtyConsumerUpTo g l N n

/-- A DIRTY node `n` is deletable at bound N iff no DIRTY consumer
    in [0, N] depends on it. -/
def isDeletable (g : DepGraph) (l : Labeling) (N n : Nat) : Bool :=
  match l n with
  | .dirty => hasNoDirtyConsumerUpTo g l N n
  | _      => false

/-- "Some dependency of n is DIRTY", Bool-recursive over [0, N]. -/
def hasDirtyDepUpTo (g : DepGraph) (l : Labeling) :
    Nat → Nat → Bool
  | 0,     n => g n 0     && Status.eqb (l 0)     .dirty
  | N + 1, n => (g n (N+1) && Status.eqb (l (N+1)) .dirty)
                || hasDirtyDepUpTo g l N n

/-- One step of the cascade-delete process at bound `N`.
    Carries Bool-valued witnesses so the step is decidable
    and ∅-axiom — no `Iff`, no `Exists`, no `propext`.

    Three operations form the full work cycle:
      `delete`    — DIRTY node with no DIRTY consumer → PURE
      `propagate` — PURE node gains DIRTY dependency → DIRTY
      `seal`      — DIRTY node marked structural-by-design → SEALED

    A fourth operation (`migrate`) — adding new PURE parallel nodes
    + redirecting consumers — requires graph mutation; deferred. -/
inductive Step (N : Nat) :
    DepGraph × Labeling → DepGraph × Labeling → Prop where
  /-- Drop a deletable DIRTY node (relabel it `pure`). -/
  | delete (g : DepGraph) (l : Labeling) (n : Nat)
      (h : isDeletable g l N n = true) :
      Step N (g, l)
        (g, fun m => if m = n then .pure else l m)
  /-- Cascade up: a PURE node with at least one DIRTY dependency
      becomes DIRTY. -/
  | propagate (g : DepGraph) (l : Labeling) (n : Nat)
      (h_pure : Status.eqb (l n) .pure = true)
      (h_dep : hasDirtyDepUpTo g l N n = true) :
      Step N (g, l)
        (g, fun m => if m = n then .dirty else l m)
  /-- Seal: mark a DIRTY node as SEALED (mathematically inherent).
      No mechanical hypothesis — the seal-justification is metalogical
      and lives in `tools/scan_all_axioms.py SEALED_DIRTY_PREFIXES`.
      Sealing is a *modal commitment*: "this DIRTY is by design". -/
  | seal (g : DepGraph) (l : Labeling) (n : Nat)
      (h_dirty : Status.eqb (l n) .dirty = true) :
      Step N (g, l)
        (g, fun m => if m = n then .sealed else l m)

end E213.Lib.Math.CascadeCalculus.Core
