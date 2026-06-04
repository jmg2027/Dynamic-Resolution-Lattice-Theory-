/-!
# Graph connectivity → δ⁰-closed cochains are constant

A minimal, reusable graph-connectedness induction over an abstract
adjacency `Adj : V → V → Prop`.  The single load-bearing fact:

  if a `Bool` colouring is constant across every edge
  (`IsClosed`) and every vertex is reachable from a root
  (`IsConnectedFrom`), then the colouring is globally constant.

This is the "graph-connectedness induction infrastructure" that the
parametric bipartite cohomology needs to lift the δ⁰-kernel = constants
fact off the complete-bipartite special case onto any connected graph:
`ker δ⁰` is the set of edge-constant colourings, and connectivity
collapses it to the two global constants (`b₀ = 1`).

Reachability is an **inductive predicate**, so the propagation argument
is plain structural induction — no well-founded recursion, no `propext`,
no `funext` (all statements are pointwise).

Companion: `theory/math/combinatorics/graph_connectivity.md`.
-/

namespace E213.Lib.Math.Combinatorics.GraphConnectivity

variable {V : Type}

/-! ## Reachability -/

/-- `Reach Adj root v` — `v` is reachable from `root` along `Adj`-edges.
    `base`: the root reaches itself.  `step`: extend a reached vertex
    across one edge. -/
inductive Reach (Adj : V → V → Prop) (root : V) : V → Prop
  | base : Reach Adj root root
  | step {u v : V} : Reach Adj root u → Adj u v → Reach Adj root v

/-- Every vertex is reachable from `root`. -/
def IsConnectedFrom (Adj : V → V → Prop) (root : V) : Prop :=
  ∀ v, Reach Adj root v

/-- A `Bool` colouring is δ⁰-closed: constant across every edge. -/
def IsClosed (Adj : V → V → Prop) (σ : V → Bool) : Prop :=
  ∀ u v, Adj u v → σ u = σ v

/-! ## Propagation -/

/-- **Constancy propagation.**  A δ⁰-closed colouring takes the root's
    value at every reachable vertex.  Structural induction on the
    reachability witness. -/
theorem closed_eq_root {Adj : V → V → Prop} {root : V} {σ : V → Bool}
    (hcl : IsClosed Adj σ) {v : V} (h : Reach Adj root v) :
    σ v = σ root := by
  induction h with
  | base => rfl
  | step _ huv ih =>
      -- σ v = σ u (edge) and σ u = σ root (ih)
      exact (hcl _ _ huv).symm.trans ih

/-- **Connectivity ⟹ global constancy.**  On a graph connected from a
    root, every δ⁰-closed colouring is globally constant. -/
theorem closed_const {Adj : V → V → Prop} {root : V} {σ : V → Bool}
    (hconn : IsConnectedFrom Adj root) (hcl : IsClosed Adj σ) :
    ∀ u v, σ u = σ v := fun u v =>
  (closed_eq_root hcl (hconn u)).trans (closed_eq_root hcl (hconn v)).symm

/-- **Kernel = the two constants (b₀ = 1).**  On a connected graph every
    δ⁰-closed colouring is pointwise the all-`false` or the all-`true`
    constant. -/
theorem closed_false_or_true {Adj : V → V → Prop} {root : V} {σ : V → Bool}
    (hconn : IsConnectedFrom Adj root) (hcl : IsClosed Adj σ) :
    (∀ x, σ x = false) ∨ (∀ x, σ x = true) := by
  cases hr : σ root with
  | false => exact Or.inl fun x => (closed_eq_root hcl (hconn x)).trans hr
  | true  => exact Or.inr fun x => (closed_eq_root hcl (hconn x)).trans hr

/-- **One Bool of freedom (dim ker = 1).**  Two δ⁰-closed colourings that
    agree at the root agree everywhere — the root colour is the single
    free parameter. -/
theorem closed_root_determines {Adj : V → V → Prop} {root : V}
    {σ τ : V → Bool} (hconn : IsConnectedFrom Adj root)
    (hσ : IsClosed Adj σ) (hτ : IsClosed Adj τ)
    (hroot : σ root = τ root) : ∀ x, σ x = τ x := fun x =>
  (closed_eq_root hσ (hconn x)).trans (hroot.trans (closed_eq_root hτ (hconn x)).symm)

/-! ## Two-step reachability helper (for bipartite-style graphs) -/

/-- A vertex reached by a single edge from the root. -/
theorem reach_one {Adj : V → V → Prop} {root v : V} (h : Adj root v) :
    Reach Adj root v :=
  Reach.step Reach.base h

/-- A vertex reached by two edges `root → m → v`. -/
theorem reach_two {Adj : V → V → Prop} {root m v : V}
    (h1 : Adj root m) (h2 : Adj m v) : Reach Adj root v :=
  Reach.step (reach_one h1) h2

end E213.Lib.Math.Combinatorics.GraphConnectivity
