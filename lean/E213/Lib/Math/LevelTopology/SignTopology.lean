/-!
# Level 1: Sign Topology = K₂ Bipartite (∅-axiom)

The sign property at CD level 1 is encoded in the simplest
possible topology: a **bipartite graph K₂** with two nodes
(Pos, Neg) and one edge between them.

This is the operation `+` (or rather the sign extension `±`)
made visible as a graph:

```
   Pos ●─────────● Neg
        (sign flip)
```

213-native: SignedCut = `(Cut, Cut)` pair maps directly to this
two-node graph, where:
  * Pos = first component active
  * Neg = second component active
  * sign flip = swap the two components (cdNeg in G37)

Atomic content:
  * `SignNode := Bool` (true = Pos, false = Neg)
  * `signFlip` swap function
  * Graph cardinality = 2, edge count = 1
-/

namespace E213.Lib.Math.LevelTopology.SignTopology

/-- Sign topology nodes: just two — Pos and Neg. -/
abbrev SignNode := Bool

/-- Pos node. -/
def Pos : SignNode := true

/-- Neg node. -/
def Neg : SignNode := false

/-- ★ Pos ≠ Neg. -/
theorem Pos_ne_Neg : Pos ≠ Neg := by decide

/-- Sign flip swap. -/
def signFlip (n : SignNode) : SignNode := !n

/-- ★ Sign flip is involutive: `flip ∘ flip = id`. -/
theorem signFlip_involutive (n : SignNode) :
    signFlip (signFlip n) = n := by cases n <;> rfl

/-- ★ flip Pos = Neg. -/
theorem flip_Pos : signFlip Pos = Neg := rfl

/-- ★ flip Neg = Pos. -/
theorem flip_Neg : signFlip Neg = Pos := rfl

/-- Node count of K₂ topology. -/
def nodeCount : Nat := 2

/-- Edge count of K₂ topology. -/
def edgeCount : Nat := 1

/-- ★ K₂ has 2 nodes, 1 edge. -/
theorem K2_structure :
    nodeCount = 2 ∧ edgeCount = 1 := ⟨rfl, rfl⟩

end E213.Lib.Math.LevelTopology.SignTopology
