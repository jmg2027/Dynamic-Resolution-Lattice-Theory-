/-!
# Level 2: Complex Topology = Z/4 Cycle (∅-axiom)

The imaginary `i` at CD level 2 is encoded as a **4-cycle**
(Z/4 cyclic group):

```
    1 ●────────● i
      │        │
      │        │ (90° rotation)
      │        │
    -1 ●────────● -i
      └────────┘
```

The vertices are the powers of `i`:
  * `i⁰ = 1`
  * `i¹ = i`
  * `i² = -1`
  * `i³ = -i`
  * `i⁴ = 1` (back to start)

This 4-cycle directly encodes the `i² = -1` rule:
walking 2 steps around the cycle = sign flip.

213-native: at CD level 2, `(0, 1)·(0, 1) = (-1, 0)` corresponds
to "two cycle steps from `i`" landing at `-1`.
-/

namespace E213.Lib.Math.LevelTopology.ComplexTopology

/-- Complex topology nodes: the 4 powers of `i`. -/
abbrev CycleNode := Fin 4

/-- The four powers: 1, i, -1, -i. -/
def one_node : CycleNode := ⟨0, by decide⟩
def i_node : CycleNode := ⟨1, by decide⟩
def neg_one_node : CycleNode := ⟨2, by decide⟩
def neg_i_node : CycleNode := ⟨3, by decide⟩

/-- The 4-cycle next-step (90° rotation). -/
def cycleStep (n : CycleNode) : CycleNode :=
  ⟨(n.val + 1) % 4, by simp [Nat.mod_lt]⟩

/-- ★ Cycle step from 1: → i. -/
theorem step_one : cycleStep one_node = i_node := by decide

/-- ★ Cycle step from i: → -1 (= i²). -/
theorem step_i : cycleStep i_node = neg_one_node := by decide

/-- ★ Cycle step from -1: → -i. -/
theorem step_neg_one : cycleStep neg_one_node = neg_i_node := by decide

/-- ★ Cycle step from -i: → 1 (closes cycle). -/
theorem step_neg_i : cycleStep neg_i_node = one_node := by decide

/-- ★ Two cycle steps from `1` reach `-1` (= `i² = -1`).
    Multiplying by `i` twice = step twice. -/
theorem two_steps_from_one :
    cycleStep (cycleStep one_node) = neg_one_node := by decide

/-- ★ Four cycle steps return to start (i⁴ = 1). -/
theorem four_steps_id :
    cycleStep (cycleStep (cycleStep (cycleStep one_node))) = one_node := by
  decide

/-- Node count of Z/4 topology. -/
def nodeCount : Nat := 4

/-- Edge count of Z/4 topology. -/
def edgeCount : Nat := 4

/-- ★ Z/4 cycle has 4 nodes, 4 edges. -/
theorem cycle_structure :
    nodeCount = 4 ∧ edgeCount = 4 := ⟨rfl, rfl⟩

end E213.Lib.Math.LevelTopology.ComplexTopology
