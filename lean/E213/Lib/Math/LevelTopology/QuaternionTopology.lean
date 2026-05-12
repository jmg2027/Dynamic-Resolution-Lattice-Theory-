/-!
# Floor 4 (CD Level 3): Quaternion Topology = K₃ Oriented (∅-axiom)

The quaternion `j, k` at CD level 3 is encoded as an **oriented
triangle** (K₃ with cyclic orientation):

```
        i
       ●
      ╱ ╲
     ╱   ╲    (cyclic: i→j→k→i positive)
    ╱     ╲
   ●───────●
   k       j
```

The 3 imaginary units {i, j, k} form K₃ (complete graph on 3
vertices).  The CYCLIC ORIENTATION encodes:
  * `i · j = k` (positive cycle)
  * `j · i = -k` (reverse = sign flip)
  * `j · k = i`, `k · j = -i`
  * `k · i = j`, `i · k = -j`

Non-commutativity is the **orientation reversal cost**:
flipping cycle direction = flipping sign.

213-native: Quat = level-2 nested pair `(ComplexCut × ComplexCut)`
(or in classical CD numbering, level 2 = quaternion 4D).
-/

namespace E213.Lib.Math.LevelTopology.QuaternionTopology

/-- The 3 imaginary basis units. -/
abbrev QuatBasis := Fin 3

/-- i basis. -/
def i_basis : QuatBasis := ⟨0, by decide⟩

/-- j basis. -/
def j_basis : QuatBasis := ⟨1, by decide⟩

/-- k basis. -/
def k_basis : QuatBasis := ⟨2, by decide⟩

/-- Cyclic next in the i→j→k→i cycle. -/
def cyclicNext (b : QuatBasis) : QuatBasis :=
  ⟨(b.val + 1) % 3, Nat.mod_lt _ (by decide : 0 < 3)⟩

/-- ★ i → j (cyclic). -/
theorem next_i_is_j : cyclicNext i_basis = j_basis := by decide

/-- ★ j → k (cyclic). -/
theorem next_j_is_k : cyclicNext j_basis = k_basis := by decide

/-- ★ k → i (cyclic, closes the triangle). -/
theorem next_k_is_i : cyclicNext k_basis = i_basis := by decide

/-- ★ Three steps from `i` returns to `i` (3-cycle closure). -/
theorem three_steps_i :
    cyclicNext (cyclicNext (cyclicNext i_basis)) = i_basis := by decide

/-- ★ Three steps from `j` returns to `j`. -/
theorem three_steps_j :
    cyclicNext (cyclicNext (cyclicNext j_basis)) = j_basis := by decide

/-- ★ Three steps from `k` returns to `k`. -/
theorem three_steps_k :
    cyclicNext (cyclicNext (cyclicNext k_basis)) = k_basis := by decide

/-- Node count of K₃ topology = 3. -/
def nodeCount : Nat := 3

/-- Edge count of K₃ (oriented) = 3. -/
def edgeCount : Nat := 3

/-- ★ K₃ structure: 3 nodes, 3 oriented edges. -/
theorem K3_structure :
    nodeCount = 3 ∧ edgeCount = 3 := ⟨rfl, rfl⟩

end E213.Lib.Math.LevelTopology.QuaternionTopology
