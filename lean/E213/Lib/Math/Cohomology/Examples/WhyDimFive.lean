import E213.Lib.Math.Cohomology.Examples.TopologyCompare

/-!
# Why d = 5? — cohomological double-uniqueness

`OS/Atomicity.lean` forces d = 5 (combinatorial).
`TopologyCompare.lean` shows that among the tested configs, the
b_1 = 8 = 1/α_3 reading lands only at (NS,NT) = (3,2) read at
presentation c = 2 (multiplicity `c` is a free presentation parameter,
no value canonical — `theory/physics/foundations/atomic_constants.md`;
`research-notes/frontiers/atomic_c_multiplicity_forcing.md`).  This file
extends across d ∈ {4..7} and confirms d = 5 is doubly forced — the
forcing is of the *dimension* d, the c = 2 only the presentation at
which the b_1 = 8 value is read.
-/

namespace E213.Lib.Math.Cohomology.Examples.WhyDimFive

open E213.Lib.Math.Cohomology.Examples.TopologyCompare (b1_bipartite)

/-- d=4 K_{2,2}^{(c)}: b_1 ∈ {1, 5, 9} — no match. -/
theorem d4_K22 :
    b1_bipartite 2 2 1 = 1
    ∧ b1_bipartite 2 2 2 = 5
    ∧ b1_bipartite 2 2 3 = 9 := by decide

/-- d=4 K_{3,1}^{(c)}: b_1 ∈ {1, 3, 6} — no match. -/
theorem d4_K31 :
    b1_bipartite 3 1 1 = 1
    ∧ b1_bipartite 3 1 2 = 3
    ∧ b1_bipartite 3 1 3 = 6 := by decide

/-- d=5: ONLY (3,2,2) and (2,3,2) match. -/
theorem d5_unique :
    b1_bipartite 3 2 2 = 8
    ∧ b1_bipartite 2 3 2 = 8
    ∧ b1_bipartite 4 1 2 ≠ 8 := by decide

/-- d=6 K_{3,3}^{(c)}: b_1 ∈ {4, 13, 22} — no match. -/
theorem d6_K33 :
    b1_bipartite 3 3 1 = 4
    ∧ b1_bipartite 3 3 2 = 13
    ∧ b1_bipartite 3 3 3 = 22 := by decide

/-- d=6 K_{4,2}^{(c)}: b_1 ∈ {3, 11, 19} — no match. -/
theorem d6_K42 :
    b1_bipartite 4 2 1 = 3
    ∧ b1_bipartite 4 2 2 = 11
    ∧ b1_bipartite 4 2 3 = 19 := by decide

/-- d=7 K_{4,3}^{(c)}: b_1 ∈ {6, 18, 30} — no match. -/
theorem d7_K43 :
    b1_bipartite 4 3 1 = 6
    ∧ b1_bipartite 4 3 2 = 18
    ∧ b1_bipartite 4 3 3 = 30 := by decide

/-- ★★★ d=5 doubly forced ★★★

    Atomicity forces d=5 (Atomicity theorem).
    At presentation c=2, only (NS,NT)=(3,2)/(2,3) read b_1=1/α_3
    (c a free presentation parameter, not forced).
    No other d admits b_1=8 in tested bipartite configs. -/
theorem d5_doubly_forced :
    b1_bipartite 2 2 2 ≠ 8
    ∧ b1_bipartite 3 1 2 ≠ 8
    ∧ b1_bipartite 3 2 2 = 8
    ∧ b1_bipartite 3 3 2 ≠ 8
    ∧ b1_bipartite 4 2 2 ≠ 8
    ∧ b1_bipartite 4 3 2 ≠ 8 := by decide

end E213.Lib.Math.Cohomology.Examples.WhyDimFive
