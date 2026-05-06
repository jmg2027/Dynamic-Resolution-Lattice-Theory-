/-!
# T² × T² minimal CW — 213-native form

The 4-fold (real dim 4 = complex dim 2) `T² × T²` has minimal CW
decomposition by Künneth product of two T²-minimal complexes
(1 vertex + 2 edges + 1 face each).  Cell counts:

  | dim | count | basis (in product notation) |
  |-----|-------|----------------------------|
  | 0   | 1     | v⊗v                        |
  | 1   | 4     | a⊗v, b⊗v, v⊗a, v⊗b         |
  | 2   | 6     | f⊗v, a⊗a, a⊗b, b⊗a, b⊗b, v⊗f |
  | 3   | 4     | f⊗a, f⊗b, a⊗f, b⊗f         |
  | 4   | 1     | f⊗f                        |

Total = 1 + 4 + 6 + 4 + 1 = 16 cells.  All boundaries vanish
(inherited from each T² factor's zero boundary), so
`H^k(T²×T²; ℤ) = C^k`.

Hodge numbers (over ℂ, with T² = elliptic curve as complex
1-fold): h^{0,0}=1, h^{1,0}=h^{0,1}=2, h^{2,0}=h^{0,2}=1,
h^{1,1}=4, h^{2,1}=h^{1,2}=2, h^{2,2}=1.  Total Betti
numbers (1, 4, 6, 4, 1) — matching our CW count.

This file ships the cell enumeration + Int-coefficient cochains.
The cup product structure + Hard Lefschetz operator live in
`Surfaces/T2Squared/HardLefschetz.lean`.

STRICT ∅-AXIOM (all by `decide` / `rfl` on finite enumerations).
-/

namespace E213.Lib.Math.Cohomology.Surfaces.T2Squared

/-- 0-cells: single vertex `vv := v⊗v`. -/
inductive Cell0 : Type
  | vv : Cell0
  deriving DecidableEq, Repr

/-- 1-cells: four edges, two from each factor. -/
inductive Cell1 : Type
  | a1 : Cell1   -- a⊗v
  | b1 : Cell1   -- b⊗v
  | a2 : Cell1   -- v⊗a
  | b2 : Cell1   -- v⊗b
  deriving DecidableEq, Repr

/-- 2-cells: six 2-faces (Künneth: 1 + 4 + 1). -/
inductive Cell2 : Type
  | a1b1 : Cell2   -- f⊗v   (T² face × point)
  | a1a2 : Cell2   -- a⊗a
  | a1b2 : Cell2   -- a⊗b
  | b1a2 : Cell2   -- b⊗a
  | b1b2 : Cell2   -- b⊗b
  | a2b2 : Cell2   -- v⊗f   (point × T² face)
  deriving DecidableEq, Repr

/-- 3-cells: four 3-faces. -/
inductive Cell3 : Type
  | a1b1a2 : Cell3   -- f⊗a
  | a1b1b2 : Cell3   -- f⊗b
  | a1a2b2 : Cell3   -- a⊗f
  | b1a2b2 : Cell3   -- b⊗f
  deriving DecidableEq, Repr

/-- 4-cells: single top cell `vol := f⊗f`. -/
inductive Cell4 : Type
  | vol : Cell4
  deriving DecidableEq, Repr

/-- ℤ-cochains at each level. -/
abbrev C0 : Type := Cell0 → Int
abbrev C1 : Type := Cell1 → Int
abbrev C2 : Type := Cell2 → Int
abbrev C3 : Type := Cell3 → Int
abbrev C4 : Type := Cell4 → Int

end E213.Lib.Math.Cohomology.Surfaces.T2Squared
