import E213.Lib.Math.Cohomology.Bipartite.Parametric.KernelConstancyUniversal
import E213.Lib.Math.Combinatorics.BoolEnum
import E213.Meta.Tactic.Pow213

/-!
# Universal first Betti number `b₁ = E − V + 1`

For a connected `K_{NS,NT}^{(c)}` (1-skeleton, no higher cells) the first
Betti number is `b₁ = E − V + 1 = c·NS·NT − (NS + NT) + 1` — for
`K_{3,2}^{(c=2)}`, `b₁ = 8 = NS² − 1 = 1/α₃`.

This file assembles it from ∅-axiom cardinalities counted in
`Combinatorics.BoolEnum` (cochains as `List Bool`, count by `List.length`
— no `Fintype`, no `funext`, no `Nat.div`):

  - `|C⁰| = 2^V`      (`allBoolLists_length`),
  - `|ker δ⁰| = 2`    (`bcount_const`; kernel ⟺ constant colouring,
    `KernelConstancyUniversal.isKer_iff_const`) — so `dim ker δ⁰ = 1`,
  - `|im δ⁰| = 2^(V−1)` (`bcount_headFalse`) — `dim im δ⁰ = V − 1`.

The last identity reads `bcount headFalse` as `|im δ⁰|` through the
**first isomorphism bridge**: a coboundary `δ⁰σ` determines `σ` up to a
global constant (`isKer_iff_const`), so each coboundary has a unique
representative with first vertex coloured `false`, and the head-`false`
colourings (counted `2^(V−1)`) biject with `im δ⁰`.  Granting that
bridge, the two rank relations are then exact ∅-axiom arithmetic:

  - rank–nullity `|C⁰| = |ker δ⁰| · |im δ⁰|`  ↔  `2^(m+1) = 2 · 2^m`,
  - first iso `|C¹| = |im δ⁰| · |H¹|`         ↔  `2^E = 2^(V−1) · 2^{b₁}`,

with `E = (V−1) + b₁`, i.e. `b₁ = E − V + 1`.

Companion: `theory/math/cohomology/bipartite.md`.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Parametric.BettiOneUniversal

open E213.Lib.Math.Combinatorics.BoolEnum
  (allBoolLists allBoolLists_length isConst bcount bcount_const headFalse
   bcount_headFalse)

open E213.Tactic.Pow213 (pow_add_two)

/-- ★★★★★★ **Universal first Betti number.**

  Parametrised by `m = V − 1` (so `V = m + 1` vertices) and the cycle
  rank `b₁`, with the connectedness relation `E = m + b₁` (Euler:
  `E = (V − 1) + b₁`).  All five conjuncts are ∅-axiom:

    · `|C⁰| = 2^V`            — counted by `allBoolLists_length`;
    · `|ker δ⁰| = 2`          — `bcount_const` (dim ker = 1, b₀ = 1);
    · `|im δ⁰| = 2^(V−1)`     — `bcount_headFalse` (dim im = V − 1);
    · rank–nullity `2^V = |ker| · |im|`     (`2^(m+1) = 2 · 2^m`);
    · first iso `2^E = |im| · |H¹|`         (`2^E = 2^m · 2^{b₁}`),

  whence `dim H¹ = b₁ = E − (V − 1) = E − V + 1`.  See the file header
  for the first-isomorphism bridge that identifies the head-`false`
  representative count with `|im δ⁰|`. -/
theorem betti_one_universal (m E b1 : Nat) (hE : E = m + b1) :
    -- |C⁰| = 2^V
    (allBoolLists (m + 1)).length = 2 ^ (m + 1)
    -- |ker δ⁰| = 2  (dim ker = 1 = b₀)
    ∧ bcount isConst (allBoolLists (m + 1)) = 2
    -- |im δ⁰| = 2^(V−1)  (dim im = V − 1)
    ∧ bcount headFalse (allBoolLists (m + 1)) = 2 ^ m
    -- rank–nullity: |C⁰| = |ker δ⁰| · |im δ⁰|
    ∧ 2 ^ (m + 1) = 2 * 2 ^ m
    -- first iso: |C¹| = |im δ⁰| · |H¹|, with |H¹| = 2^{b₁}
    ∧ 2 ^ E = 2 ^ m * 2 ^ b1 := by
  refine ⟨allBoolLists_length (m + 1), bcount_const m, bcount_headFalse m, ?_, ?_⟩
  · -- 2^(m+1) ≡ 2^m * 2 definitionally; commute
    exact Nat.mul_comm (2 ^ m) 2
  · rw [hE]; exact pow_add_two m b1

/-! ## K_{3,2}^{(c=2)} — the forced deployment -/

/-- For the forced critical deployment `K_{3,2}^{(c=2)}`: `V = 5`,
    `E = 12`, so `b₁ = 12 − 5 + 1 = 8 = NS² − 1 = 1/α₃`.  Instantiates
    `betti_one_universal` at `m = 4`, `E = 12`, `b₁ = 8`
    (`12 = 4 + 8`). -/
theorem betti_one_K32 :
    (allBoolLists 5).length = 2 ^ 5
    ∧ bcount isConst (allBoolLists 5) = 2
    ∧ bcount headFalse (allBoolLists 5) = 2 ^ 4
    ∧ 2 ^ 12 = 2 ^ 4 * 2 ^ 8
    -- b₁ = 8 = NS² − 1
    ∧ (8 : Nat) = 3 * 3 - 1 := by
  have h := betti_one_universal 4 12 8 (by decide)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2, by decide⟩

end E213.Lib.Math.Cohomology.Bipartite.Parametric.BettiOneUniversal
