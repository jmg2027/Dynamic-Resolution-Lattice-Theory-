import E213.Theory.Raw.API
import E213.Lib.Math.UniverseChain.Recursion

/-!
# SelfSimilarityBridge — the "same shape under descent" has a qualitative and a
quantitative reading

"What keeps the same shape as you descend is the floor" has two framework
readings of one fact:

  * **Qualitative (Raw branching)** — `Raw.Lambek.self_similar_floor`: peeling a
    non-atom yields parts that each *again* have the atom-or-slash shape
    (`decompose` holds at every depth), while depth strictly drops, bottoming
    out at the atoms.  The *form* is invariant under refinement.

  * **Quantitative (universe chain)** — `numV L = 5^L`: each vertex carries a
    copy of the same `d = 5`-vertex shape, so the count multiplies across
    levels: `numV (m + n) = numV m · numV n` (`self_similar_count`).  The
    *count* is self-similar under level addition (the exponential law is exactly
    "each level replicates the whole").

These are not two facts: the qualitative self-similarity (same constructor shape
at every depth) and the quantitative self-similarity (count replicates per
level) are one "same shape under descent" read through the form-Lens and the
count-Lens.  `replicate_image_card : numV 2 = numV 1 · numV 1` is the base
instance; `self_similar_count` is the general law.
-/

namespace E213.Lib.Math.SelfSimilarityBridge

open E213.Theory (Raw)
open E213.Lib.Math.Cohomology.Fractal.Level (numV)
open E213.Lib.Math.UniverseChain.Recursion (numV_def)

/-- `a^(m+n) = a^m · a^n`, propext-free (core `Nat.pow_add` pulls propext;
    this structural recursion via `Nat.pow_succ` + `NatHelper.mul_assoc` does
    not). -/
private theorem pow_add_pure (a : Nat) :
    ∀ m n, a ^ (m + n) = a ^ m * a ^ n
  | _, 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | m, n + 1 => by
    rw [← Nat.add_assoc, Nat.pow_succ, Nat.pow_succ, pow_add_pure a m n]
    exact E213.Tactic.NatHelper.mul_assoc (a ^ m) (a ^ n) a

/-- **Quantitative self-similarity**: the level count replicates under level
    addition — `numV (m + n) = numV m · numV n`.  Each level carries a copy of
    the whole, so counts multiply (the `5^L` exponential law is the count-Lens
    reading of "same shape at every level"). -/
theorem self_similar_count (m n : Nat) : numV (m + n) = numV m * numV n := by
  rw [numV_def, numV_def, numV_def, pow_add_pure]

/-- The base instance recovered from the general law: `numV 2 = numV 1 · numV 1`
    (one level replicating into two). -/
theorem self_similar_base : numV 2 = numV 1 * numV 1 :=
  self_similar_count 1 1

/-- ★★ **Self-similarity bridge.**  "Same shape under descent" in both readings:

    - **form** (Raw): the atom-or-slash decompose-shape holds at *every* depth,
      depth strictly drops on the way down, and atoms are the floor (depth 0) —
      `Raw.Lambek.self_similar_floor`.
    - **count** (universe chain): the level count replicates,
      `numV (m + n) = numV m · numV n`.

    One self-similarity, two Lenses (form / count): the residue's shape is
    invariant under refinement, whether read as "same constructor shape" or as
    "count replicates per level." -/
theorem self_similarity_two_readings :
    -- form reading: decompose-shape invariant + strict descent + atomic floor
    ( (∀ r : Raw, r = Raw.a ∨ r = Raw.b ∨
          ∃ (u v : Raw) (h : u ≠ v), r = Raw.slash u v h)
      ∧ (∀ (x y : Raw) (h : x ≠ y),
          x.depth < (Raw.slash x y h).depth ∧ y.depth < (Raw.slash x y h).depth)
      ∧ (Raw.a.depth = 0 ∧ Raw.b.depth = 0) )
    ∧ -- count reading: level count replicates
    (∀ m n : Nat, numV (m + n) = numV m * numV n) :=
  ⟨E213.Theory.Raw.Lambek.self_similar_floor, self_similar_count⟩

end E213.Lib.Math.SelfSimilarityBridge
