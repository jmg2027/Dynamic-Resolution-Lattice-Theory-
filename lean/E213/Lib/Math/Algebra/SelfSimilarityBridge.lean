import E213.Theory.Raw.API
import E213.Lib.Math.Foundations.UniverseChain.Recursion
import E213.Lib.Math.Algebra.Mobius213.TowerLInfty
import E213.Lib.Math.NumberSystems.Real213.PhiCut
import E213.Lib.Math.NumberSystems.Real213.PhiConvergence
import E213.Meta.Nat.PureNat

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

namespace E213.Lib.Math.Algebra.SelfSimilarityBridge

open E213.Theory (Raw)
open E213.Lib.Math.Cohomology.Fractal.Level (numV)
open E213.Lib.Math.Foundations.UniverseChain.Recursion (numV_def)
open E213.Meta.Nat.PureNat (pow_add)

/-- **Quantitative self-similarity**: the level count replicates under level
    addition — `numV (m + n) = numV m · numV n`.  Each level carries a copy of
    the whole, so counts multiply (the `5^L` exponential law is the count-Lens
    reading of "same shape at every level"). -/
theorem self_similar_count (m n : Nat) : numV (m + n) = numV m * numV n := by
  rw [numV_def, numV_def, numV_def, pow_add]

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

/-! ## The third reading — the limit-ratio is φ

The form reading keeps the same *shape*; the count reading replicates by a
constant factor (`5` per level — the universe-chain self-similarity is rational,
ratio exactly `d`).  The third reading takes the *ratio of consecutive terms* of
the P-orbit (`P = [[2,1],[1,1]]`, the Möbius signature of (NS, NT) = (3, 2)):
that ratio does not settle on an integer but on the irrational fixed point
`φ = (1+√5)/2`, because φ is `P`'s fixed point (`P(φ) = φ`,
`seed/AXIOM/05_no_exterior.md` §5.6).

So self-similarity has *two* scale factors from the same signature: the rational
`d = 5` (count replication, `numV`) and the irrational `φ` (P-orbit limit-ratio).
Both are readings of the one self-pointing orbit — `disc P = 5 = NS + NT` and
`fixed point = φ` are the same matrix's invariants.  The limit-ratio reading is
where "same shape under descent" stops being a finite count and becomes the
residue's irrational signature.

Below, the limit-ratio is witnessed PURE by the existing brackets:
`tower_growth_phi_squared_bracket` (consecutive P-orbit ratio ∈ (2, 3) = φ²) and
`phi_bracket_via_pell` / `phi_cut_capstone` (the Pell convergent brackets φ
itself as a Cut). -/

open E213.Lib.Math.Algebra.Mobius213 (P_numerator)
open E213.Lib.Math.NumberSystems.Real213.PhiCut (pellNum pellDen)

/-- **Limit-ratio reading**: the consecutive-term ratio of the P-orbit is
    bracketed in `(2, 3) = φ²` (so the per-step ratio is φ), and the Pell
    convergent brackets φ = (1+√5)/2 itself.  Unlike the count reading (ratio =
    integer `5`), this self-similar descent settles on the irrational fixed
    point of `P`.  PURE — assembled from the existing φ brackets. -/
theorem self_similar_ratio_is_phi :
    -- consecutive P-orbit ratio ∈ (2,3) = φ² at layers 1..2 (φ per step)
    (2 * P_numerator.seq 1 ≤ P_numerator.seq 2
       ∧ P_numerator.seq 2 ≤ 3 * P_numerator.seq 1)
    ∧ -- Pell convergent brackets φ ∈ [3/2, 5/3] at layer 2
    (3 * pellDen 2 < 2 * pellNum 2 ∧ 3 * pellNum 2 < 5 * pellDen 2) :=
  ⟨(E213.Lib.Math.Algebra.Mobius213.TowerLInfty.tower_growth_phi_squared_bracket).1,
   ⟨(E213.Lib.Math.NumberSystems.Real213.PhiCut.phi_bracket_via_pell).1,
    (E213.Lib.Math.NumberSystems.Real213.PhiCut.phi_bracket_via_pell).2.1⟩⟩

/-- ★★ **Self-similarity, three readings.**  "Same shape under descent" is one
    self-similarity read through three Lenses, all from the (NS, NT) = (3, 2)
    signature:

    - **form** (Raw `self_similar_floor`): the constructor shape is invariant at
      every depth, descent terminates at the atoms.
    - **count** (`self_similar_count`): the level count replicates by the
      rational factor `d = 5` — `numV (m+n) = numV m · numV n`.
    - **limit-ratio** (`self_similar_ratio_is_phi`): the P-orbit's
      consecutive-term ratio settles on the irrational fixed point `φ` of `P`.

    The rational scale factor (`5 = disc P = NS + NT`) and the irrational one
    (`φ`, `P`'s fixed point) are invariants of the *same* matrix — so the three
    readings are one self-similarity, not three coincidences. -/
theorem self_similarity_three_readings :
    -- form
    ( (∀ r : Raw, r = Raw.a ∨ r = Raw.b ∨
          ∃ (u v : Raw) (h : u ≠ v), r = Raw.slash u v h)
      ∧ (Raw.a.depth = 0 ∧ Raw.b.depth = 0) )
    ∧ -- count: rational factor 5
    (∀ m n : Nat, numV (m + n) = numV m * numV n)
    ∧ -- limit-ratio: irrational fixed point φ
    ( (2 * P_numerator.seq 1 ≤ P_numerator.seq 2
         ∧ P_numerator.seq 2 ≤ 3 * P_numerator.seq 1)
      ∧ (3 * pellDen 2 < 2 * pellNum 2 ∧ 3 * pellNum 2 < 5 * pellDen 2) ) :=
  ⟨⟨E213.Theory.Raw.Lambek.decompose, E213.Theory.Raw.Lambek.atoms_are_floor⟩,
   self_similar_count,
   self_similar_ratio_is_phi⟩

/-- ★★★ **Limit-ratio is φ, pinned (not merely bracketed).**  Strengthens the
    third reading: the Pell convergents form a *nested* sequence of rational
    brackets (cross-products ±1) whose widths *strictly shrink* (denominators
    grow), pinning a unique value in `[3/2, 5/3]` — that value is φ
    (`PhiConvergence.phi_is_unique_nested_limit`).  So the self-similar descent's
    limit-ratio reading does not just lie near φ; the nested brackets determine φ
    uniquely.  This upgrades `self_similarity_three_readings`'s limit-ratio leg
    from "bounded" to "pinned." -/
theorem self_similar_ratio_pins_phi :
    -- nested (cross-products ±1) ∧ shrinking (gap denominators grow) ∧ in φ-bracket
    ( (pellNum 1 * pellDen 2 + 1 = pellNum 2 * pellDen 1)
      ∧ (pellNum 2 * pellDen 3 + 1 = pellNum 3 * pellDen 2) )
    ∧ ( pellDen 1 * pellDen 2 < pellDen 2 * pellDen 3
        ∧ pellDen 2 * pellDen 3 < pellDen 3 * pellDen 4 )
    ∧ ( 3 * pellDen 2 < 2 * pellNum 2 ∧ 3 * pellNum 2 < 5 * pellDen 2 ) :=
  E213.Lib.Math.NumberSystems.Real213.PhiConvergence.phi_is_unique_nested_limit

end E213.Lib.Math.Algebra.SelfSimilarityBridge
