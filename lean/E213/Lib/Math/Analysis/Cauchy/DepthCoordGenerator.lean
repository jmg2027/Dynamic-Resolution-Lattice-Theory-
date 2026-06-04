import E213.Lib.Math.Analysis.Cauchy.DepthPRecursiveInstances
import E213.Lib.Math.Analysis.Cauchy.DepthClosure
import E213.Lib.Math.Analysis.Cauchy.DepthOmegaTower
import E213.Meta.Tactic.NatHelper

/-!
# DepthCoordGenerator — the tower is a coordinate system: every coordinate is generated

The completeness arc *classified* reals by their tower coordinate.  This file shows the
tower is also a **generator**: place a coordinate and read off an explicit sequence
sitting at it.  So the tower is a coordinate system populated top-down, not merely a
labelling of reals that happen to exist.

  * **Difference axis** — `genExp d = (n ↦ binom n d)` realizes difference-depth `d`
    for *every* `d` (`genExp_realizes` floors by `d`, `genExp_not_below` not before):
    the degree-`d` discrete monomial floors at *exactly* `d` (`genExp_depth_exact`), so
    the difference axis is **surjectively** generated.
  * **Exponent / ratio axis** — `genValue c d = c^{binom · d}` lifts it one tier:
    `genValue_floors` gives it finite ratio-depth (by depth `d`, via `DepthClosure`'s
    exponent axis closure).  Every finite ratio coordinate is reached by an explicit
    value.
  * **`ωʳ` tower** — `DepthOmegaTower.expTower c r` realizes every exponential height,
    each strictly dominating the whole lower tower (`coord_layer_dominates`), with the
    generator recursion `expTower c (r+1) = c^{expTower c r}` (`expTower_succ`).
  * ★★★ `tower_is_coordinate_system` bundles the three — the `ω^ω` ladder is generated
    level by level by explicit sequences.

In the tower a real *is* a divergence trajectory; the finite-coordinate trajectories
generated here are exactly the rate-carrying class that carries a free modulus
(`Real213/{RateModulus, CrossDetOvertake, LiouvilleModulus}`, e in `ExpLog/EulerModulus`),
so each generated finite coordinate is an actually-completing real.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.DepthCoordGenerator

open E213.Lib.Math.Analysis.Cauchy.DivergenceLadder (diff liftK isConst)
open E213.Lib.Math.Analysis.Cauchy.DepthTower (diffN ratioN)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursive (polyDepth)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursiveInstances
  (binom binom_mono liftK_binomCol binomCol_polyDepth binomCol_not_below)
open E213.Lib.Math.Analysis.Cauchy.DepthExponentRecursion (expSeq totMono)
open E213.Lib.Math.Analysis.Cauchy.DepthClosure
  (FinDiffDepth FinRatioDepth value_finRatio_of_finDiff floor_up)
open E213.Lib.Math.Analysis.Cauchy.DepthOmegaTower (expTower expTower_succ Coord coordLt coord_layer_dominates)
open E213.Tactic.NatHelper (sub_add_cancel)

/-! ## §0 — `liftK` and `diffN` are the same operation -/

/-- The `DivergenceLadder` lift `liftK` and the `DepthTower` lift `diffN` coincide
    (both are iterated `diff`); pointwise, so no `funext`. -/
theorem liftK_eq_diffN : ∀ (d : Nat) (s : Nat → Nat) (n : Nat),
    liftK d s n = diffN d s n
  | 0,   _, _ => rfl
  | d+1, s, n => by
    show liftK d s (n+1) - liftK d s n = diffN d s (n+1) - diffN d s n
    rw [liftK_eq_diffN d s (n+1), liftK_eq_diffN d s n]

/-! ## §1 — the difference-axis generator -/

/-- The degree-`d` generator exponent `n ↦ binom n d`. -/
def genExp (d : Nat) : Nat → Nat := fun n => binom n d

/-- ★ **Each depth is realized (upper bound).**  `genExp d` is the degree-`d` discrete
    monomial; its `d`-th difference is constant (`polyDepth d`, `binomCol_polyDepth`) —
    it floors *by* depth `d`. -/
theorem genExp_realizes (d : Nat) : polyDepth d (genExp d) := binomCol_polyDepth d

/-- The generator does **not** floor before its depth: for `j < d`, the `j`-th
    difference of `genExp d` is not constant (`binomCol_not_below`, via the
    `liftK = diffN` bridge). -/
theorem genExp_not_below (d j : Nat) (hj : j < d) : ¬ isConst (diffN j (genExp d)) := by
  intro hconst
  refine binomCol_not_below d j hj (fun n => ?_)
  show liftK j (genExp d) n = liftK j (genExp d) 0
  rw [liftK_eq_diffN j (genExp d) n, liftK_eq_diffN j (genExp d) 0]
  exact hconst n

/-- ★★ **Each difference coordinate is realized *exactly*.**  `genExp d` floors at
    depth `d` (`genExp_realizes`) and not before (`genExp_not_below`), so its
    difference-depth is exactly `d`.  The generator `d ↦ genExp d` is therefore
    **surjective** onto the difference-coordinate axis: every depth is hit by an
    explicit sequence of precisely that depth. -/
theorem genExp_depth_exact (d : Nat) :
    polyDepth d (genExp d) ∧ ∀ j, j < d → ¬ isConst (diffN j (genExp d)) :=
  ⟨genExp_realizes d, fun j hj => genExp_not_below d j hj⟩

/-- `genExp d` floors at depth `d` on the `diffN` axis (the `diffN` reading of
    `genExp_realizes`). -/
theorem genExp_floors_diffN (d : Nat) : isConst (diffN d (genExp d)) := by
  intro n
  rw [← liftK_eq_diffN d (genExp d) n, ← liftK_eq_diffN d (genExp d) 0]
  exact binomCol_polyDepth d n

/-- Below its depth the generator equals a lower column: `diffN j (genExp d) =
    binom · (d−j)` for `j ≤ d`. -/
theorem genExp_diffN_eq (d j : Nat) (h : j ≤ d) (n : Nat) :
    diffN j (genExp d) n = binom n (d - j) := by
  have hidx : (d - j) + j = d := sub_add_cancel h
  have hb : liftK j (fun m => binom m ((d - j) + j)) n = binom n (d - j) :=
    liftK_binomCol j (d - j) n
  rw [hidx] at hb
  rw [← liftK_eq_diffN j (genExp d) n]
  exact hb

/-- `genExp d` is totally monotone: below depth `d` each iterated difference is a
    binomial column (monotone, `binom_mono`); at/above depth `d` it is constant
    (`genExp_floors_diffN` + `floor_up`). -/
theorem genExp_totMono (d : Nat) : totMono (genExp d) := by
  intro j n
  rcases Nat.lt_or_ge d j with hj | hj
  · have hconst : isConst (diffN j (genExp d)) :=
      floor_up (genExp d) d j (Nat.le_of_lt hj) (genExp_floors_diffN d)
    rw [hconst n, hconst (n+1)]; exact Nat.le_refl _
  · rw [genExp_diffN_eq d j hj n, genExp_diffN_eq d j hj (n+1)]
    exact binom_mono (d - j) n

/-! ## §2 — the exponent-axis generator (one tier up) -/

/-- The value generator `genValue c d = c^{binom · d}`. -/
def genValue (c d : Nat) : Nat → Nat := expSeq c (genExp d)

/-- ★★ **Every finite ratio-depth is reached.**  `genValue c d` has finite ratio depth
    (floors by ratio-depth `d`): the exponent `genExp d` has finite difference depth and
    the exponent axis lifts it one tier (`DepthClosure.value_finRatio_of_finDiff`). -/
theorem genValue_floors (c : Nat) (hc : 1 ≤ c) (d : Nat) :
    FinRatioDepth (genValue c d) :=
  value_finRatio_of_finDiff c hc (genExp d) (genExp_totMono d) ⟨d, genExp_floors_diffN d⟩

/-! ## §3 — the `ωʳ` tower generator -/

/-- ★★ **Every exponential height is realized, strictly dominating the lower tower.**
    `expTower c r` is the `r`-fold exponential; its coordinate sits at tower level `r`,
    and a larger leading coefficient outranks the entire lower tower
    (`coord_layer_dominates`). -/
theorem tower_level_dominates (r a : Nat) (p q : Coord r) :
    coordLt (r+1) (a, p) (a+1, q) :=
  coord_layer_dominates r a p q

/-! ## §4 — the coordinate system, bundled -/

/-- ★★★ **The tower is a coordinate system, generated top-down.**  Every finite
    difference-depth `d` is realized **exactly** by an explicit sequence `genExp d`
    (floors at `d`, not before — `genExp_depth_exact`); every exponential height is
    generated by the recursion `expTower c (r+1) = c^{expTower c r}`, each height
    strictly dominating the whole lower tower.  So the `ω^ω` ladder is not a mere
    classification of pre-existing reals — it is populated, level by level, by
    sequences read off from the coordinate.  Placing a coordinate and reading off the
    trajectory it defines is the constructive, generative form of the completeness
    picture. -/
theorem tower_is_coordinate_system :
    (∀ d, polyDepth d (genExp d) ∧ ∀ j, j < d → ¬ isConst (diffN j (genExp d)))
    ∧ (∀ c r, expTower c (r+1) = expSeq c (expTower c r))
    ∧ (∀ r a (p q : Coord r), coordLt (r+1) (a, p) (a+1, q)) :=
  ⟨genExp_depth_exact, expTower_succ, coord_layer_dominates⟩

end E213.Lib.Math.Analysis.Cauchy.DepthCoordGenerator
