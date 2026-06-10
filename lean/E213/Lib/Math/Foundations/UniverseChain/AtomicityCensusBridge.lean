import E213.Lib.Math.Foundations.UniverseChain.RawRecurrence
import E213.Theory.Atomicity

/-!
# The two 5s: atomicity sizes vs the depth-2 census (∅-axiom)

Atomicity's `5` is a Diophantine uniqueness of **sizes**
(`Five.atomic_iff_five`: unique alive decomposition
`5 = 2·1 + 3·1` = `pairSize + closureSize`).  The census `5` is a
**term count** (`rawCount 2` = 2 atoms + `C(3,2)` composites).
They are not one definition; their agreement factors through a
single mediating fixed point:

  `choose2 n = n  ↔  n = 3`   (for `1 ≤ n`)

and `3` is simultaneously `closureSize` ("the pair plus their
relation" — literally `Raw.level1_set = [a, b, a/b]`) and the
level-≤1 population `rawCount 1`.  The level-2 additions form one
`Raw.swap` orbit of size `pairSize = 2`.  So the two 5s agree
because the same `3` is both a forced size and a forced census —
a mediated identity, not numerology and not a coincidence.
-/

namespace E213.Lib.Math.Foundations.UniverseChain.AtomicityCensusBridge

open E213.Theory
open E213.Theory.Atomicity
open E213.Lib.Math.Foundations.UniverseChain.RawRecurrence (choose2 rawCount)
open E213.Lib.Math.Foundations.UniverseChain.RawDepthCount
  (depthLe2List s_ab s_a_ab s_b_ab)

-- ═══ choose2 elementary structure ═══

/-- `choose2 (m+1) = choose2 m + m` for every `m` (the `m = 0` case
    is `0 = 0`; `m ≥ 1` is definitional). -/
theorem choose2_succ : ∀ m : Nat, choose2 (m + 1) = choose2 m + m
  | 0 => rfl
  | _ + 1 => rfl

/-- Above the fixed point the map escapes: `n < choose2 n` for all
    `n ≥ 4` (stated in offset form). -/
theorem choose2_gt_self : (k : Nat) → k + 4 < choose2 (k + 4)
  | 0 => by decide
  | k + 1 => by
    have h1 : k + 5 ≤ choose2 (k + 4) := choose2_gt_self k
    have h2 : choose2 (k + 4) + 0 < choose2 (k + 4) + (k + 4) :=
      Nat.add_lt_add_left (Nat.succ_pos (k + 3)) (choose2 (k + 4))
    exact E213.Tactic.NatHelper.lt_of_le_lt h1 h2

/-- ★ **The mediating fixed point**: among positive integers,
    `choose2` fixes exactly `3`.  (`choose2 0 = 0` is the trivial
    fixed point excluded by positivity.) -/
theorem choose2_fixed (n : Nat) (h1 : 1 ≤ n) : choose2 n = n ↔ n = 3 :=
  match n, h1 with
  | 0, h => absurd h (by decide)
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | k + 4, _ =>
    ⟨fun h => absurd h.symm (Nat.ne_of_lt (choose2_gt_self k)),
     fun h => absurd (h ▸ Nat.le_add_left 4 k) (by decide)⟩

-- ═══ The level-2 additions are one swap orbit ═══

theorem swap_s_ab : Raw.swap s_ab = s_ab := by
  apply Subtype.ext; rfl

theorem swap_s_a_ab : Raw.swap s_a_ab = s_b_ab := by
  apply Subtype.ext; rfl

theorem swap_s_b_ab : Raw.swap s_b_ab = s_a_ab := by
  apply Subtype.ext; rfl

-- ═══ Capstone ═══

/-- ★★★ **The two 5s, mediated.**  Bundles:
    (1) the level-≤1 population IS the closure size
        (`Raw.level1_set` is literally "the pair plus their
        relation");
    (2) the level-2 census = `pairSize + choose2 closureSize`;
    (3) the mediating fixed point `choose2 3 = 3` — with its
        uniqueness among positives (`choose2_fixed`);
    (4) both 5s: the census value and atomicity's `Atomic 5`;
    (5) the level-2 additions form one swap orbit (size
        `pairSize`), the level-≤1 stratum is swap-closed.

    The agreement of the two 5s is forced by the same `3` that
    `closureSize` forces — not a coincidence, not an identity of
    definitions. -/
theorem two_fives :
    -- (1) level-1 population = closure size
    rawCount 1 = PrimitiveSizes.closureSize
    ∧ Raw.level1_set.length = PrimitiveSizes.closureSize
    -- (2) the census decomposition
    ∧ rawCount 2 = PrimitiveSizes.pairSize
        + choose2 PrimitiveSizes.closureSize
    -- (3) the mediating fixed point
    ∧ choose2 PrimitiveSizes.closureSize = PrimitiveSizes.closureSize
    -- (4) both 5s
    ∧ rawCount 2 = 5 ∧ depthLe2List.length = 5 ∧ Five.Atomic 5
    -- (5) swap structure: one orbit of size pairSize + a fixed line
    ∧ Raw.swap s_a_ab = s_b_ab ∧ Raw.swap s_b_ab = s_a_ab
    ∧ Raw.swap s_ab = s_ab :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, Five.atomic_five,
   swap_s_a_ab, swap_s_b_ab, swap_s_ab⟩

/-- Uniqueness face of the mediation, re-exported at capstone level:
    the fixed point that makes the two 5s agree is the *only* one. -/
theorem mediating_fixed_point_unique (n : Nat) (h1 : 1 ≤ n) :
    choose2 n = n ↔ n = PrimitiveSizes.closureSize :=
  choose2_fixed n h1

end E213.Lib.Math.Foundations.UniverseChain.AtomicityCensusBridge
