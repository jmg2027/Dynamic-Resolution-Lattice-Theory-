import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly
import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMasterId
import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertOrder
import E213.Meta.Nat.PolyNatMTactic

/-!
# LambertBridge — the convolution–master bridge (the weld's last brick, F1–F7)

Executes `lowerbase_blueprint.md` F1–F7: connect the suffix sums of the two
`LowerBase` convolutions (`LambertPoly`) to the master-identity accumulators
(`LambertMasterId`), and close the general-`i` suffix dominance.

This file: **F1** — the reversed convergent-coefficient lists are the
`truncA/truncB` coefficient stacks:

  `rev (AP (2k+1)) = truncA (2k+1) k`,  `rev (BP (2k+1)) = truncB (2k+1) k`

(+ even-level twins), via `rev_ladd_eq`/`rev_ladd_succ`/`rev_lsmul` and the
`truncA/B` three-term recursions; the support-vanishing `apF (2k+1) (k+1+j) = 0`
closes the parity mismatches.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertBridge

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
  (ladd lsmul AP BP)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMinor (apF bpF)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly (rev)

/-! ## §1 — reversal infrastructure -/

theorem lsmul_append (k : Nat) : ∀ (a b : List Nat),
    lsmul k (a ++ b) = lsmul k a ++ lsmul k b
  | [], _ => rfl
  | a₀ :: as, b => by
    show k * a₀ :: lsmul k (as ++ b) = k * a₀ :: (lsmul k as ++ lsmul k b)
    rw [lsmul_append k as b]

theorem rev_lsmul (k : Nat) : ∀ l : List Nat, rev (lsmul k l) = lsmul k (rev l)
  | [] => rfl
  | c :: cs => by
    show rev (lsmul k cs) ++ [k * c] = lsmul k (rev cs ++ [c])
    rw [rev_lsmul k cs, lsmul_append k (rev cs) [c]]
    rfl

theorem ladd_append_eq : ∀ (a b : List Nat) (c d : Nat), a.length = b.length →
    ladd (a ++ [c]) (b ++ [d]) = ladd a b ++ [c + d]
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => Nat.noConfusion h
  | _ :: _, [], _, _, h => Nat.noConfusion h
  | a₀ :: as, b₀ :: bs, c, d, h => by
    show (a₀ + b₀) :: ladd (as ++ [c]) (bs ++ [d])
        = (a₀ + b₀) :: (ladd as bs ++ [c + d])
    rw [ladd_append_eq as bs c d (Nat.succ.inj h)]

theorem rev_ladd_eq : ∀ (a b : List Nat), a.length = b.length →
    rev (ladd a b) = ladd (rev a) (rev b)
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | a₀ :: as, b₀ :: bs, h => by
    show rev (ladd as bs) ++ [a₀ + b₀] = ladd (rev as ++ [a₀]) (rev bs ++ [b₀])
    rw [rev_ladd_eq as bs (Nat.succ.inj h),
        ladd_append_eq (rev as) (rev bs) a₀ b₀ (by
          rw [E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly.len_rev,
              E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly.len_rev]
          exact Nat.succ.inj h)]

theorem rev_ladd_succ : ∀ (a b : List Nat), a.length + 1 = b.length →
    rev (ladd a b) = ladd (0 :: rev a) (rev b)
  | [], [], h => Nat.noConfusion h
  | [], b₀ :: bs, h => by
    cases bs with
    | nil =>
      show [b₀] = ladd [0] [b₀]
      show [b₀] = [0 + b₀]
      rw [Nat.zero_add]
    | cons b₁ bs' => exact Nat.noConfusion (Nat.succ.inj h)
  | _ :: _, [], h => Nat.noConfusion h
  | a₀ :: as, b₀ :: bs, h => by
    show rev (ladd as bs) ++ [a₀ + b₀]
        = ladd (0 :: (rev as ++ [a₀])) (rev bs ++ [b₀])
    rw [rev_ladd_succ as bs (Nat.succ.inj h),
        show (0 :: (rev as ++ [a₀])) = (0 :: rev as) ++ [a₀] from rfl,
        ladd_append_eq (0 :: rev as) (rev bs) a₀ b₀ (by
          show (rev as).length + 1 = (rev bs).length
          rw [E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly.len_rev,
              E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly.len_rev]
          exact Nat.succ.inj h)]

/-! ## §2 — the truncated coefficient stacks and their three-term recursions -/

/-- `truncA n m = [apF n m, …, apF n 0]` — the constant-first coefficient list
    of `dev (AP n)` (when `m` = the degree). -/
def truncA (n : Nat) : Nat → List Nat
  | 0 => [apF n 0]
  | m + 1 => apF n (m + 1) :: truncA n m

def truncB (n : Nat) : Nat → List Nat
  | 0 => [bpF n 0]
  | m + 1 => bpF n (m + 1) :: truncB n m

/-- The `apF` three-term recursion lifts to the stacks. -/
theorem truncA_rec (n : Nat) : ∀ m,
    truncA (n + 2) (m + 1)
      = ladd (lsmul (2 * n + 3) (truncA (n + 1) (m + 1))) (truncA n m ++ [0])
  | 0 => by
    show [apF (n + 2) 1, apF (n + 2) 0]
        = ladd [(2 * n + 3) * apF (n + 1) 1, (2 * n + 3) * apF (n + 1) 0]
            [apF n 0, 0]
    show [apF (n + 2) 1, apF (n + 2) 0]
        = [(2 * n + 3) * apF (n + 1) 1 + apF n 0, (2 * n + 3) * apF (n + 1) 0 + 0]
    rw [show apF (n + 2) 1 = (2 * n + 3) * apF (n + 1) 1 + apF n 0 from rfl,
        show apF (n + 2) 0 = (2 * n + 3) * apF (n + 1) 0 from rfl,
        show (2 * n + 3) * apF (n + 1) 0 + 0 = (2 * n + 3) * apF (n + 1) 0 from
          Nat.add_zero _]
  | m + 1 => by
    show apF (n + 2) (m + 2) :: truncA (n + 2) (m + 1)
        = ladd ((2 * n + 3) * apF (n + 1) (m + 2)
              :: lsmul (2 * n + 3) (truncA (n + 1) (m + 1)))
            (apF n (m + 1) :: (truncA n m ++ [0]))
    show apF (n + 2) (m + 2) :: truncA (n + 2) (m + 1)
        = ((2 * n + 3) * apF (n + 1) (m + 2) + apF n (m + 1))
          :: ladd (lsmul (2 * n + 3) (truncA (n + 1) (m + 1))) (truncA n m ++ [0])
    rw [truncA_rec n m,
        show apF (n + 2) (m + 2)
          = (2 * n + 3) * apF (n + 1) (m + 2) + apF n (m + 1) from rfl]

theorem truncB_rec (n : Nat) : ∀ m,
    truncB (n + 2) (m + 1)
      = ladd (lsmul (2 * n + 3) (truncB (n + 1) (m + 1))) (truncB n m ++ [0])
  | 0 => by
    show [bpF (n + 2) 1, bpF (n + 2) 0]
        = ladd [(2 * n + 3) * bpF (n + 1) 1, (2 * n + 3) * bpF (n + 1) 0]
            [bpF n 0, 0]
    show [bpF (n + 2) 1, bpF (n + 2) 0]
        = [(2 * n + 3) * bpF (n + 1) 1 + bpF n 0, (2 * n + 3) * bpF (n + 1) 0 + 0]
    rw [show bpF (n + 2) 1 = (2 * n + 3) * bpF (n + 1) 1 + bpF n 0 from rfl,
        show bpF (n + 2) 0 = (2 * n + 3) * bpF (n + 1) 0 from rfl,
        show (2 * n + 3) * bpF (n + 1) 0 + 0 = (2 * n + 3) * bpF (n + 1) 0 from
          Nat.add_zero _]
  | m + 1 => by
    show bpF (n + 2) (m + 2) :: truncB (n + 2) (m + 1)
        = ladd ((2 * n + 3) * bpF (n + 1) (m + 2)
              :: lsmul (2 * n + 3) (truncB (n + 1) (m + 1)))
            (bpF n (m + 1) :: (truncB n m ++ [0]))
    show bpF (n + 2) (m + 2) :: truncB (n + 2) (m + 1)
        = ((2 * n + 3) * bpF (n + 1) (m + 2) + bpF n (m + 1))
          :: ladd (lsmul (2 * n + 3) (truncB (n + 1) (m + 1))) (truncB n m ++ [0])
    rw [truncB_rec n m,
        show bpF (n + 2) (m + 2)
          = (2 * n + 3) * bpF (n + 1) (m + 2) + bpF n (m + 1) from rfl]

/-! ## §3 — support vanishing beyond the degree (via `nth` + the lengths) -/

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertOrder (nth AP_nth BP_nth)

theorem nth_ge_len : ∀ (l : List Nat) (s : Nat), l.length ≤ s → nth l s = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: cs, s + 1, h => nth_ge_len cs s (Nat.le_of_succ_le_succ h)

theorem apF_vanish_odd (k : Nat) : apF (2 * k + 1) (k + 1) = 0 := by
  rw [← AP_nth (2 * k + 1) (k + 1)]
  exact nth_ge_len _ _ (by
    rw [(E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.AP_BP_length k).1]
    exact Nat.le_refl _)

theorem bpF_vanish_even (k : Nat) : bpF (2 * k + 2) (k + 1) = 0 := by
  rw [← BP_nth (2 * k + 2) (k + 1)]
  exact nth_ge_len _ _ (by
    rw [(E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.AP_BP_length k).2.2.2]
    exact Nat.le_refl _)

/-! ## §4 — F1: the reversed convergent lists ARE the coefficient stacks -/

private theorem lsmul_zero_cons (c : Nat) (l : List Nat) :
    lsmul c (0 :: l) = 0 :: lsmul c l := by
  show c * 0 :: lsmul c l = 0 :: lsmul c l
  rw [Nat.mul_zero]

/-- ★★★★ **F1, the 4-way joint induction**: at every level the reversal of the
    convergent coefficient list is the `trunc` stack (parities mirror
    `AP_BP_length`: equal-length `ladd` at A-odd/B-even, shifted at A-even/B-odd,
    support-vanishing absorbing the off-by-one). -/
theorem rev_trunc : ∀ k,
    rev (AP (2 * k + 1)) = truncA (2 * k + 1) k
    ∧ rev (AP (2 * k + 2)) = truncA (2 * k + 2) (k + 1)
    ∧ rev (BP (2 * k + 1)) = truncB (2 * k + 1) k
    ∧ rev (BP (2 * k + 2)) = truncB (2 * k + 2) k
  | 0 => ⟨by decide, by decide, by decide, by decide⟩
  | k + 1 => by
    obtain ⟨ihAo, ihAe, ihBo, ihBe⟩ := rev_trunc k
    obtain ⟨lA1, lA2, lB1, lB2⟩ :=
      E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.AP_BP_length k
    -- A-odd at k+1 : AP (2k+3), equal-length ladd
    have hAodd : rev (AP (2 * (k + 1) + 1)) = truncA (2 * (k + 1) + 1) (k + 1) := by
      show rev (ladd (lsmul (2 * (2 * k + 1) + 3) (AP (2 * k + 2))) (0 :: AP (2 * k + 1)))
          = truncA (2 * k + 3) (k + 1)
      rw [rev_ladd_eq _ _ (by
            rw [E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.lsmul_length, lA2]
            show k + 2 = (AP (2 * k + 1)).length + 1
            rw [lA1]),
          rev_lsmul,
          show rev (0 :: AP (2 * k + 1)) = rev (AP (2 * k + 1)) ++ [0] from rfl,
          ihAe, ihAo, truncA_rec (2 * k + 1) k]
    -- A-even at k+1 : AP (2k+4), shifted ladd + vanishing top
    have hAeven : rev (AP (2 * (k + 1) + 2)) = truncA (2 * (k + 1) + 2) (k + 2) := by
      show rev (ladd (lsmul (2 * (2 * k + 2) + 3) (AP (2 * k + 3))) (0 :: AP (2 * k + 2)))
          = truncA (2 * k + 4) (k + 2)
      have lA1' := (E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.AP_BP_length (k + 1)).1
      rw [rev_ladd_succ _ _ (by
            rw [E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.lsmul_length]
            show (AP (2 * (k + 1) + 1)).length + 1 = (0 :: AP (2 * k + 2)).length
            rw [lA1']
            show k + 2 + 1 = (AP (2 * k + 2)).length + 1
            rw [lA2]),
          rev_lsmul,
          show rev (0 :: AP (2 * k + 2)) = rev (AP (2 * k + 2)) ++ [0] from rfl,
          ihAe,
          show AP (2 * k + 3) = AP (2 * (k + 1) + 1) from rfl, hAodd,
          truncA_rec (2 * k + 2) (k + 1),
          show truncA (2 * k + 3) (k + 2)
            = apF (2 * k + 3) (k + 2) :: truncA (2 * k + 3) (k + 1) from rfl,
          show apF (2 * k + 3) (k + 2) = 0 from apF_vanish_odd (k + 1),
          lsmul_zero_cons]
      rfl
    -- B-odd at k+1 : BP (2k+3), shifted ladd + vanishing top
    have hBodd : rev (BP (2 * (k + 1) + 1)) = truncB (2 * (k + 1) + 1) (k + 1) := by
      show rev (ladd (lsmul (2 * (2 * k + 1) + 3) (BP (2 * k + 2))) (0 :: BP (2 * k + 1)))
          = truncB (2 * k + 3) (k + 1)
      rw [rev_ladd_succ _ _ (by
            rw [E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.lsmul_length, lB2]
            show k + 1 + 1 = (0 :: BP (2 * k + 1)).length
            show k + 1 + 1 = (BP (2 * k + 1)).length + 1
            rw [lB1]),
          rev_lsmul,
          show rev (0 :: BP (2 * k + 1)) = rev (BP (2 * k + 1)) ++ [0] from rfl,
          ihBe, ihBo, truncB_rec (2 * k + 1) k,
          show truncB (2 * k + 2) (k + 1)
            = bpF (2 * k + 2) (k + 1) :: truncB (2 * k + 2) k from rfl,
          show bpF (2 * k + 2) (k + 1) = 0 from bpF_vanish_even k,
          lsmul_zero_cons]
    refine ⟨hAodd, hAeven, hBodd, ?_⟩
    -- B-even at k+1 : BP (2k+4), equal-length ladd
    show rev (ladd (lsmul (2 * (2 * k + 2) + 3) (BP (2 * k + 3))) (0 :: BP (2 * k + 2)))
        = truncB (2 * k + 4) (k + 1)
    have lB1' := (E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.AP_BP_length (k + 1)).2.2.1
    rw [rev_ladd_eq _ _ (by
          rw [E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.lsmul_length]
          show (BP (2 * (k + 1) + 1)).length = (0 :: BP (2 * k + 2)).length
          rw [lB1']
          show k + 2 = (BP (2 * k + 2)).length + 1
          rw [lB2]),
        rev_lsmul,
        show rev (0 :: BP (2 * k + 2)) = rev (BP (2 * k + 2)) ++ [0] from rfl,
        ihBe,
        show BP (2 * k + 3) = BP (2 * (k + 1) + 1) from rfl, hBodd,
        truncB_rec (2 * k + 2) k]
    rfl

/-- The odd-level identities the brick consumes. -/
theorem rev_AP_odd (i : Nat) : rev (AP (2 * i + 1)) = truncA (2 * i + 1) i :=
  (rev_trunc i).1

theorem rev_BP_odd (i : Nat) : rev (BP (2 * i + 1)) = truncB (2 * i + 1) i :=
  (rev_trunc i).2.2.1

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertBridge
