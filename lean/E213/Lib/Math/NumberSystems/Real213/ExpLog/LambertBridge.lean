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

/-! ## §5 — F2: the accumulator snoc (last-step peel)

The bridges walk the convolution from the polynomial's head (`s = i` end) while
`Aacc/Bacc` recurse from `s = 0`; the snoc lemmas peel the accumulators' LAST
step.  `wprod cc m` is the threaded weight after `m` steps
(`= Π_{j<m}(cc−2j−1)(cc−2j)`; at `cc = 2N+1` this is `W(N,m) =
(2N+1)!/(2N−2m+1)!`), with the **shift identity**
`wprod cc (m+1) = (cc−1)·cc·wprod (cc−2) m` aligning head-peel and threading. -/

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMasterId
  (Aacc Bacc sub_one_sub)

/-- The threaded weight after `m` accumulator steps. -/
def wprod (cc : Nat) : Nat → Nat
  | 0 => 1
  | m + 1 => wprod cc m * ((cc - 2 * m - 1) * (cc - 2 * m))

private theorem sub_two_sub (a b : Nat) : a - 2 - b = a - (b + 2) := by
  calc a - 2 - b = a - 1 - 1 - b := rfl
    _ = a - 1 - (b + 1) := sub_one_sub (a - 1) b
    _ = a - ((b + 1) + 1) := sub_one_sub a (b + 1)

/-- ★★ **The threading shift**: one head-step trades for the `(cc−1)·cc` factor. -/
theorem wprod_shift : ∀ (cc m : Nat),
    wprod cc (m + 1) = (cc - 1) * cc * wprod (cc - 2) m
  | cc, 0 => by
    show wprod cc 0 * ((cc - 2 * 0 - 1) * (cc - 2 * 0)) = (cc - 1) * cc * wprod (cc - 2) 0
    show 1 * ((cc - 0 - 1) * (cc - 0)) = (cc - 1) * cc * 1
    rw [Nat.sub_zero, Nat.one_mul, Nat.mul_one]
  | cc, m + 1 => by
    show wprod cc (m + 1) * ((cc - 2 * (m + 1) - 1) * (cc - 2 * (m + 1)))
        = (cc - 1) * cc * (wprod (cc - 2) m * ((cc - 2 - 2 * m - 1) * (cc - 2 - 2 * m)))
    rw [wprod_shift cc m,
        show cc - 2 - 2 * m = cc - 2 * (m + 1) from by
          rw [sub_two_sub cc (2 * m)]
          rfl,
        show cc - 2 * (m + 1) - 1 = cc - 2 * (m + 1) - 1 from rfl]
    ring_nat

/-- ★★★ **The `Aacc` snoc**: peel the LAST step with its threaded weight. -/
theorem Aacc_snoc (n : Nat) : ∀ (m cc w s : Nat),
    Aacc n cc w s (m + 1) = Aacc n cc w s m + w * wprod cc m * apF n (s + m)
  | 0, cc, w, s => by
    show w * apF n s + 0 = 0 + w * wprod cc 0 * apF n (s + 0)
    rw [Nat.add_zero, Nat.zero_add]
    show w * apF n s = w * 1 * apF n s
    rw [Nat.mul_one]
  | m + 1, cc, w, s => by
    show w * apF n s + Aacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) (m + 1)
        = (w * apF n s + Aacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) m)
          + w * wprod cc (m + 1) * apF n (s + (m + 1))
    rw [Aacc_snoc n m (cc - 2) (w * (cc - 1) * cc) (s + 1), wprod_shift cc m,
        show s + 1 + m = s + (m + 1) from by
          rw [Nat.succ_add s m]
          rfl]
    ring_nat

/-- ★★★ **The `Bacc` snoc** (the term carries the running coefficient `cc−2m`). -/
theorem Bacc_snoc (n : Nat) : ∀ (m cc w s : Nat),
    Bacc n cc w s (m + 1)
      = Bacc n cc w s m + w * wprod cc m * ((cc - 2 * m) * bpF n (s + m))
  | 0, cc, w, s => by
    show w * cc * bpF n s + 0 = 0 + w * wprod cc 0 * ((cc - 2 * 0) * bpF n (s + 0))
    rw [Nat.add_zero, Nat.zero_add]
    show w * cc * bpF n s = w * 1 * ((cc - 0) * bpF n s)
    rw [Nat.mul_one, Nat.sub_zero]
    ring_nat
  | m + 1, cc, w, s => by
    show w * cc * bpF n s + Bacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) (m + 1)
        = (w * cc * bpF n s + Bacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) m)
          + w * wprod cc (m + 1) * ((cc - 2 * (m + 1)) * bpF n (s + (m + 1)))
    rw [Bacc_snoc n m (cc - 2) (w * (cc - 1) * cc) (s + 1), wprod_shift cc m,
        show s + 1 + m = s + (m + 1) from by rw [Nat.succ_add s m]; rfl,
        show cc - 2 - 2 * m = cc - 2 * (m + 1) from by
          rw [sub_two_sub cc (2 * m)]; rfl]
    ring_nat

/-! ## §6 — F3 weight layer: σ/γ-steps and the product matches

The `(m, p) → (m−1, p−1)` head-peel of the convolution preserves `N̂ = J + g`
(`g = m − p` the invariant); these lemmas match the polynomial coefficient
ratios with the accumulator's threaded-weight steps, in both regimes
(`p ≤ J` exactly, `p > J` both sides vanish — `Nat`-subtraction is exactly
right). -/

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertOrder (nth_ladd nth_lsmul)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly (lmulC sListC cListC)

def AaccSum (n N k : Nat) : Nat := Aacc n (2 * N + 1) 1 0 k
def BaccSum (n N k : Nat) : Nat := Bacc n (2 * N + 1) 1 0 k

theorem AaccSum_snoc (n N m : Nat) :
    AaccSum n N (m + 1) = AaccSum n N m + wprod (2 * N + 1) m * apF n m := by
  have h := Aacc_snoc n m (2 * N + 1) 1 0
  rw [Nat.one_mul, Nat.zero_add] at h
  exact h

theorem BaccSum_snoc (n N m : Nat) :
    BaccSum n N (m + 1)
      = BaccSum n N m + wprod (2 * N + 1) m * ((2 * N + 1 - 2 * m) * bpF n m) := by
  have h := Bacc_snoc n m (2 * N + 1) 1 0
  rw [Nat.one_mul, Nat.zero_add] at h
  exact h

/-- The convolution coefficient recursions (head peel). -/
theorem nth_lmulC_zero (a₀ : Nat) (as b : List Nat) :
    nth (lmulC (a₀ :: as) b) 0 = a₀ * nth b 0 := by
  show nth (ladd (lsmul a₀ b) (0 :: lmulC as b)) 0 = a₀ * nth b 0
  rw [nth_ladd, nth_lsmul]
  show a₀ * nth b 0 + 0 = a₀ * nth b 0
  rw [Nat.add_zero]

theorem nth_lmulC_succ (a₀ : Nat) (as b : List Nat) (p : Nat) :
    nth (lmulC (a₀ :: as) b) (p + 1) = a₀ * nth b (p + 1) + nth (lmulC as b) p := by
  show nth (ladd (lsmul a₀ b) (0 :: lmulC as b)) (p + 1) = _
  rw [nth_ladd, nth_lsmul]
  rfl

theorem sListC_head : ∀ J, nth (sListC J) 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

theorem cListC_head : ∀ J, nth (cListC J) 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

/-- ★★ **The σ-step**: `σ_{p+1} = (2(J−p))·(2(J−p)+1)·σ_p` (`Nat`-subtraction
    makes the past-the-end regime vanish on both sides). -/
theorem sig_step : ∀ (J p : Nat),
    nth (sListC J) (p + 1) = (2 * (J - p)) * (2 * (J - p) + 1) * nth (sListC J) p
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | J + 1, 0 => by
    show nth (lsmul ((2 * J + 2) * (2 * J + 3)) (sListC J)) 0
        = (2 * (J + 1 - 0)) * (2 * (J + 1 - 0) + 1) * nth (sListC (J + 1)) 0
    rw [nth_lsmul, sListC_head J, sListC_head (J + 1), Nat.mul_one, Nat.mul_one,
        Nat.sub_zero]
    ring_nat
  | J + 1, p + 1 => by
    show nth (lsmul ((2 * J + 2) * (2 * J + 3)) (sListC J)) (p + 1)
        = (2 * (J + 1 - (p + 1))) * (2 * (J + 1 - (p + 1)) + 1)
          * nth (lsmul ((2 * J + 2) * (2 * J + 3)) (sListC J)) p
    rw [nth_lsmul, nth_lsmul, sig_step J p, Nat.succ_sub_succ]
    ring_nat

/-- The γ-step: `γ_{p+1} = (2(J−p)−1)·(2(J−p))·γ_p`. -/
theorem gam_step : ∀ (J p : Nat),
    nth (cListC J) (p + 1)
      = (2 * (J - p) - 1) * (2 * (J - p)) * nth (cListC J) p
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | J + 1, 0 => by
    show nth (lsmul ((2 * J + 1) * (2 * J + 2)) (cListC J)) 0
        = (2 * (J + 1 - 0) - 1) * (2 * (J + 1 - 0)) * nth (cListC (J + 1)) 0
    rw [nth_lsmul, cListC_head J, cListC_head (J + 1), Nat.mul_one, Nat.mul_one,
        Nat.sub_zero, show 2 * (J + 1) - 1 = 2 * J + 1 from rfl]
    ring_nat
  | J + 1, p + 1 => by
    show nth (lsmul ((2 * J + 1) * (2 * J + 2)) (cListC J)) (p + 1)
        = (2 * (J + 1 - (p + 1)) - 1) * (2 * (J + 1 - (p + 1)))
          * nth (lsmul ((2 * J + 1) * (2 * J + 2)) (cListC J)) p
    rw [nth_lsmul, nth_lsmul, gam_step J p, Nat.succ_sub_succ]
    ring_nat

private theorem sub_vanish : ∀ (a b : Nat), a - (a + b) = 0
  | a, 0 => by rw [Nat.add_zero]; exact Nat.sub_self a
  | a, b + 1 => by
    show (a - (a + b)).pred = 0
    rw [sub_vanish a b]
    rfl

private theorem sub_cancel_left {x : Nat} (k : Nat) : k + x - x = k :=
  E213.Tactic.NatHelper.add_sub_cancel_right k x

/-- ★★ **The A-side product match**: the σ-ratio equals the `wprod`-step
    factor (both regimes; products vanish together past `J`). -/
theorem prod_match (J p g : Nat) :
    (2 * (J - p)) * (2 * (J - p) + 1)
      = ((2 * (J + g) + 1) - 2 * (p + g) - 1) * ((2 * (J + g) + 1) - 2 * (p + g)) := by
  rcases Nat.lt_or_ge J p with hlt | hge
  · obtain ⟨e, he⟩ := Nat.le.dest hlt
    have hJp : J - p = 0 := by
      rw [← he, show J + 1 + e = J + (1 + e) from by ring_nat]
      exact sub_vanish J (1 + e)
    have hsub : (2 * (J + g) + 1) - 2 * (p + g) = 0 := by
      rw [← he,
          show 2 * ((J + 1 + e) + g) = (2 * (J + g) + 1) + (2 * e + 1) from by ring_nat]
      exact sub_vanish _ _
    rw [hJp, hsub]
  · obtain ⟨d, hd⟩ := Nat.le.dest hge
    rw [← hd,
        show p + d - p = d from by
          rw [Nat.add_comm p d]; exact sub_cancel_left d,
        show (2 * ((p + d) + g) + 1) - 2 * (p + g) = 2 * d + 1 from by
          rw [show 2 * ((p + d) + g) + 1 = (2 * d + 1) + (2 * (p + g)) from by ring_nat]
          exact sub_cancel_left (2 * d + 1),
        show 2 * d + 1 - 1 = 2 * d from rfl]

/-- ★★ **The B-side product match**: γ-ratio × (old coefficient) =
    `wprod`-step × (new coefficient). -/
theorem prod_match_B (J p g : Nat) :
    (2 * (J - p) - 1) * (2 * (J - p)) * ((2 * (J + g) + 1) - 2 * (p + g))
      = ((2 * (J + g) + 1) - 2 * (p + g) - 1) * ((2 * (J + g) + 1) - 2 * (p + g))
        * ((2 * (J + g) + 1) - 2 * (p + 1 + g)) := by
  rcases Nat.lt_or_ge J p with hlt | hge
  · obtain ⟨e, he⟩ := Nat.le.dest hlt
    have hsub : (2 * (J + g) + 1) - 2 * (p + g) = 0 := by
      rw [← he,
          show 2 * ((J + 1 + e) + g) = (2 * (J + g) + 1) + (2 * e + 1) from by ring_nat]
      exact sub_vanish _ _
    rw [hsub, Nat.mul_zero,
        show ((0 : Nat) - 1) * 0 * ((2 * (J + g) + 1) - 2 * (p + 1 + g))
          = 0 from by rw [Nat.mul_zero, Nat.zero_mul]]
  · obtain ⟨d, hd⟩ := Nat.le.dest hge
    rw [← hd,
        show p + d - p = d from by
          rw [Nat.add_comm p d]; exact sub_cancel_left d,
        show (2 * ((p + d) + g) + 1) - 2 * (p + g) = 2 * d + 1 from by
          rw [show 2 * ((p + d) + g) + 1 = (2 * d + 1) + (2 * (p + g)) from by ring_nat]
          exact sub_cancel_left (2 * d + 1)]
    cases d with
    | zero =>
      rw [show (2 * ((p + 0) + g) + 1) - 2 * (p + 1 + g) = 0 from by
            rw [show 2 * (p + 1 + g) = (2 * ((p + 0) + g) + 1) + 1 from by ring_nat]
            exact sub_vanish _ 1,
          Nat.mul_zero]
    | succ d' =>
      rw [show (2 * ((p + (d' + 1)) + g) + 1) - 2 * (p + 1 + g) = 2 * d' + 1 from by
            rw [show 2 * ((p + (d' + 1)) + g) + 1
                  = (2 * d' + 1) + (2 * (p + 1 + g)) from by ring_nat]
            exact sub_cancel_left (2 * d' + 1),
          show 2 * (d' + 1) - 1 = 2 * d' + 1 from rfl,
          show 2 * (d' + 1) + 1 - 1 = 2 * (d' + 1) from rfl]
      ring_nat



/-! ## §7 — F3: the bridges proper -/

/-- ★★★ **A-side weight match**: `Mf(g)·σ_p = wprod (p+g)` — the fixed-`g`
    multiplier converts the sinh-coefficients into the accumulator weights. -/
theorem wmatchA (J g : Nat) : ∀ p,
    wprod (2 * (J + g) + 1) g * nth (sListC J) p = wprod (2 * (J + g) + 1) (p + g)
  | 0 => by
    rw [sListC_head J, Nat.mul_one, Nat.zero_add]
  | p + 1 => by
    rw [sig_step J p,
        show wprod (2 * (J + g) + 1) g
            * ((2 * (J - p)) * (2 * (J - p) + 1) * nth (sListC J) p)
          = (2 * (J - p)) * (2 * (J - p) + 1)
            * (wprod (2 * (J + g) + 1) g * nth (sListC J) p) from by ring_nat,
        wmatchA J g p,
        show p + 1 + g = (p + g) + 1 from Nat.succ_add p g,
        show wprod (2 * (J + g) + 1) ((p + g) + 1)
          = wprod (2 * (J + g) + 1) (p + g)
            * (((2 * (J + g) + 1) - 2 * (p + g) - 1)
              * ((2 * (J + g) + 1) - 2 * (p + g))) from rfl,
        ← prod_match J p g]
    ring_nat

/-- ★★★ **B-side weight match**: `Mf(g)·(2J+1)·γ_p = wprod (p+g) ·
    ((2(J+g)+1) − 2(p+g))` — the cosh side carries the running coefficient. -/
theorem wmatchB (J g : Nat) : ∀ p,
    wprod (2 * (J + g) + 1) g * ((2 * J + 1) * nth (cListC J) p)
      = wprod (2 * (J + g) + 1) (p + g) * ((2 * (J + g) + 1) - 2 * (p + g))
  | 0 => by
    rw [cListC_head J, Nat.mul_one, Nat.zero_add,
        show (2 * (J + g) + 1) - 2 * g = 2 * J + 1 from by
          rw [show 2 * (J + g) + 1 = (2 * J + 1) + 2 * g from by ring_nat]
          exact sub_cancel_left (2 * J + 1)]
  | p + 1 => by
    rw [gam_step J p,
        show wprod (2 * (J + g) + 1) g
            * ((2 * J + 1) * ((2 * (J - p) - 1) * (2 * (J - p)) * nth (cListC J) p))
          = (2 * (J - p) - 1) * (2 * (J - p))
            * (wprod (2 * (J + g) + 1) g * ((2 * J + 1) * nth (cListC J) p)) from by
          ring_nat,
        wmatchB J g p,
        show p + 1 + g = (p + g) + 1 from Nat.succ_add p g,
        show wprod (2 * (J + g) + 1) ((p + g) + 1)
          = wprod (2 * (J + g) + 1) (p + g)
            * (((2 * (J + g) + 1) - 2 * (p + g) - 1)
              * ((2 * (J + g) + 1) - 2 * (p + g))) from rfl,
        show (2 * (J - p) - 1) * (2 * (J - p))
            * (wprod (2 * (J + g) + 1) (p + g) * ((2 * (J + g) + 1) - 2 * (p + g)))
          = wprod (2 * (J + g) + 1) (p + g)
            * ((2 * (J - p) - 1) * (2 * (J - p)) * ((2 * (J + g) + 1) - 2 * (p + g)))
          from by ring_nat,
        prod_match_B J p g,
        show p + 1 + g = (p + g) + 1 from Nat.succ_add p g]
    ring_nat

/-- ★★★★★ **BRIDGE A**: the `Mf(g)`-scaled convolution coefficient of
    `(rev A-stack) ⋆ (sinh list)` at `p` completes the `g`-headed accumulator
    to `p+g+1` steps — `N̂ = J+g` is invariant along the head-peel, and the
    weight match aligns each peel with the snoc. -/
theorem bridgeA (n J g : Nat) : ∀ p,
    wprod (2 * (J + g) + 1) g * nth (lmulC (truncA n (p + g)) (sListC J)) p
        + AaccSum n (J + g) g
      = AaccSum n (J + g) (p + g + 1)
  | 0 => by
    cases g with
    | zero =>
      show wprod (2 * (J + 0) + 1) 0 * nth (lmulC (truncA n 0) (sListC J)) 0
            + AaccSum n (J + 0) 0
          = AaccSum n (J + 0) 1
      rw [show truncA n 0 = [apF n 0] from rfl, nth_lmulC_zero, sListC_head J,
          AaccSum_snoc n (J + 0) 0,
          show wprod (2 * (J + 0) + 1) 0 = 1 from rfl]
      show 1 * (apF n 0 * 1) + AaccSum n (J + 0) 0
          = AaccSum n (J + 0) 0 + 1 * apF n 0
      ring_nat
    | succ g' =>
      show wprod (2 * (J + (g' + 1)) + 1) (g' + 1)
            * nth (lmulC (apF n (0 + (g' + 1)) :: truncA n (0 + g')) (sListC J)) 0
            + AaccSum n (J + (g' + 1)) (g' + 1)
          = AaccSum n (J + (g' + 1)) (0 + (g' + 1) + 1)
      rw [nth_lmulC_zero, sListC_head J, Nat.zero_add,
          AaccSum_snoc n (J + (g' + 1)) (g' + 1)]
      ring_nat
  | p + 1 => by
    rw [show p + 1 + g = (p + g) + 1 from Nat.succ_add p g,
        show truncA n ((p + g) + 1) = apF n ((p + g) + 1) :: truncA n (p + g) from rfl,
        nth_lmulC_succ,
        show wprod (2 * (J + g) + 1) g
            * (apF n ((p + g) + 1) * nth (sListC J) (p + 1)
              + nth (lmulC (truncA n (p + g)) (sListC J)) p)
          = wprod (2 * (J + g) + 1) g * nth (sListC J) (p + 1) * apF n ((p + g) + 1)
            + wprod (2 * (J + g) + 1) g
              * nth (lmulC (truncA n (p + g)) (sListC J)) p from by ring_nat,
        wmatchA J g (p + 1),
        show p + 1 + g = (p + g) + 1 from Nat.succ_add p g]
    rw [show wprod (2 * (J + g) + 1) ((p + g) + 1) * apF n ((p + g) + 1)
          + wprod (2 * (J + g) + 1) g * nth (lmulC (truncA n (p + g)) (sListC J)) p
          + AaccSum n (J + g) g
        = (wprod (2 * (J + g) + 1) g * nth (lmulC (truncA n (p + g)) (sListC J)) p
            + AaccSum n (J + g) g)
          + wprod (2 * (J + g) + 1) ((p + g) + 1) * apF n ((p + g) + 1) from by
          ring_nat,
        bridgeA n J g p,
        ← AaccSum_snoc n (J + g) ((p + g) + 1)]

/-- ★★★★★ **BRIDGE B** (the cosh side, with the `(2J+1)`-laden list). -/
theorem bridgeB (n J g : Nat) : ∀ p,
    wprod (2 * (J + g) + 1) g
        * nth (lmulC (truncB n (p + g)) (lsmul (2 * J + 1) (cListC J))) p
        + BaccSum n (J + g) g
      = BaccSum n (J + g) (p + g + 1)
  | 0 => by
    cases g with
    | zero =>
      show wprod (2 * (J + 0) + 1) 0
            * nth (lmulC (truncB n 0) (lsmul (2 * J + 1) (cListC J))) 0
            + BaccSum n (J + 0) 0
          = BaccSum n (J + 0) 1
      rw [show truncB n 0 = [bpF n 0] from rfl, nth_lmulC_zero, nth_lsmul,
          cListC_head J, BaccSum_snoc n (J + 0) 0,
          show wprod (2 * (J + 0) + 1) 0 = 1 from rfl,
          show (2 * (J + 0) + 1) - 2 * 0 = 2 * (J + 0) + 1 from Nat.sub_zero _]
      show 1 * (bpF n 0 * ((2 * J + 1) * 1)) + BaccSum n (J + 0) 0
          = BaccSum n (J + 0) 0 + 1 * ((2 * (J + 0) + 1) * bpF n 0)
      ring_nat
    | succ g' =>
      show wprod (2 * (J + (g' + 1)) + 1) (g' + 1)
            * nth (lmulC (bpF n (0 + (g' + 1)) :: truncB n (0 + g'))
                (lsmul (2 * J + 1) (cListC J))) 0
            + BaccSum n (J + (g' + 1)) (g' + 1)
          = BaccSum n (J + (g' + 1)) (0 + (g' + 1) + 1)
      rw [nth_lmulC_zero, nth_lsmul, Nat.zero_add,
          BaccSum_snoc n (J + (g' + 1)) (g' + 1)]
      have hw := wmatchB J (g' + 1) 0
      rw [cListC_head J, Nat.mul_one, Nat.zero_add] at hw
      rw [show wprod (2 * (J + (g' + 1)) + 1) (g' + 1)
            * (bpF n (g' + 1) * ((2 * J + 1) * nth (cListC J) 0))
          = wprod (2 * (J + (g' + 1)) + 1) (g' + 1) * (2 * J + 1)
            * bpF n (g' + 1) from by
            rw [cListC_head J]; ring_nat,
          hw]
      ring_nat
  | p + 1 => by
    rw [show p + 1 + g = (p + g) + 1 from Nat.succ_add p g,
        show truncB n ((p + g) + 1) = bpF n ((p + g) + 1) :: truncB n (p + g) from rfl,
        nth_lmulC_succ, nth_lsmul,
        show wprod (2 * (J + g) + 1) g
            * (bpF n ((p + g) + 1) * ((2 * J + 1) * nth (cListC J) (p + 1))
              + nth (lmulC (truncB n (p + g)) (lsmul (2 * J + 1) (cListC J))) p)
          = wprod (2 * (J + g) + 1) g * ((2 * J + 1) * nth (cListC J) (p + 1))
              * bpF n ((p + g) + 1)
            + wprod (2 * (J + g) + 1) g
              * nth (lmulC (truncB n (p + g)) (lsmul (2 * J + 1) (cListC J))) p
          from by ring_nat,
        wmatchB J g (p + 1),
        show p + 1 + g = (p + g) + 1 from Nat.succ_add p g]
    rw [show wprod (2 * (J + g) + 1) ((p + g) + 1)
            * ((2 * (J + g) + 1) - 2 * ((p + g) + 1)) * bpF n ((p + g) + 1)
          + wprod (2 * (J + g) + 1) g
            * nth (lmulC (truncB n (p + g)) (lsmul (2 * J + 1) (cListC J))) p
          + BaccSum n (J + g) g
        = (wprod (2 * (J + g) + 1) g
            * nth (lmulC (truncB n (p + g)) (lsmul (2 * J + 1) (cListC J))) p
            + BaccSum n (J + g) g)
          + wprod (2 * (J + g) + 1) ((p + g) + 1)
            * (((2 * (J + g) + 1) - 2 * ((p + g) + 1)) * bpF n ((p + g) + 1)) from by
          ring_nat,
        bridgeB n J g p,
        ← BaccSum_snoc n (J + g) ((p + g) + 1)]

/-! ## §8 — F4: the division-free budget -/

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMinor (bpF_halving)

private theorem le_sub_of_add_le {k a b : Nat} (h : b + k ≤ a) : k ≤ a - b := by
  obtain ⟨e, he⟩ := Nat.le.dest h
  rw [← he, show b + k + e = (k + e) + b from by ring_nat, sub_cancel_left (k + e)]
  exact Nat.le_add_right k e

theorem wprod_pos : ∀ (cc m : Nat), 2 * m + 1 ≤ cc → 1 ≤ wprod cc m
  | _, 0, _ => Nat.le_refl 1
  | cc, m + 1, h => by
    show 1 ≤ wprod cc m * ((cc - 2 * m - 1) * (cc - 2 * m))
    obtain ⟨e, he⟩ := Nat.le.dest h
    have hyp' : 2 * m + 1 ≤ cc := by
      rw [← he, show 2 * (m + 1) + 1 + e = (2 * m + 1) + (e + 2) from by ring_nat]
      exact Nat.le_add_right _ _
    have hsub : cc - 2 * m = e + 3 := by
      rw [← he, show 2 * (m + 1) + 1 + e = (e + 3) + 2 * m from by ring_nat,
          sub_cancel_left (e + 3)]
    have h1 : 1 ≤ cc - 2 * m - 1 := by
      rw [hsub, show e + 3 = (e + 2) + 1 from rfl, sub_cancel_left (e + 2)]
      exact Nat.succ_le_succ (Nat.zero_le _)
    have h2 : 1 ≤ cc - 2 * m := by
      rw [hsub]; exact Nat.succ_le_succ (Nat.zero_le _)
    calc 1 = 1 * (1 * 1) := rfl
      _ ≤ wprod cc m * ((cc - 2 * m - 1) * (cc - 2 * m)) :=
          Nat.mul_le_mul (wprod_pos cc m hyp') (Nat.mul_le_mul h1 h2)

/-- ★★★★ **The state-general budget**: along the accumulator the head coefficient
    stays below the threaded weight by at least the `(2J+2)`-factor, so —
    with halving — the whole `Bacc` is bounded by `2·(head value)·(final
    weight)`, division-free. -/
theorem budgetGen (n J : Nat) : ∀ (steps cc w s : Nat),
    2 * J + 1 + 2 * steps ≤ cc →
    (2 * J + 2) * Bacc n cc w s steps ≤ w * wprod cc steps * (2 * bpF n s)
  | 0, _, w, s, _ => by
    show (2 * J + 2) * 0 ≤ w * 1 * (2 * bpF n s)
    rw [Nat.mul_zero]
    exact Nat.zero_le _
  | steps + 1, cc, w, s, h => by
    have hyp' : 2 * J + 1 + 2 * steps ≤ cc - 2 := le_sub_of_add_le (by
      rw [show 2 + (2 * J + 1 + 2 * steps) = 2 * J + 1 + 2 * (steps + 1) from by
            ring_nat]
      exact h)
    have ih := budgetGen n J steps (cc - 2) (w * (cc - 1) * cc) (s + 1) hyp'
    have hhalf : 2 * bpF n (s + 1) ≤ bpF n s := bpF_halving n s
    have hccbig : 2 * J + 3 ≤ cc := Nat.le_trans (by
      rw [show 2 * J + 1 + 2 * (steps + 1) = (2 * J + 3) + 2 * steps from by ring_nat]
      exact Nat.le_add_right _ _) h
    have hcc1 : 2 * J + 2 ≤ cc - 1 := le_sub_of_add_le (by
      rw [Nat.add_comm 1 (2 * J + 2)]
      exact hccbig)
    have hW : 1 ≤ wprod (cc - 2) steps :=
      wprod_pos (cc - 2) steps (Nat.le_trans (by
        rw [show 2 * J + 1 + 2 * steps = (2 * steps + 1) + 2 * J from by ring_nat]
        exact Nat.le_add_right _ _) hyp')
    show (2 * J + 2) * (w * cc * bpF n s
          + Bacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) steps)
        ≤ w * wprod cc (steps + 1) * (2 * bpF n s)
    rw [wprod_shift cc steps]
    calc (2 * J + 2) * (w * cc * bpF n s
          + Bacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) steps)
        = (2 * J + 2) * (w * cc * bpF n s)
          + (2 * J + 2) * Bacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) steps := by
          ring_nat
      _ ≤ (2 * J + 2) * (w * cc * bpF n s)
          + w * (cc - 1) * cc * wprod (cc - 2) steps * (2 * bpF n (s + 1)) :=
          Nat.add_le_add_left ih _
      _ ≤ (2 * J + 2) * (w * cc * bpF n s)
          + w * (cc - 1) * cc * wprod (cc - 2) steps * bpF n s :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ hhalf) _
      _ ≤ (cc - 1) * (w * cc * bpF n s) * wprod (cc - 2) steps
          + w * (cc - 1) * cc * wprod (cc - 2) steps * bpF n s := by
          refine Nat.add_le_add_right ?_ _
          calc (2 * J + 2) * (w * cc * bpF n s)
              ≤ (cc - 1) * (w * cc * bpF n s) :=
                Nat.mul_le_mul_right _ hcc1
            _ = (cc - 1) * (w * cc * bpF n s) * 1 := (Nat.mul_one _).symm
            _ ≤ (cc - 1) * (w * cc * bpF n s) * wprod (cc - 2) steps :=
                Nat.mul_le_mul_left _ hW
      _ = w * ((cc - 1) * cc * wprod (cc - 2) steps) * (2 * bpF n s) := by ring_nat

/-! ## §9 — F5 stabilization: the accumulators saturate at their support

For `n = 2i+1` the coefficient support ends at `s = i` (the `AP/BP` lengths),
and the weight `wprod (2N+1)` vanishes from step `N+1`; so `i+1` accumulator
steps already give the full `Asum/Bsum` — for **every** `N`. -/

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMasterId
  (Asum Bsum cfpos descFac descFac_vanish cfpos_one master_odd master_diagonal)

theorem apF_vanish_ge (i j : Nat) : apF (2 * i + 1) (i + 1 + j) = 0 := by
  rw [← AP_nth (2 * i + 1) (i + 1 + j)]
  exact nth_ge_len _ _ (by
    rw [(E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.AP_BP_length i).1]
    exact Nat.le_add_right _ _)

theorem bpF_vanish_ge (i j : Nat) : bpF (2 * i + 1) (i + 1 + j) = 0 := by
  rw [← BP_nth (2 * i + 1) (i + 1 + j)]
  exact nth_ge_len _ _ (by
    rw [(E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.AP_BP_length i).2.2.1]
    exact Nat.le_add_right _ _)

theorem wprod_vanish (N : Nat) : ∀ j, wprod (2 * N + 1) (N + 1 + j) = 0
  | 0 => by
    show wprod (2 * N + 1) N * ((2 * N + 1 - 2 * N - 1) * (2 * N + 1 - 2 * N)) = 0
    rw [show 2 * N + 1 = 1 + 2 * N from by ring_nat, sub_cancel_left 1]
    rfl
  | j + 1 => by
    show wprod (2 * N + 1) (N + 1 + j)
        * ((2 * N + 1 - 2 * (N + 1 + j) - 1) * (2 * N + 1 - 2 * (N + 1 + j))) = 0
    rw [wprod_vanish N j, Nat.zero_mul]

theorem AaccSum_stable (i N : Nat) : ∀ j,
    AaccSum (2 * i + 1) N (i + 1 + j) = AaccSum (2 * i + 1) N (i + 1)
  | 0 => rfl
  | j + 1 => by
    show AaccSum (2 * i + 1) N (i + 1 + j + 1) = AaccSum (2 * i + 1) N (i + 1)
    rw [AaccSum_snoc (2 * i + 1) N (i + 1 + j), apF_vanish_ge i j, Nat.mul_zero,
        Nat.add_zero, AaccSum_stable i N j]

theorem AaccSum_stable_w (n N : Nat) : ∀ j,
    AaccSum n N (N + 1 + j) = AaccSum n N (N + 1)
  | 0 => rfl
  | j + 1 => by
    show AaccSum n N (N + 1 + j + 1) = AaccSum n N (N + 1)
    rw [AaccSum_snoc n N (N + 1 + j), wprod_vanish N j, Nat.zero_mul,
        Nat.add_zero, AaccSum_stable_w n N j]

theorem BaccSum_stable (i N : Nat) : ∀ j,
    BaccSum (2 * i + 1) N (i + 1 + j) = BaccSum (2 * i + 1) N (i + 1)
  | 0 => rfl
  | j + 1 => by
    show BaccSum (2 * i + 1) N (i + 1 + j + 1) = BaccSum (2 * i + 1) N (i + 1)
    rw [BaccSum_snoc (2 * i + 1) N (i + 1 + j), bpF_vanish_ge i j, Nat.mul_zero,
        Nat.mul_zero, Nat.add_zero, BaccSum_stable i N j]

theorem BaccSum_stable_w (n N : Nat) : ∀ j,
    BaccSum n N (N + 1 + j) = BaccSum n N (N + 1)
  | 0 => rfl
  | j + 1 => by
    show BaccSum n N (N + 1 + j + 1) = BaccSum n N (N + 1)
    rw [BaccSum_snoc n N (N + 1 + j), wprod_vanish N j, Nat.zero_mul,
        Nat.add_zero, BaccSum_stable_w n N j]

/-- ★★★ **`A`-saturation**: `i+1` steps already give the whole `Asum` —
    for every `N` (support or weight vanishes, whichever comes first). -/
theorem AaccSum_eq_Asum (i N : Nat) :
    AaccSum (2 * i + 1) N (i + 1) = Asum (2 * i + 1) N := by
  show AaccSum (2 * i + 1) N (i + 1) = AaccSum (2 * i + 1) N (N + 1)
  rcases Nat.lt_or_ge N i with h | h
  · obtain ⟨e, he⟩ := Nat.le.dest h
    rw [show i + 1 = N + 1 + (e + 1) from congrArg (· + 1) he.symm,
        AaccSum_stable_w (2 * i + 1) N (e + 1)]
  · obtain ⟨d, hd⟩ := Nat.le.dest h
    rw [show N + 1 = i + 1 + d from
          (congrArg (· + 1) hd.symm).trans (Nat.succ_add i d).symm,
        AaccSum_stable i N d]

/-- ★★★ **`B`-saturation** (twin). -/
theorem BaccSum_eq_Bsum (i N : Nat) :
    BaccSum (2 * i + 1) N (i + 1) = Bsum (2 * i + 1) N := by
  show BaccSum (2 * i + 1) N (i + 1) = BaccSum (2 * i + 1) N (N + 1)
  rcases Nat.lt_or_ge N i with h | h
  · obtain ⟨e, he⟩ := Nat.le.dest h
    rw [show i + 1 = N + 1 + (e + 1) from congrArg (· + 1) he.symm,
        BaccSum_stable_w (2 * i + 1) N (e + 1)]
  · obtain ⟨d, hd⟩ := Nat.le.dest h
    rw [show N + 1 = i + 1 + d from
          (congrArg (· + 1) hd.symm).trans (Nat.succ_add i d).symm,
        BaccSum_stable i N d]

/-! ## §10 — F5 mirrors: beyond the stack the convolution reads the accumulators

For index `r + m` (shift `r` past the full stack `truncA n m`) the convolution
coefficient is `wprod (2J+1) r · (saturated accumulator at level J − r)` —
the σ/γ lists are pure `wprod` weights, and `wprod` splits multiplicatively. -/

theorem sig_eq_wprod : ∀ (J t : Nat), nth (sListC J) t = wprod (2 * J + 1) t
  | J, 0 => sListC_head J
  | J, t + 1 => by
    rw [sig_step J t, sig_eq_wprod J t]
    have hf : (2 * (J - t)) * (2 * (J - t) + 1)
        = ((2 * J + 1) - 2 * t - 1) * ((2 * J + 1) - 2 * t) := prod_match J t 0
    rw [hf]
    show ((2 * J + 1) - 2 * t - 1) * ((2 * J + 1) - 2 * t) * wprod (2 * J + 1) t
        = wprod (2 * J + 1) t * ((2 * J + 1 - 2 * t - 1) * (2 * J + 1 - 2 * t))
    ring_nat

/-- The γ-side match: γ-step factor = (`wprod`-step factor) ÷ old coefficient ×
    new coefficient, division-free (both regimes vanish together past `J`). -/
theorem gam_match (J t : Nat) :
    (2 * (J - t) - 1) * (2 * (J - t))
      = ((2 * J + 1) - 2 * t - 1) * ((2 * J + 1) - 2 * (t + 1)) := by
  rcases Nat.lt_or_ge J t with hlt | hge
  · obtain ⟨e, he⟩ := Nat.le.dest hlt
    have hJt : J - t = 0 := by
      rw [← he, show J + 1 + e = J + (1 + e) from by ring_nat]
      exact sub_vanish J (1 + e)
    have h1 : (2 * J + 1) - 2 * t - 1 = 0 := by
      rw [← he,
          show 2 * (J + 1 + e) = (2 * J + 1) + (2 * e + 1) from by ring_nat,
          sub_vanish (2 * J + 1) (2 * e + 1)]
    rw [hJt, h1, Nat.zero_mul, Nat.zero_mul]
  · obtain ⟨d, hd⟩ := Nat.le.dest hge
    rw [← hd,
        show t + d - t = d from by
          rw [Nat.add_comm t d]; exact sub_cancel_left d,
        show (2 * (t + d) + 1) - 2 * t = 2 * d + 1 from by
          rw [show 2 * (t + d) + 1 = (2 * d + 1) + 2 * t from by ring_nat]
          exact sub_cancel_left (2 * d + 1)]
    cases d with
    | zero =>
      rw [show (2 * (t + 0) + 1) - 2 * (t + 1) = 0 from by
            rw [show 2 * (t + 1) = (2 * (t + 0) + 1) + 1 from by ring_nat]
            exact sub_vanish _ 1,
          Nat.mul_zero]
    | succ d' =>
      rw [show (2 * (t + (d' + 1)) + 1) - 2 * (t + 1) = 2 * d' + 1 from by
            rw [show 2 * (t + (d' + 1)) + 1 = (2 * d' + 1) + 2 * (t + 1) from by
                  ring_nat]
            exact sub_cancel_left (2 * d' + 1),
          show 2 * (d' + 1) - 1 = 2 * d' + 1 from rfl,
          show 2 * (d' + 1) + 1 - 1 = 2 * (d' + 1) from rfl]
      ring_nat

theorem gam_eq : ∀ (J t : Nat),
    (2 * J + 1) * nth (cListC J) t = wprod (2 * J + 1) t * ((2 * J + 1) - 2 * t)
  | J, 0 => by
    rw [cListC_head J]
    show (2 * J + 1) * 1 = 1 * ((2 * J + 1) - 2 * 0)
    rw [show (2 * J + 1) - 2 * 0 = 2 * J + 1 from rfl, Nat.mul_one, Nat.one_mul]
  | J, t + 1 => by
    rw [gam_step J t,
        show (2 * J + 1) * ((2 * (J - t) - 1) * (2 * (J - t)) * nth (cListC J) t)
          = (2 * (J - t) - 1) * (2 * (J - t))
            * ((2 * J + 1) * nth (cListC J) t) from by ring_nat,
        gam_eq J t, gam_match J t]
    show ((2 * J + 1) - 2 * t - 1) * ((2 * J + 1) - 2 * (t + 1))
          * (wprod (2 * J + 1) t * ((2 * J + 1) - 2 * t))
        = wprod (2 * J + 1) t * ((2 * J + 1 - 2 * t - 1) * (2 * J + 1 - 2 * t))
          * ((2 * J + 1) - 2 * (t + 1))
    ring_nat

theorem wprod_split (K r : Nat) : ∀ s,
    wprod (2 * (K + r) + 1) (r + s)
      = wprod (2 * (K + r) + 1) r * wprod (2 * K + 1) s
  | 0 => by
    show wprod (2 * (K + r) + 1) r = wprod (2 * (K + r) + 1) r * 1
    rw [Nat.mul_one]
  | s + 1 => by
    show wprod (2 * (K + r) + 1) (r + s)
          * ((2 * (K + r) + 1 - 2 * (r + s) - 1) * (2 * (K + r) + 1 - 2 * (r + s)))
        = wprod (2 * (K + r) + 1) r
          * (wprod (2 * K + 1) s * ((2 * K + 1 - 2 * s - 1) * (2 * K + 1 - 2 * s)))
    have hf : (2 * (K + r) + 1 - 2 * (r + s) - 1) * (2 * (K + r) + 1 - 2 * (r + s))
        = (2 * K + 1 - 2 * s - 1) * (2 * K + 1 - 2 * s) := by
      rw [show r + s = s + r from Nat.add_comm r s, ← prod_match K s r]
      exact prod_match K s 0
    rw [wprod_split K r s, hf]
    ring_nat

private theorem sub_shift (K r s : Nat) :
    (2 * (K + r) + 1) - 2 * (r + s) = (2 * K + 1) - 2 * s := by
  rcases Nat.lt_or_ge K s with hlt | hge
  · obtain ⟨e, he⟩ := Nat.le.dest hlt
    rw [← he,
        show 2 * (r + (K + 1 + e)) = (2 * (K + r) + 1) + (2 * e + 1) from by ring_nat,
        sub_vanish (2 * (K + r) + 1) (2 * e + 1),
        show 2 * (K + 1 + e) = (2 * K + 1) + (2 * e + 1) from by ring_nat,
        sub_vanish (2 * K + 1) (2 * e + 1)]
  · obtain ⟨d, hd⟩ := Nat.le.dest hge
    rw [← hd,
        show 2 * ((s + d) + r) + 1 = (2 * d + 1) + 2 * (r + s) from by ring_nat,
        sub_cancel_left (2 * d + 1),
        show 2 * (s + d) + 1 = (2 * d + 1) + 2 * s from by ring_nat,
        sub_cancel_left (2 * d + 1)]

/-- ★★★★ **Mirror bridge A**: at shift `r` past the full stack, the convolution
    coefficient is the `wprod`-weighted saturating accumulator at level `K`. -/
theorem mirrorA (n K r : Nat) : ∀ m,
    nth (lmulC (truncA n m) (sListC (K + r))) (r + m)
      = wprod (2 * (K + r) + 1) r * AaccSum n K (m + 1)
  | 0 => by
    cases r with
    | zero =>
      show nth (lmulC (apF n 0 :: []) (sListC K)) 0
          = wprod (2 * K + 1) 0 * AaccSum n K 1
      rw [nth_lmulC_zero, sListC_head, AaccSum_snoc n K 0]
      show apF n 0 * 1
          = 1 * (AaccSum n K 0 + wprod (2 * K + 1) 0 * apF n 0)
      rw [show AaccSum n K 0 = 0 from rfl, show wprod (2 * K + 1) 0 = 1 from rfl,
          Nat.mul_one, Nat.one_mul, Nat.zero_add, Nat.one_mul]
    | succ r' =>
      show nth (lmulC (apF n 0 :: []) (sListC (K + (r' + 1)))) (r' + 1)
          = wprod (2 * (K + (r' + 1)) + 1) (r' + 1) * AaccSum n K 1
      rw [nth_lmulC_succ,
          show nth (lmulC ([] : List Nat) (sListC (K + (r' + 1)))) r' = 0 from rfl,
          Nat.add_zero, sig_eq_wprod (K + (r' + 1)) (r' + 1), AaccSum_snoc n K 0,
          show AaccSum n K 0 = 0 from rfl, show wprod (2 * K + 1) 0 = 1 from rfl,
          Nat.zero_add, Nat.one_mul]
      ring_nat
  | m + 1 => by
    show nth (lmulC (apF n (m + 1) :: truncA n m) (sListC (K + r))) ((r + m) + 1)
        = wprod (2 * (K + r) + 1) r * AaccSum n K (m + 1 + 1)
    rw [nth_lmulC_succ, mirrorA n K r m, sig_eq_wprod (K + r) ((r + m) + 1),
        show (r + m) + 1 = r + (m + 1) from rfl, wprod_split K r (m + 1),
        AaccSum_snoc n K (m + 1)]
    ring_nat

/-- ★★★★ **Mirror bridge B** (the cosh side, `(2J+1)`-laden). -/
theorem mirrorB (n K r : Nat) : ∀ m,
    nth (lmulC (truncB n m) (lsmul (2 * (K + r) + 1) (cListC (K + r)))) (r + m)
      = wprod (2 * (K + r) + 1) r * BaccSum n K (m + 1)
  | 0 => by
    cases r with
    | zero =>
      show nth (lmulC (bpF n 0 :: []) (lsmul (2 * K + 1) (cListC K))) 0
          = wprod (2 * K + 1) 0 * BaccSum n K 1
      rw [nth_lmulC_zero, nth_lsmul, cListC_head, BaccSum_snoc n K 0]
      show bpF n 0 * ((2 * K + 1) * 1)
          = 1 * (BaccSum n K 0
              + wprod (2 * K + 1) 0 * ((2 * K + 1 - 2 * 0) * bpF n 0))
      rw [show BaccSum n K 0 = 0 from rfl, show wprod (2 * K + 1) 0 = 1 from rfl,
          show 2 * K + 1 - 2 * 0 = 2 * K + 1 from rfl,
          Nat.mul_one, Nat.one_mul, Nat.zero_add, Nat.one_mul]
      exact Nat.mul_comm _ _
    | succ r' =>
      show nth (lmulC (bpF n 0 :: [])
              (lsmul (2 * (K + (r' + 1)) + 1) (cListC (K + (r' + 1))))) (r' + 1)
          = wprod (2 * (K + (r' + 1)) + 1) (r' + 1) * BaccSum n K 1
      rw [nth_lmulC_succ, nth_lsmul,
          show nth (lmulC ([] : List Nat)
              (lsmul (2 * (K + (r' + 1)) + 1) (cListC (K + (r' + 1))))) r' = 0
            from rfl,
          Nat.add_zero, gam_eq (K + (r' + 1)) (r' + 1),
          show (2 * (K + (r' + 1)) + 1) - 2 * (r' + 1) = (2 * K + 1) - 2 * 0 from
            sub_shift K (r' + 1) 0,
          BaccSum_snoc n K 0,
          show BaccSum n K 0 = 0 from rfl, show wprod (2 * K + 1) 0 = 1 from rfl,
          Nat.zero_add, Nat.one_mul]
      ring_nat
  | m + 1 => by
    show nth (lmulC (bpF n (m + 1) :: truncB n m)
            (lsmul (2 * (K + r) + 1) (cListC (K + r)))) ((r + m) + 1)
        = wprod (2 * (K + r) + 1) r * BaccSum n K (m + 1 + 1)
    rw [nth_lmulC_succ, nth_lsmul, mirrorB n K r m, gam_eq (K + r) ((r + m) + 1),
        show (r + m) + 1 = r + (m + 1) from rfl, wprod_split K r (m + 1),
        sub_shift K r (m + 1), BaccSum_snoc n K (m + 1)]
    ring_nat

/-! ## §11 — F5 per-coefficient laws of the two `LowerBase` convolution lists

`LAl i = (rev A-stack) ⋆ (sinh list)`, `LBl i = (rev B-stack) ⋆ ((2J+1)·cosh)`
at the matched level `J = n = 2i+1`.  Entry-by-entry: equal past the diagonal
(`entry_eq`), flipped by exactly `cfpos n n` at it (`diag`), and below it the
`(2n+2)`-scaled `A` entry exceeds `B`'s by at most `2·bpF n 0` (`slack`). -/

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld (lsmul_length)

theorem truncA_len (n : Nat) : ∀ m, (truncA n m).length = m + 1
  | 0 => rfl
  | m + 1 => congrArg (· + 1) (truncA_len n m)

theorem truncB_len (n : Nat) : ∀ m, (truncB n m).length = m + 1
  | 0 => rfl
  | m + 1 => congrArg (· + 1) (truncB_len n m)

theorem sListC_len : ∀ J, (sListC J).length = J + 1
  | 0 => rfl
  | J + 1 => by
    show (lsmul ((2 * J + 2) * (2 * J + 3)) (sListC J)).length + 1 = (J + 1) + 1
    rw [lsmul_length, sListC_len J]

theorem cListC_len : ∀ J, (cListC J).length = J + 1
  | 0 => rfl
  | J + 1 => by
    show (lsmul ((2 * J + 1) * (2 * J + 2)) (cListC J)).length + 1 = (J + 1) + 1
    rw [lsmul_length, cListC_len J]

theorem ladd_length_le : ∀ (a b : List Nat), a.length ≤ b.length →
    (ladd a b).length = b.length
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (Nat.not_succ_le_zero _)
  | _ :: as, _ :: bs, h => by
    show (ladd as bs).length + 1 = bs.length + 1
    rw [ladd_length_le as bs (Nat.le_of_succ_le_succ h)]

theorem ladd_length_ge : ∀ (a b : List Nat), b.length ≤ a.length →
    (ladd a b).length = a.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: _, [], _ => rfl
  | _ :: as, _ :: bs, h => by
    show (ladd as bs).length + 1 = as.length + 1
    rw [ladd_length_ge as bs (Nat.le_of_succ_le_succ h)]

theorem lmulC_len : ∀ (as : List Nat) (a₀ : Nat) (b : List Nat), 1 ≤ b.length →
    (lmulC (a₀ :: as) b).length = as.length + b.length
  | [], a₀, b, hb => by
    show (ladd (lsmul a₀ b) (0 :: lmulC [] b)).length = List.length [] + b.length
    rw [show lmulC ([] : List Nat) b = [] from rfl,
        ladd_length_ge (lsmul a₀ b) [0] (by
          show 1 ≤ (lsmul a₀ b).length
          rw [lsmul_length]
          exact hb),
        lsmul_length]
    show b.length = 0 + b.length
    rw [Nat.zero_add]
  | a₁ :: as, a₀, b, hb => by
    show (ladd (lsmul a₀ b) (0 :: lmulC (a₁ :: as) b)).length
        = (as.length + 1) + b.length
    rw [ladd_length_le (lsmul a₀ b) (0 :: lmulC (a₁ :: as) b) (by
          show (lsmul a₀ b).length ≤ (lmulC (a₁ :: as) b).length + 1
          rw [lsmul_length, lmulC_len as a₁ b hb]
          exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))]
    show (lmulC (a₁ :: as) b).length + 1 = (as.length + 1) + b.length
    rw [lmulC_len as a₁ b hb]
    ring_nat

/-- The `LowerBase` left list at level `i`: `(rev A-stack) ⋆ (sinh list)`. -/
def LAl (i : Nat) : List Nat := lmulC (truncA (2 * i + 1) i) (sListC (2 * i + 1))

/-- The `LowerBase` right list: `(rev B-stack) ⋆ ((2J+1)·cosh list)`. -/
def LBl (i : Nat) : List Nat :=
  lmulC (truncB (2 * i + 1) i) (lsmul (2 * (2 * i + 1) + 1) (cListC (2 * i + 1)))

theorem LAl_len (i : Nat) : (LAl i).length = 3 * i + 2 := by
  show (lmulC (truncA (2 * i + 1) i) (sListC (2 * i + 1))).length = 3 * i + 2
  cases i with
  | zero =>
    show (lmulC (apF 1 0 :: []) (sListC 1)).length = 2
    rw [lmulC_len [] (apF 1 0) (sListC 1) (by
          rw [sListC_len]
          exact Nat.succ_le_succ (Nat.zero_le _)),
        sListC_len]
    rfl
  | succ i' =>
    show (lmulC (apF (2 * (i' + 1) + 1) (i' + 1) :: truncA (2 * (i' + 1) + 1) i')
            (sListC (2 * (i' + 1) + 1))).length = 3 * (i' + 1) + 2
    rw [lmulC_len (truncA (2 * (i' + 1) + 1) i') _ _ (by
          rw [sListC_len]
          exact Nat.succ_le_succ (Nat.zero_le _)),
        truncA_len, sListC_len]
    ring_nat

theorem LBl_len (i : Nat) : (LBl i).length = 3 * i + 2 := by
  show (lmulC (truncB (2 * i + 1) i)
        (lsmul (2 * (2 * i + 1) + 1) (cListC (2 * i + 1)))).length = 3 * i + 2
  cases i with
  | zero =>
    show (lmulC (bpF 1 0 :: []) (lsmul 3 (cListC 1))).length = 2
    rw [lmulC_len [] (bpF 1 0) (lsmul 3 (cListC 1)) (by
          rw [lsmul_length, cListC_len]
          exact Nat.succ_le_succ (Nat.zero_le _)),
        lsmul_length, cListC_len]
    rfl
  | succ i' =>
    show (lmulC (bpF (2 * (i' + 1) + 1) (i' + 1) :: truncB (2 * (i' + 1) + 1) i')
            (lsmul (2 * (2 * (i' + 1) + 1) + 1) (cListC (2 * (i' + 1) + 1)))).length
        = 3 * (i' + 1) + 2
    rw [lmulC_len (truncB (2 * (i' + 1) + 1) i') _ _ (by
          rw [lsmul_length, cListC_len]
          exact Nat.succ_le_succ (Nat.zero_le _)),
        truncB_len, lsmul_length, cListC_len]
    ring_nat

/-- ★★★ Past the diagonal the two lists agree entry-by-entry: the mirrors read
    saturated accumulators at level `K < n`, where `cfpos (2i+1) K = 0` and the
    master identity is an **equality**. -/
theorem entry_eq (i e : Nat) : nth (LAl i) (i + 1 + e) = nth (LBl i) (i + 1 + e) := by
  rcases Nat.lt_or_ge e (2 * i + 1) with hlt | hge
  · have he' : e ≤ 2 * i := Nat.le_of_lt_succ hlt
    obtain ⟨c, hc⟩ := Nat.le.dest he'
    have hKr : c + (e + 1) = 2 * i + 1 := by
      rw [show c + (e + 1) = (e + c) + 1 from by ring_nat, hc]
    have hA : nth (lmulC (truncA (2 * i + 1) i) (sListC (2 * i + 1))) ((e + 1) + i)
        = wprod (2 * (2 * i + 1) + 1) (e + 1) * AaccSum (2 * i + 1) c (i + 1) := by
      have h := mirrorA (2 * i + 1) c (e + 1) i
      rw [hKr] at h
      exact h
    have hB : nth (lmulC (truncB (2 * i + 1) i)
            (lsmul (2 * (2 * i + 1) + 1) (cListC (2 * i + 1)))) ((e + 1) + i)
        = wprod (2 * (2 * i + 1) + 1) (e + 1) * BaccSum (2 * i + 1) c (i + 1) := by
      have h := mirrorB (2 * i + 1) c (e + 1) i
      rw [hKr] at h
      exact h
    rw [show lmulC (truncA (2 * i + 1) i) (sListC (2 * i + 1)) = LAl i from rfl] at hA
    rw [show lmulC (truncB (2 * i + 1) i)
          (lsmul (2 * (2 * i + 1) + 1) (cListC (2 * i + 1))) = LBl i from rfl] at hB
    have hcf : cfpos (2 * i + 1) c = 0 := by
      show 2 ^ (2 * i + 1) * descFac c (2 * i + 1) = 0
      rw [descFac_vanish c (2 * i + 1) (Nat.lt_succ_of_le (by
            rw [← hc]; exact Nat.le_add_left c e)),
          Nat.mul_zero]
    have hAB : AaccSum (2 * i + 1) c (i + 1) = BaccSum (2 * i + 1) c (i + 1) := by
      rw [AaccSum_eq_Asum i c, BaccSum_eq_Bsum i c]
      have h := master_odd i c
      rw [hcf, Nat.add_zero] at h
      exact h
    rw [show i + 1 + e = (e + 1) + i from by ring_nat, hA, hB, hAB]
  · obtain ⟨f, hf⟩ := Nat.le.dest hge
    have hlen : 3 * i + 2 ≤ i + 1 + e := by
      rw [← hf, show i + 1 + (2 * i + 1 + f) = (3 * i + 2) + f from by ring_nat]
      exact Nat.le_add_right _ _
    rw [nth_ge_len (LAl i) (i + 1 + e) (by rw [LAl_len]; exact hlen),
        nth_ge_len (LBl i) (i + 1 + e) (by rw [LBl_len]; exact hlen)]

/-- ★★★★ **The diagonal flip**: at `p = i` the `B` side exceeds the `A` side by
    exactly `cfpos n n = (4i+2)!!` — the master identity's Padé remainder. -/
theorem diag (i : Nat) :
    nth (LBl i) i = nth (LAl i) i + cfpos (2 * i + 1) (2 * i + 1) := by
  have hA : 1 * nth (LAl i) i + AaccSum (2 * i + 1) (2 * i + 1) 0
      = AaccSum (2 * i + 1) (2 * i + 1) (i + 1) :=
    bridgeA (2 * i + 1) (2 * i + 1) 0 i
  have hB : 1 * nth (LBl i) i + BaccSum (2 * i + 1) (2 * i + 1) 0
      = BaccSum (2 * i + 1) (2 * i + 1) (i + 1) :=
    bridgeB (2 * i + 1) (2 * i + 1) 0 i
  rw [Nat.one_mul, show AaccSum (2 * i + 1) (2 * i + 1) 0 = 0 from rfl,
      Nat.add_zero, AaccSum_eq_Asum i (2 * i + 1)] at hA
  rw [Nat.one_mul, show BaccSum (2 * i + 1) (2 * i + 1) 0 = 0 from rfl,
      Nat.add_zero, BaccSum_eq_Bsum i (2 * i + 1)] at hB
  rw [hA, hB]
  exact master_diagonal i

/-- ★★★★ **The uniform sub-diagonal slack**: below the diagonal, after scaling
    by `2n+2 = 4i+4`, the `A` entry exceeds the `B` entry by at most
    `2·bpF n 0` — the budget pays the gap out of the threaded weight, and the
    weight cancels (division-free). -/
theorem slack (i p g : Nat) (hpg : p + (g + 1) = i) :
    (2 * (2 * i + 1) + 2) * nth (LAl i) p
      ≤ (2 * (2 * i + 1) + 2) * nth (LBl i) p + 2 * bpF (2 * i + 1) 0 := by
  have hA := bridgeA (2 * i + 1) (2 * i + 1) (g + 1) p
  have hB := bridgeB (2 * i + 1) (2 * i + 1) (g + 1) p
  rw [hpg] at hA hB
  rw [show lmulC (truncA (2 * i + 1) i) (sListC (2 * i + 1)) = LAl i from rfl,
      AaccSum_eq_Asum i ((2 * i + 1) + (g + 1))] at hA
  rw [show lmulC (truncB (2 * i + 1) i)
        (lsmul (2 * (2 * i + 1) + 1) (cListC (2 * i + 1))) = LBl i from rfl,
      BaccSum_eq_Bsum i ((2 * i + 1) + (g + 1))] at hB
  have hM := master_odd i ((2 * i + 1) + (g + 1))
  have hEq : wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1) * nth (LAl i) p
        + AaccSum (2 * i + 1) ((2 * i + 1) + (g + 1)) (g + 1)
        + cfpos (2 * i + 1) ((2 * i + 1) + (g + 1))
      = wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1) * nth (LBl i) p
        + BaccSum (2 * i + 1) ((2 * i + 1) + (g + 1)) (g + 1) := by
    rw [hA, hB, hM]
  have hyp : 2 * (2 * i + 1) + 1 + 2 * (g + 1) ≤ 2 * ((2 * i + 1) + (g + 1)) + 1 :=
    Nat.le_of_eq (by ring_nat)
  have hBud := budgetGen (2 * i + 1) (2 * i + 1) (g + 1)
    (2 * ((2 * i + 1) + (g + 1)) + 1) 1 0 hyp
  rw [Nat.one_mul] at hBud
  have hMf : 1 ≤ wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1) :=
    wprod_pos _ _ (by
      rw [show 2 * ((2 * i + 1) + (g + 1)) + 1
            = (2 * (g + 1) + 1) + 2 * (2 * i + 1) from by ring_nat]
      exact Nat.le_add_right _ _)
  have main : wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1)
        * ((2 * (2 * i + 1) + 2) * nth (LAl i) p)
      ≤ wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1)
        * ((2 * (2 * i + 1) + 2) * nth (LBl i) p + 2 * bpF (2 * i + 1) 0) := by
    calc wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1)
          * ((2 * (2 * i + 1) + 2) * nth (LAl i) p)
        = (2 * (2 * i + 1) + 2)
            * (wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1) * nth (LAl i) p) := by
          ring_nat
      _ ≤ (2 * (2 * i + 1) + 2)
            * (wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1) * nth (LAl i) p
              + AaccSum (2 * i + 1) ((2 * i + 1) + (g + 1)) (g + 1)
              + cfpos (2 * i + 1) ((2 * i + 1) + (g + 1))) :=
          Nat.mul_le_mul_left _
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      _ = (2 * (2 * i + 1) + 2)
            * (wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1) * nth (LBl i) p
              + BaccSum (2 * i + 1) ((2 * i + 1) + (g + 1)) (g + 1)) := by
          rw [hEq]
      _ = (2 * (2 * i + 1) + 2)
            * (wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1) * nth (LBl i) p)
          + (2 * (2 * i + 1) + 2)
            * BaccSum (2 * i + 1) ((2 * i + 1) + (g + 1)) (g + 1) := by ring_nat
      _ ≤ (2 * (2 * i + 1) + 2)
            * (wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1) * nth (LBl i) p)
          + wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1)
            * (2 * bpF (2 * i + 1) 0) := Nat.add_le_add_left hBud _
      _ = wprod (2 * ((2 * i + 1) + (g + 1)) + 1) (g + 1)
            * ((2 * (2 * i + 1) + 2) * nth (LBl i) p + 2 * bpF (2 * i + 1) 0) := by
          ring_nat
  exact Nat.le_of_mul_le_mul_left main hMf

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertBridge
