import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.Real213.Sum.BoolOrLadder
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Real213.Core.CutPoset

/-!
# CutMulN: parametric-N cutMul

Multiplicative analog of `Sum.CutSumN`.  Generalises `cutMul`'s
fixed search to an N-aware product cut: takes two cuts at
denominator N and writes the product as a cut at denominator N²
(the natural fiber for `(a/N) · (c/N) = (a·c)/N²`).

## Definition

`cutMulN N cx cy m k` searches for witnesses `m1`, `m2` with
`cx m1 (N·k)` and `cy m2 (N·k)` and `m1·m2 ≤ N²·m·k`.  The rate
factor `N·k` and the slack factor `N²` on the product constraint
together implement the N-fiber multiplication closure.

## Key result

`cutMulN_same_denom`: for any `N > 0`, `a, c : Nat`,
  `cutMulN N (constCut a N) (constCut c N) ≡ constCut (a·c) (N²)`
bidirectionally (cutEq).  Both sides reduce to `a·c·k ≤ N²·m`
after dividing through.

For `N = 1` this is integer multiplication; for `N = 2` it is
dyadic; for `N = 3` it closes the `b = 3` case that motivated
the parametric framework on the additive side.

All declarations PURE.
-/

namespace E213.Lib.Math.Real213.Mul.CutMulN

open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Core.CutPoset (cutEq)

/-! ## §1 — Inner and outer ladders -/

/-- Inner ladder: iterate over `m2` from 0 to `n`, with `m1` fixed.
    The witness check uses rate factor `N·k` on both cuts and
    constraint `m1·m2 ≤ N²·m·k`. -/
def cutMulN_inner (N : Nat) (cx cy : Nat → Nat → Bool)
    (k m m1 : Nat) : Nat → Bool
  | 0     => cx m1 (N*k) && cy 0 (N*k) && decide (m1 * 0 ≤ N * N * m * k)
  | n + 1 => (cx m1 (N*k) && cy (n+1) (N*k)
              && decide (m1 * (n+1) ≤ N * N * m * k))
             || cutMulN_inner N cx cy k m m1 n

/-- Outer ladder: iterate over `m1` from 0 to `n`, inner sweeps
    over `m2 ∈ [0, m2Bound]`. -/
def cutMulN_outer (N : Nat) (cx cy : Nat → Nat → Bool)
    (k m m2Bound : Nat) : Nat → Bool
  | 0     => cutMulN_inner N cx cy k m 0 m2Bound
  | n + 1 => cutMulN_inner N cx cy k m (n+1) m2Bound
             || cutMulN_outer N cx cy k m m2Bound n

/-- **cutMulN**: N-parametric product cut.  Search bound
    `N² · (m + 1) · (k + 1)` covers the natural witnesses
    `m1 = a·k`, `m2 = c·k` whenever the closure inequality
    `a·c·k ≤ N²·m` holds. -/
def cutMulN (N : Nat) (cx cy : Nat → Nat → Bool) (m k : Nat) : Bool :=
  let bound := N * N * (m + 1) * (k + 1)
  cutMulN_outer N cx cy k m bound bound

/-! ## §2 — Existential characterisations of the ladders -/

/-- Pack three Bool conjuncts as a Prop conjunction.  PURE. -/
private theorem triple_and_pack (a b : Bool) (P : Prop) [Decidable P] :
    (a && b && decide P) = true ↔ a = true ∧ b = true ∧ P := by
  constructor
  · intro h
    have h1 : (a && b) = true ∧ decide P = true :=
      E213.Lib.Math.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _ |>.mp h
    have h2 : a = true ∧ b = true :=
      E213.Lib.Math.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _ |>.mp h1.1
    exact ⟨h2.1, h2.2, of_decide_eq_true h1.2⟩
  · rintro ⟨ha, hb, hP⟩
    exact (E213.Lib.Math.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _).mpr
      ⟨(E213.Lib.Math.Real213.Sum.BoolOrLadder.and_eq_true_pure _ _).mpr ⟨ha, hb⟩,
       decide_eq_true hP⟩

/-- Inner ladder existence iff: applies the `BoolOrLadder` template
    with the per-index witness `cx m1 (N·k) ∧ cy i (N·k) ∧ m1·i ≤
    N²·m·k`. -/
theorem cutMulN_inner_eq_true_iff
    (N : Nat) (cx cy : Nat → Nat → Bool) (k m m1 : Nat) (n : Nat) :
    cutMulN_inner N cx cy k m m1 n = true
      ↔ ∃ i, i ≤ n ∧ cx m1 (N*k) = true ∧ cy i (N*k) = true
        ∧ m1 * i ≤ N * N * m * k :=
  E213.Lib.Math.Real213.Sum.BoolOrLadder.bool_or_ladder_iff_with_pack
    (fun i => cx m1 (N*k) && cy i (N*k) && decide (m1 * i ≤ N * N * m * k))
    (cutMulN_inner N cx cy k m m1)
    (fun _ => triple_and_pack _ _ _)
    rfl
    (fun _ => rfl)
    n

/-- Outer ladder existence iff: combines the outer `BoolOrLadder`
    template with the inner existential.  Yields the nested
    double-existential characterising the cutMulN search. -/
theorem cutMulN_outer_eq_true_iff
    (N : Nat) (cx cy : Nat → Nat → Bool) (k m m2Bound : Nat) (n : Nat) :
    cutMulN_outer N cx cy k m m2Bound n = true
      ↔ ∃ m1, m1 ≤ n ∧ ∃ m2, m2 ≤ m2Bound
        ∧ cx m1 (N*k) = true ∧ cy m2 (N*k) = true
        ∧ m1 * m2 ≤ N * N * m * k :=
  E213.Lib.Math.Real213.Sum.BoolOrLadder.bool_or_ladder_iff_with_pack
    (fun i => cutMulN_inner N cx cy k m i m2Bound)
    (fun n => cutMulN_outer N cx cy k m m2Bound n)
    (fun i => cutMulN_inner_eq_true_iff N cx cy k m i m2Bound)
    rfl
    (fun _ => rfl)
    n

/-! ## §3 — Forward N-fiber closure

The forward direction: when the N-aware search certifies a
product witness on same-denominator-N const cuts, the
`(a · c) / N²` rational inequality at `(m, k)` holds.  Matches
`cutMul_const_const_forward` (`Mul/CutMulConstConst.lean`)
specialised to same-N inputs with the N-aware search.

Backward direction (`constCut (a·c) (N·N) → cutMulN N`) is the
**precision-artifact direction** and fails in general without
a divisibility hypothesis — same artifact as the standard
`cutMul`.  See `Mul/CutMulConstConst.precision_artifact_at_k3`
for the structurally identical witness on `cutMul`.  Adding the
hypothesis `N ∣ k` (or sufficient bound on `a`, `c`) unlocks
the bidirectional closure; recorded as continuing work in the
`Mobius213` canonical-equivalence chapter. -/

/-- ★★★★★ **Forward N-fiber closure**: `cutMulN N` certifying a
    product witness on same-denominator-N const cuts implies the
    `(a · c) / N²` rational inequality at `(m, k)`. -/
theorem cutMulN_const_const_forward (N a c m k : Nat) (hN : 0 < N)
    (h : cutMulN N (constCut a N) (constCut c N) m k = true) :
    constCut (a * c) (N * N) m k = true := by
  change cutMulN_outer N (constCut a N) (constCut c N) k m
          (N * N * (m + 1) * (k + 1)) (N * N * (m + 1) * (k + 1)) = true at h
  obtain ⟨m1, _, m2, _, hcx, hcy, hmul⟩ :=
    (cutMulN_outer_eq_true_iff N (constCut a N) (constCut c N) k m
        (N * N * (m + 1) * (k + 1)) (N * N * (m + 1) * (k + 1))).mp h
  have h_acx : a * (N * k) ≤ N * m1 := of_decide_eq_true hcx
  have h_acy : c * (N * k) ≤ N * m2 := of_decide_eq_true hcy
  show decide (a * c * k ≤ N * N * m) = true
  apply decide_eq_true
  have h_ak_m1 : a * k ≤ m1 := by
    have h_eq : a * (N * k) = N * (a * k) := by
      rw [E213.Tactic.NatHelper.mul_left_comm]
    rw [h_eq] at h_acx
    exact Nat.le_of_mul_le_mul_left h_acx hN
  have h_ck_m2 : c * k ≤ m2 := by
    have h_eq : c * (N * k) = N * (c * k) := by
      rw [E213.Tactic.NatHelper.mul_left_comm]
    rw [h_eq] at h_acy
    exact Nat.le_of_mul_le_mul_left h_acy hN
  have h_prod : (a * k) * (c * k) ≤ m1 * m2 := Nat.mul_le_mul h_ak_m1 h_ck_m2
  have h_chain : (a * k) * (c * k) ≤ N * N * m * k :=
    Nat.le_trans h_prod hmul
  have h_ak_ck : (a * k) * (c * k) = a * c * k * k := by
    rw [← E213.Tactic.NatHelper.mul_assoc (a*k) c k,
        E213.Tactic.NatHelper.mul_assoc a k c,
        Nat.mul_comm k c,
        ← E213.Tactic.NatHelper.mul_assoc a c k]
  rw [h_ak_ck] at h_chain
  cases k with
  | zero =>
    show a * c * 0 ≤ N * N * m
    rw [Nat.mul_zero]; exact Nat.zero_le _
  | succ j =>
    have h_swap_l : a * c * (j+1) * (j+1) = (j+1) * (a * c * (j+1)) :=
      Nat.mul_comm _ _
    have h_swap_r : N * N * m * (j+1) = (j+1) * (N * N * m) := Nat.mul_comm _ _
    rw [h_swap_l, h_swap_r] at h_chain
    exact Nat.le_of_mul_le_mul_left h_chain (Nat.succ_pos j)

/-- ★★ **Contrapositive**: when the `(a · c) / N²` inequality
    fails, `cutMulN N` also fails.  Matches
    `cutMul_const_const_contrapositive` pattern. -/
theorem cutMulN_const_const_contrapositive (N a c m k : Nat) (hN : 0 < N)
    (h : constCut (a * c) (N * N) m k = false) :
    cutMulN N (constCut a N) (constCut c N) m k = false := by
  cases hcm : cutMulN N (constCut a N) (constCut c N) m k with
  | true =>
    have := cutMulN_const_const_forward N a c m k hN hcm
    rw [this] at h; cases h
  | false => rfl

/-! ## §4 — cutEq congruences (cutMulN respects pointwise equality) -/

private theorem bool_eq_iff (a b : Bool) (h : a = true ↔ b = true) :
    a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

/-- ★★ cutMulN respects cutEq in the left argument. -/
theorem cutMulN_cutEq_left (N : Nat) (cx cx' cy : Nat → Nat → Bool)
    (h : cutEq cx cx') (m k : Nat) :
    cutMulN N cx cy m k = cutMulN N cx' cy m k := by
  apply bool_eq_iff
  show cutMulN_outer N cx cy k m (N*N*(m+1)*(k+1)) (N*N*(m+1)*(k+1)) = true
       ↔ cutMulN_outer N cx' cy k m (N*N*(m+1)*(k+1)) (N*N*(m+1)*(k+1)) = true
  constructor
  · intro hh
    obtain ⟨m1, hm1, m2, hm2, hcx, hcy, hmul⟩ :=
      (cutMulN_outer_eq_true_iff N cx cy k m _ _).mp hh
    exact (cutMulN_outer_eq_true_iff N cx' cy k m _ _).mpr
      ⟨m1, hm1, m2, hm2, (h m1 (N*k)) ▸ hcx, hcy, hmul⟩
  · intro hh
    obtain ⟨m1, hm1, m2, hm2, hcx', hcy, hmul⟩ :=
      (cutMulN_outer_eq_true_iff N cx' cy k m _ _).mp hh
    exact (cutMulN_outer_eq_true_iff N cx cy k m _ _).mpr
      ⟨m1, hm1, m2, hm2, (h m1 (N*k)).symm ▸ hcx', hcy, hmul⟩

/-- ★★ cutMulN respects cutEq in the right argument. -/
theorem cutMulN_cutEq_right (N : Nat) (cx cy cy' : Nat → Nat → Bool)
    (h : cutEq cy cy') (m k : Nat) :
    cutMulN N cx cy m k = cutMulN N cx cy' m k := by
  apply bool_eq_iff
  show cutMulN_outer N cx cy k m (N*N*(m+1)*(k+1)) (N*N*(m+1)*(k+1)) = true
       ↔ cutMulN_outer N cx cy' k m (N*N*(m+1)*(k+1)) (N*N*(m+1)*(k+1)) = true
  constructor
  · intro hh
    obtain ⟨m1, hm1, m2, hm2, hcx, hcy, hmul⟩ :=
      (cutMulN_outer_eq_true_iff N cx cy k m _ _).mp hh
    exact (cutMulN_outer_eq_true_iff N cx cy' k m _ _).mpr
      ⟨m1, hm1, m2, hm2, hcx, (h m2 (N*k)) ▸ hcy, hmul⟩
  · intro hh
    obtain ⟨m1, hm1, m2, hm2, hcx, hcy', hmul⟩ :=
      (cutMulN_outer_eq_true_iff N cx cy' k m _ _).mp hh
    exact (cutMulN_outer_eq_true_iff N cx cy k m _ _).mpr
      ⟨m1, hm1, m2, hm2, hcx, (h m2 (N*k)).symm ▸ hcy', hmul⟩

end E213.Lib.Math.Real213.Mul.CutMulN
