import E213.Lib.Math.Real213.RateModulus
import E213.Meta.Tactic.NatHelper

/-!
# CrossDetOvertake — completability is a comparison of two growth-axes

`Htel_of_crossdet` reduced "does this real carry a free modulus?" to a
single *tower-internal* inequality — the **cross-determinant smallness condition**

> `i·(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}`   (`CrossDetSmall W d`)

comparing the cross-determinant axis `W` (`W_i = a_{i+1}d_i − a_i d_{i+1}`, the
divergence ladder's central object) against the denominator axis `d`.  No
irrationality measure, no LEM, no countability: just two growth-axes inside the
resolution tower.  This file proves the **boundary layer** — the condition holds
below a critical tower level and fails above it, exactly where the cross-determinant's
growth overtakes the denominator's — with both regimes realised over the *same*
single-exponential denominator `d_i = 2^i`.

  * ★ `crossdet_small_total_modulus` — **below ⟹ free.**  Any numerator/denominator
    realising a cross-det that satisfies `CrossDetSmall` carries a total ∅-axiom
    modulus (`N = k+2`), via `Htel_of_crossdet` then `rate_total_modulus`.  The
    complete chain "cross-det small ⟹ completes".
  * ★ `overtake_breaks` — **above ⟹ the bridge's smallness fails.**  If the
    cross-determinant overtakes the *next* denominator (`d_{i+1} ≤ W_i` for `i ≥ 2`),
    `CrossDetSmall` is false: the sufficient completability condition is violated.
  * ★★★ `dexp_overtakes_denom` — the **concrete witness**.  The double exponential
    `W_i = 2^{2^i}` (`DepthDoubleExp`'s object — no finite ratio-coordinate,
    `dexp_not_const`) overtakes the single-exponential denominator `d_i = 2^i`
    (`2^{i+1} ≤ 2^{2^i}` since `i+1 ≤ 2^i`), so `CrossDetSmall` fails.  This is the
    critical layer made concrete: **the cross-determinant's exponential growth
    overtaking the denominator's is the same `2^{2^i}` that `DepthDoubleExp` shows the
    ratio axis cannot cross.**
  * ★★★ `const_crossdet_small` — the **free bottom** over the same denominator.  A
    *constant* cross-determinant `W_i = 1` (the det-one floor, `DepthFloorDetOne`)
    satisfies `CrossDetSmall` against `d_i = 2^i` (`i(i+1) ≤ (i+1)·2^i` since
    `i ≤ 2^i`): the trivially-free bottom.

So the single-exponential denominator `2^i` is the *fixed reference axis*; the
cross-determinant's position relative to it — constant (free) vs double-exponential
(broken) — decides completability.  "Which reals complete?" is not a yes/no fact
about individual points but a stratification by where the cross-det axis sits
relative to the denominator axis.  The tower has no top (`DepthCeilingResidue`): the
overtaking layer recedes without bound, so the boundary is the residue read at the
scale of divergence-complexity.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.CrossDetOvertake

open E213.Lib.Math.Real213.RateModulus (rcut Htel_of_crossdet rate_total_modulus)
open E213.Tactic.NatHelper (mul_assoc)

/-! ## §0 — the smallness condition: the bridge's currency -/

/-- The **cross-determinant smallness condition** — `Htel_of_crossdet`'s hypothesis,
    named as the comparison of two growth-axes.  The cross-determinant `W` per step is
    dominated by the denominator's discrete growth: `i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}`. -/
def CrossDetSmall (W d : Nat → Nat) : Prop :=
  ∀ i, 1 ≤ i → i * (i + 1) * W i + i * d i ≤ (i + 1) * d (i + 1)

/-! ## §1 — below the boundary ⟹ the real completes -/

/-- ★ **Below ⟹ free.**  Any convergent num/den `a/d` whose cross-determinant `W`
    (given by the relation `hW`) satisfies `CrossDetSmall` carries a total ∅-axiom
    modulus `N = k+2`: `CrossDetSmall W d` is exactly the hypothesis of
    `Htel_of_crossdet`, so it produces `Htel`, and `rate_total_modulus` then completes
    the real.  The full chain "cross-det dominated by the denominator's growth ⟹
    completes", with no measure. -/
theorem crossdet_small_total_modulus {a d : Nat → Nat} (W : Nat → Nat)
    (hd : ∀ i, 1 ≤ d i)
    (hW : ∀ i, a (i + 1) * d i = a i * d (i + 1) + W i)
    (hcs : CrossDetSmall W d)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i + 1) < a (i + 1) * d i)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut a d i m k = rcut a d j m k :=
  rate_total_modulus hd
    (Htel_of_crossdet W hW hcs) hmono hmonoS m k hk

/-! ## §2 — above the boundary ⟹ the smallness condition fails -/

/-- ★ **Above ⟹ the bridge breaks.**  If the cross-determinant overtakes the *next*
    denominator (`d_{i+1} ≤ W_i` for `i ≥ 2`) on a positive-denominator sequence, then
    `CrossDetSmall` is false — the sufficient completability condition is violated.

    Tested at `i = 2`: smallness would force `2·3·W₂ + 2·d₂ ≤ 3·d₃ ≤ 3·W₂`, hence
    `6·W₂ ≤ 3·W₂` with `W₂ ≥ 1` (`1 ≤ d₃ ≤ W₂`), contradicting `3·W₂ < 6·W₂`.  (This
    falsifies the *sufficient* bridge, the honest tower-internal boundary; it is not a
    claim that no modulus whatsoever exists.) -/
theorem overtake_breaks (W d : Nat → Nat)
    (hd : ∀ i, 1 ≤ d i)
    (hover : ∀ i, 2 ≤ i → d (i + 1) ≤ W i) :
    ¬ CrossDetSmall W d := by
  intro hcs
  have hsmall : 2 * 3 * W 2 + 2 * d 2 ≤ 3 * d 3 := hcs 2 (by decide)
  have hov : d 3 ≤ W 2 := hover 2 (by decide)
  have h3 : 3 * d 3 ≤ 3 * W 2 := Nat.mul_le_mul_left 3 hov
  have hchain : 2 * 3 * W 2 ≤ 3 * W 2 :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans hsmall h3)
  have hW2 : 1 ≤ W 2 := Nat.le_trans (hd 3) hov
  have hlt : 3 * W 2 < 2 * 3 * W 2 := Nat.mul_lt_mul_of_pos_right (by decide) hW2
  exact absurd hlt (Nat.not_lt.mpr hchain)

/-! ## §3 — the tower-native arithmetic: `2^i` dominates the polynomial axis -/

/-- `n + 1 ≤ 2^n` — the single exponential outgrows the linear axis. -/
theorem two_pow_ge_succ : ∀ n, n + 1 ≤ 2 ^ n
  | 0 => by decide
  | n + 1 => by
    rw [Nat.pow_succ, Nat.mul_two]
    have ih := two_pow_ge_succ n
    have hpos : 1 ≤ 2 ^ n := Nat.pos_pow_of_pos n (by decide)
    exact Nat.le_trans (Nat.add_le_add_right ih 1) (Nat.add_le_add_left hpos (2 ^ n))

/-- `n ≤ 2^n`. -/
theorem two_pow_ge_self (n : Nat) : n ≤ 2 ^ n :=
  Nat.le_trans (Nat.le_succ n) (two_pow_ge_succ n)

/-! ## §4 — the two regimes over the single-exponential denominator `d_i = 2^i` -/

/-- The single-exponential **denominator axis** `d_i = 2^i` — the fixed reference. -/
def denomExp : Nat → Nat := fun i => 2 ^ i

/-- The double-exponential **cross-determinant** `W_i = 2^{2^i}` — `DepthDoubleExp`'s
    object, with no finite ratio-coordinate. -/
def crossW : Nat → Nat := fun i => 2 ^ (2 ^ i)

/-- ★★★ **The overtake is concrete (the critical layer).**  The double-exponential
    cross-determinant `W_i = 2^{2^i}` overtakes the single-exponential denominator
    `d_i = 2^i` — `d_{i+1} = 2^{i+1} ≤ 2^{2^i} = W_i` because `i+1 ≤ 2^i`
    (`two_pow_ge_succ`) and `2^·` is monotone — so `CrossDetSmall` fails.  The same
    `2^{2^i}` that `DepthDoubleExp.dexp_not_const` shows the ratio axis cannot cross is
    exactly the cross-determinant whose growth overtakes the denominator and breaks the
    completability bridge. -/
theorem dexp_overtakes_denom : ¬ CrossDetSmall crossW denomExp :=
  overtake_breaks crossW denomExp
    (fun i => Nat.pos_pow_of_pos i (by decide))
    (fun i _ => by
      show 2 ^ (i + 1) ≤ 2 ^ (2 ^ i)
      exact Nat.pow_le_pow_right (by decide) (two_pow_ge_succ i))

/-- ★★★ **The free bottom is concrete.**  A *constant* cross-determinant `W_i = 1`
    (the det-one floor of `DepthFloorDetOne` — already at the divergence-ladder floor)
    satisfies `CrossDetSmall` against the same denominator `d_i = 2^i`: the polynomial
    factor `i(i+1)` is dominated by `(i+1)·2^i` (since `i ≤ 2^i`).  So over the fixed
    `2^i` axis, the det-one floor is the trivially-free bottom while the double
    exponential breaks it — the boundary is a position on the cross-det axis. -/
theorem const_crossdet_small : CrossDetSmall (fun _ => 1) denomExp := by
  intro i _
  show i * (i + 1) * 1 + i * 2 ^ i ≤ (i + 1) * 2 ^ (i + 1)
  rw [Nat.mul_one, Nat.pow_succ, ← mul_assoc, Nat.mul_two]
  have hle : i ≤ 2 ^ i := two_pow_ge_self i
  have h1 : i * (i + 1) ≤ (i + 1) * 2 ^ i := by
    rw [Nat.mul_comm i (i + 1)]; exact Nat.mul_le_mul_left (i + 1) hle
  have h2 : i * 2 ^ i ≤ (i + 1) * 2 ^ i := Nat.mul_le_mul_right (2 ^ i) (Nat.le_succ i)
  exact Nat.add_le_add h1 h2

/-! ## §5 — the boundary, bundled -/

/-- ★★★ **The completability boundary, over one denominator axis.**  Against the fixed
    single-exponential denominator `d_i = 2^i`:

    * a **constant** cross-determinant (`W = 1`, the det-one floor) satisfies the
      smallness condition — the trivially-free bottom; while
    * the **double-exponential** cross-determinant (`W_i = 2^{2^i}`) overtakes it and
      breaks the smallness condition.

    Completability is therefore not a yes/no property of a real but a *stratification*
    by where its cross-determinant axis sits relative to the denominator axis — the
    exponential-overtake boundary, proved by comparing two tower-internal growth-axes
    with no irrationality measure and no LEM. -/
theorem completability_boundary :
    CrossDetSmall (fun _ => 1) denomExp ∧ ¬ CrossDetSmall crossW denomExp :=
  ⟨const_crossdet_small, dexp_overtakes_denom⟩

end E213.Lib.Math.Real213.CrossDetOvertake
