import E213.Lib.Math.Analysis.ModulusConvergence
import E213.Lib.Math.Analysis.UniformLimitContinuous
import E213.Meta.Nat.Max213

/-!
# Limit arithmetic: sum limit law on the concrete `distMet` metric (∅-axiom)

`distN_add_le` (additive-compatibility core) + `add_converges` (headline:
sum of two convergent sequences converges to the sum, modulus computed
`m ↦ max (ra (m+1)) (rb (m+1))`).
-/

namespace E213.Lib.Math.Analysis.LimitArithmetic

open E213.Lib.Math.Analysis.UniformLimitContinuous
  (distN distN_tri distN_symm closeN distMet le_sub_add sub_le_of_le_add)
open E213.Lib.Math.Analysis.ModulusConvergence (ConvergesWith const_converges)

/-! ## 1. The additive-compatibility core -/

/-- One-sided additive bound: `(a + u) - (b + v) ≤ (a - b) + (u - v)`.
    Pure `Nat` truncated subtraction via `sub_le_of_le_add` + `le_sub_add`. -/
theorem add_sub_le (a u b v : Nat) :
    (a + u) - (b + v) ≤ (a - b) + (u - v) := by
  apply sub_le_of_le_add
  -- suffices: a + u ≤ ((a - b) + (u - v)) + (b + v)
  have ha : a ≤ (a - b) + b := le_sub_add b a
  have hu : u ≤ (u - v) + v := le_sub_add v u
  have hsum : a + u ≤ ((a - b) + b) + ((u - v) + v) := Nat.add_le_add ha hu
  -- rearrange ((a-b)+b) + ((u-v)+v) = ((a-b)+(u-v)) + (b+v)
  have hrearr : ((a - b) + b) + ((u - v) + v) = ((a - b) + (u - v)) + (b + v) := by
    rw [Nat.add_assoc (a - b) b ((u - v) + v)]
    rw [show b + ((u - v) + v) = (b + (u - v)) + v from
        (Nat.add_assoc b (u - v) v).symm]
    rw [Nat.add_comm b (u - v)]
    rw [Nat.add_assoc (u - v) b v]
    rw [show (a - b) + ((u - v) + (b + v)) = ((a - b) + (u - v)) + (b + v) from
        (Nat.add_assoc (a - b) (u - v) (b + v)).symm]
  rw [hrearr] at hsum
  exact hsum

/-- **`distN_add_le` (additive-compatibility core).**  The `Nat` distance is
    sub-additive under componentwise addition:
    `distN (a + u) (b + v) ≤ distN a b + distN u v`.
    Both one-sided gaps bounded by `add_sub_le`, then the four summands
    regrouped. -/
theorem distN_add_le (a u b v : Nat) :
    distN (a + u) (b + v) ≤ distN a b + distN u v := by
  have h1 : (a + u) - (b + v) ≤ (a - b) + (u - v) := add_sub_le a u b v
  have h2 : (b + v) - (a + u) ≤ (b - a) + (v - u) := add_sub_le b v a u
  have hsum : ((a + u) - (b + v)) + ((b + v) - (a + u))
      ≤ ((a - b) + (u - v)) + ((b - a) + (v - u)) := Nat.add_le_add h1 h2
  have hrearr : ((a - b) + (u - v)) + ((b - a) + (v - u))
      = ((a - b) + (b - a)) + ((u - v) + (v - u)) := by
    rw [Nat.add_assoc (a - b) (u - v) ((b - a) + (v - u))]
    rw [show (u - v) + ((b - a) + (v - u)) = ((u - v) + (b - a)) + (v - u) from
        (Nat.add_assoc (u - v) (b - a) (v - u)).symm]
    rw [Nat.add_comm (u - v) (b - a)]
    rw [Nat.add_assoc (b - a) (u - v) (v - u)]
    rw [show (a - b) + ((b - a) + ((u - v) + (v - u)))
          = ((a - b) + (b - a)) + ((u - v) + (v - u)) from
        (Nat.add_assoc (a - b) (b - a) ((u - v) + (v - u))).symm]
  show ((a + u) - (b + v)) + ((b + v) - (a + u)) ≤ distN a b + distN u v
  have hgoal : distN a b + distN u v = ((a - b) + (b - a)) + ((u - v) + (v - u)) :=
    rfl
  rw [hgoal, ← hrearr]
  exact hsum

/-! ## 2. The headline: sum of convergent sequences converges to the sum -/

/-- The two-halves-make-a-whole bookkeeping at the `closeN` level:
    if `2^(m+1)·X < 2^(L+1)` and `2^(m+1)·Y < 2^(L+1)` then
    `2^m·(X+Y) < 2^(L+1)`.  Same halving argument as `closeN_tri`, but for an
    arbitrary upper bound `X+Y` on the distance (here `distN a b + distN u v`). -/
theorem closeN_add_core (L m X Y : Nat)
    (hX : 2 ^ (m + 1) * X < 2 ^ (L + 1))
    (hY : 2 ^ (m + 1) * Y < 2 ^ (L + 1)) :
    2 ^ m * (X + Y) < 2 ^ (L + 1) := by
  -- 2^(m+1)·X = 2·(2^m·X)
  have eX : 2 ^ (m + 1) * X = 2 * (2 ^ m * X) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2,
        E213.Meta.Nat.PureNat.mul_assoc 2 (2 ^ m) X]
  have eY : 2 ^ (m + 1) * Y = 2 * (2 ^ m * Y) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2,
        E213.Meta.Nat.PureNat.mul_assoc 2 (2 ^ m) Y]
  have hX2 : 2 * (2 ^ m * X) < 2 ^ (L + 1) := by rw [← eX]; exact hX
  have hY2 : 2 * (2 ^ m * Y) < 2 ^ (L + 1) := by rw [← eY]; exact hY
  -- 2·((2^m·X)+(2^m·Y)) < 2·2^(L+1)
  have hsum2 : 2 * ((2 ^ m * X) + (2 ^ m * Y)) < 2 * 2 ^ (L + 1) := by
    rw [Nat.mul_add]
    calc 2 * (2 ^ m * X) + 2 * (2 ^ m * Y)
        < 2 ^ (L + 1) + 2 * (2 ^ m * Y) := Nat.add_lt_add_right hX2 _
      _ < 2 ^ (L + 1) + 2 ^ (L + 1) := Nat.add_lt_add_left hY2 _
      _ = 2 * 2 ^ (L + 1) := by rw [Nat.two_mul]
  have hsum : (2 ^ m * X) + (2 ^ m * Y) < 2 ^ (L + 1) :=
    E213.Meta.Nat.NatDiv213.two_cancel_lt _ _ hsum2
  -- 2^m·(X+Y) = 2^m·X + 2^m·Y
  have hdistr : 2 ^ m * (X + Y) = (2 ^ m * X) + (2 ^ m * Y) := Nat.mul_add _ _ _
  rw [hdistr]; exact hsum

/-- **★ `add_converges` — the headline (∅-axiom, modulus computed).**
    On the concrete metric `distMet L0`, if `a → A` with modulus `ra` and
    `b → B` with modulus `rb`, then the pointwise sum `fun n => a n + b n`
    converges to `A + B` with the **computed** modulus
    `m ↦ max (ra (m+1)) (rb (m+1))`.

    For `n` past both bounds, `distN (a n + b n) (A + B) ≤ distN (a n) A +
    distN (b n) B` (`distN_add_le`); each summand is `1/2^(m+1)`-small (from
    the convergence hypotheses at scale `m+1`), and two halves make a whole
    (`closeN_add_core`). -/
theorem add_converges {L0 : Nat} {a b : Nat → Nat} {A B : Nat} {ra rb : Nat → Nat}
    (ha : ConvergesWith (distMet L0) a A ra)
    (hb : ConvergesWith (distMet L0) b B rb) :
    ConvergesWith (distMet L0) (fun n => a n + b n) (A + B)
      (fun m => Nat.max (ra (m + 1)) (rb (m + 1))) := by
  intro m n hn
  -- hn : max (ra (m+1)) (rb (m+1)) ≤ n
  have hna : ra (m + 1) ≤ n :=
    Nat.le_trans (E213.Meta.Nat.Max213.le_max_left (ra (m + 1)) (rb (m + 1))) hn
  have hnb : rb (m + 1) ≤ n :=
    Nat.le_trans (E213.Meta.Nat.Max213.le_max_right (ra (m + 1)) (rb (m + 1))) hn
  -- closeN at scale m+1 for each component
  have ca : closeN L0 (m + 1) (a n) A := ha (m + 1) n hna
  have cb : closeN L0 (m + 1) (b n) B := hb (m + 1) n hnb
  -- unfold: 2^(m+1)·distN (a n) A < 2^(L0+1), similarly for b
  have hXlt : 2 ^ (m + 1) * distN (a n) A < 2 ^ (L0 + 1) := ca
  have hYlt : 2 ^ (m + 1) * distN (b n) B < 2 ^ (L0 + 1) := cb
  -- core: 2^m · (distN (a n) A + distN (b n) B) < 2^(L0+1)
  have hcore : 2 ^ m * (distN (a n) A + distN (b n) B) < 2 ^ (L0 + 1) :=
    closeN_add_core L0 m (distN (a n) A) (distN (b n) B) hXlt hYlt
  -- distN (a n + b n) (A + B) ≤ distN (a n) A + distN (b n) B
  have hle : distN (a n + b n) (A + B) ≤ distN (a n) A + distN (b n) B :=
    distN_add_le (a n) (b n) A B
  -- goal: closeN L0 m (a n + b n) (A + B), i.e. 2^m·distN (a n + b n) (A+B) < 2^(L0+1)
  show closeN L0 m (a n + b n) (A + B)
  show 2 ^ m * distN (a n + b n) (A + B) < 2 ^ (L0 + 1)
  have hmono : 2 ^ m * distN (a n + b n) (A + B)
      ≤ 2 ^ m * (distN (a n) A + distN (b n) B) :=
    Nat.mul_le_mul_left _ hle
  exact Nat.lt_of_le_of_lt hmono hcore

/-! ## 3. Non-vacuous: const + const → sum -/

/-- `const + const → sum` on `distMet L0`: instantiating `add_converges` with
    two `const_converges` witnesses gives that the (constant) sum sequence
    converges to `c + d`. -/
theorem const_add_const_converges (L0 c d : Nat) :
    ConvergesWith (distMet L0) (fun _ => c + d) (c + d)
      (fun m => Nat.max ((fun _ => 0) (m + 1)) ((fun _ => 0) (m + 1))) :=
  add_converges (const_converges (distMet L0) c) (const_converges (distMet L0) d)

/-! ## 4. Shift corollary: a → A ⟹ a + c → A + c -/

/-- **Shift law.**  If `a → A` with modulus `ra`, then `fun n => a n + c`
    converges to `A + c` with modulus `m ↦ max (ra (m+1)) 0 = ra (m+1)`.
    Corollary of `add_converges` against the constant `c`. -/
theorem shift_converges {L0 : Nat} {a : Nat → Nat} {A : Nat} {ra : Nat → Nat}
    (ha : ConvergesWith (distMet L0) a A ra) (c : Nat) :
    ConvergesWith (distMet L0) (fun n => a n + c) (A + c)
      (fun m => Nat.max (ra (m + 1)) ((fun _ => 0) (m + 1))) :=
  add_converges ha (const_converges (distMet L0) c)

-- purity probes
#print axioms E213.Lib.Math.Analysis.LimitArithmetic.add_sub_le
#print axioms E213.Lib.Math.Analysis.LimitArithmetic.distN_add_le
#print axioms E213.Lib.Math.Analysis.LimitArithmetic.closeN_add_core
#print axioms E213.Lib.Math.Analysis.LimitArithmetic.add_converges
#print axioms E213.Lib.Math.Analysis.LimitArithmetic.const_add_const_converges
#print axioms E213.Lib.Math.Analysis.LimitArithmetic.shift_converges

end E213.Lib.Math.Analysis.LimitArithmetic
