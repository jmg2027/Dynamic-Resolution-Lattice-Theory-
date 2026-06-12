import E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut
import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMinor
import E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpMoebius
import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Int213.OrderMul

/-!
# LambertOrder — the upper order transfer: the series sits below every odd convergent

The weld's `(A′)`-family, in full.  `CothSeriesCut` proved the base instance
(`T_J` below the *first* odd convergent, every `q`); here the whole family closes:

  ★ `series_le_odd` — `T_J ≤ p_{2i+1}/q_{2i+1}` for **every** truncation `J` and
    **every** odd convergent of the Lambert fold `[q; 3q, 5q, …]`.

Assembly (all pieces previously built):

  * the **minor sign** (`LambertMinor.minor_all`) is carried from the position
    functions `apF/bpF` onto the weld polynomial lists by a totalized coefficient
    reading `nth` (§1–§2) — no list edge cases survive the transport;
  * the **Chebyshev engine** (`LambertWeld.cross_le`) fires twice — once at level
    `2i+2` against the zero-padded `BP` (the padding is the equivalence-transform
    `q²`, §3), once at level `2i+1` for the tail;
  * the two firings are chained through the pivot `dev (AP (2i+1))` by
    `ratio_chain`, whose cross condition is exactly the **det-one floor** read
    through the evaluation bridge (`cf_det_even` ⟹ `dev_cross_det`, §4);
  * the weld rows (`weld_pair_cosh/sinh`) convert the result into the
    cosh/sinh-partial comparison, and the conversion weight `v0Fac` cancels (§5).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertOrder

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMinor
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut
  (TNum cothSeriesAb cothSeriesCut_eq)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus
  (cfPn cothCF cothCF_pos cfP_eq_cast)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionFloor
  (cfP cfQ cfQn cfQn_pos cfQ_eq_cast cfDet cf_det_even)
open E213.Lib.Math.NumberSystems.Real213 (AbCutSeq)

/-! ## §1 — the totalized coefficient reading of a list -/

/-- Totalized coefficient access (`0` off the end) — the list-side mirror of the
    position functions `apF/bpF`. -/
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, i + 1 => nth cs i

theorem nth_ladd : ∀ (a b : List Nat) (i : Nat), nth (ladd a b) i = nth a i + nth b i
  | [], b, i => (Nat.zero_add (nth b i)).symm
  | _ :: _, [], _ => (Nat.add_zero _).symm
  | _ :: _, _ :: _, 0 => rfl
  | _ :: as, _ :: bs, i + 1 => nth_ladd as bs i

theorem nth_lsmul (k : Nat) : ∀ (c : List Nat) (i : Nat), nth (lsmul k c) i = k * nth c i
  | [], _ => (Nat.mul_zero k).symm
  | _ :: _, 0 => rfl
  | _ :: cs, i + 1 => nth_lsmul k cs i

theorem nth_append_zero : ∀ (c : List Nat) (i : Nat), nth (c ++ [0]) i = nth c i
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: cs, i + 1 => nth_append_zero cs i

/-- The weld polynomials read coefficient-wise as the minor position functions. -/
theorem AP_nth : ∀ (n i : Nat), nth (AP n) i = apF n i
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | 1, 0 => rfl
  | 1, _ + 1 => rfl
  | n + 2, i => by
    show nth (ladd (lsmul (2 * n + 3) (AP (n + 1))) (0 :: AP n)) i = apF (n + 2) i
    rw [nth_ladd, nth_lsmul]
    cases i with
    | zero =>
      show (2 * n + 3) * nth (AP (n + 1)) 0 + 0 = apF (n + 2) 0
      rw [AP_nth (n + 1) 0]
      exact Nat.add_zero _
    | succ s =>
      show (2 * n + 3) * nth (AP (n + 1)) (s + 1) + nth (AP n) s = apF (n + 2) (s + 1)
      rw [AP_nth (n + 1) (s + 1), AP_nth n s]
      exact rfl

theorem BP_nth : ∀ (n i : Nat), nth (BP n) i = bpF n i
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | 1, 0 => rfl
  | 1, _ + 1 => rfl
  | n + 2, i => by
    show nth (ladd (lsmul (2 * n + 3) (BP (n + 1))) (0 :: BP n)) i = bpF (n + 2) i
    rw [nth_ladd, nth_lsmul]
    cases i with
    | zero =>
      show (2 * n + 3) * nth (BP (n + 1)) 0 + 0 = bpF (n + 2) 0
      rw [BP_nth (n + 1) 0]
      exact Nat.add_zero _
    | succ s =>
      show (2 * n + 3) * nth (BP (n + 1)) (s + 1) + nth (BP n) s = bpF (n + 2) (s + 1)
      rw [BP_nth (n + 1) (s + 1), BP_nth n s]
      exact rfl

/-! ## §2 — the minor condition transported onto the lists -/

theorem scaledLE_of_nth (x y : Nat) : ∀ (us vs : List Nat),
    (∀ j, x * nth vs j ≤ y * nth us j) → scaledLE x y us vs
  | [], [], _ => True.intro
  | [], _ :: _, _ => True.intro
  | _ :: _, [], _ => True.intro
  | u :: us, v :: vs, h => by
    show x * v ≤ y * u ∧ scaledLE x y us vs
    exact ⟨h 0, scaledLE_of_nth x y us vs fun j => h (j + 1)⟩

theorem minorLE_of_nth : ∀ (a b : List Nat),
    (∀ i j, i < j → nth a i * nth b j ≤ nth b i * nth a j) → MinorLE a b
  | [], _, _ => True.intro
  | _ :: _, [], _ => True.intro
  | a :: as, b :: bs, h => by
    show scaledLE a b as bs ∧ MinorLE as bs
    exact ⟨scaledLE_of_nth a b as bs
        (fun j => h 0 (j + 1) (Nat.succ_le_succ (Nat.zero_le j))),
      minorLE_of_nth as bs
        (fun i j hij => h (i + 1) (j + 1) (Nat.succ_le_succ hij))⟩

/-- The minor condition of the weld polynomial pair, every level. -/
theorem minorLE_AP_BP (n : Nat) : MinorLE (AP n) (BP n) :=
  minorLE_of_nth (AP n) (BP n) (fun i j hij => by
    rw [AP_nth n i, AP_nth n j, BP_nth n i, BP_nth n j]
    exact minor_all n j i hij)

/-- The minor condition against the zero-padded `BP` (the pad reads `0`, so every
    new minor is free). -/
theorem minorLE_AP_BPpad (n : Nat) : MinorLE (AP n) (BP n ++ [0]) :=
  minorLE_of_nth (AP n) (BP n ++ [0]) (fun i j hij => by
    rw [AP_nth n i, AP_nth n j, nth_append_zero (BP n) i, nth_append_zero (BP n) j,
        BP_nth n i, BP_nth n j]
    exact minor_all n j i hij)

/-! ## §3 — the zero pad: `dev` gains the equivalence-transform `q²`, `PF` ignores it -/

theorem length_append_zero : ∀ c : List Nat, (c ++ [0]).length = c.length + 1
  | [] => rfl
  | _ :: cs => congrArg (· + 1) (length_append_zero cs)

theorem PF_append_zero (q m : Nat) : ∀ (c : List Nat) (J : Nat),
    PF q (c ++ [0]) m J = PF q c m J
  | [], J => by
    show 0 * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q [] m (J - 1) = PF q [] m J
    rw [Nat.zero_mul]
    show 0 + 2 * J * (2 * m + 2 * J + 1) * 0 = 0
    rw [Nat.mul_zero]
  | c :: cs, J => by
    show c * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q (cs ++ [0]) m (J - 1)
        = c * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q cs m (J - 1)
    rw [PF_append_zero q m cs (J - 1)]

private theorem pow_add_two' (q n : Nat) : q ^ (n + 2) = q ^ n * (q * q) := by
  show q ^ n * q * q = q ^ n * (q * q)
  ring_nat

theorem dev_append_zero (q : Nat) : ∀ c : List Nat, dev q (c ++ [0]) = q * q * dev q c
  | [] => by
    show dev q [0] = q * q * 0
    rw [Nat.mul_zero]
    rfl
  | c :: cs => by
    show dev q (c :: (cs ++ [0])) = q * q * dev q (c :: cs)
    rw [dev_cons q c (cs ++ [0]), dev_cons q c cs, length_append_zero cs,
        dev_append_zero q cs,
        show q ^ (2 * (cs.length + 1)) = q ^ (2 * cs.length) * (q * q) from
          pow_add_two' q (2 * cs.length)]
    ring_nat

/-! ## §4 — the det-one floor through the evaluation bridge -/

/-- `X + (−Y) = a ⟹ X = Y + a` over `ℤ` (the descent rearrangement). -/
private theorem int_eq_of_add_neg {X Y a : Int} (h : X + -Y = a) : X = Y + a := by
  have e : Y + a = X := by
    rw [← h, ← E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_comm Y X,
        E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_neg_cancel, Int.add_zero]
  exact e.symm

/-- The one-step determinant at an even index, over `ℕ`:
    `p_{2n+1}·q_{2n} = p_{2n}·q_{2n+1} + 1` — `cf_det_even` descended by `ofNat`
    injectivity (the det-one floor in subtraction-free form). -/
theorem cf_det_even_nat (a : Nat → Nat) (n : Nat) :
    cfPn a (2 * n + 1) * cfQn a (2 * n) = cfPn a (2 * n) * cfQn a (2 * n + 1) + 1 := by
  have h : cfP a (2 * n + 1) * cfQ a (2 * n) + -(cfP a (2 * n) * cfQ a (2 * n + 1))
      = 1 := cf_det_even a n
  rw [cfP_eq_cast a (2 * n + 1), cfQ_eq_cast a (2 * n), cfP_eq_cast a (2 * n),
      cfQ_eq_cast a (2 * n + 1)] at h
  have h3 := int_eq_of_add_neg h
  have goal_int : (↑(cfPn a (2 * n + 1) * cfQn a (2 * n)) : Int)
      = ↑(cfPn a (2 * n) * cfQn a (2 * n + 1) + 1) := by
    rw [Int.ofNat_mul, Int.ofNat_add, Int.ofNat_mul]
    exact h3
  exact Int.ofNat.inj goal_int

/-- ★★★ **The dev-level cross-determinant**: the det-one floor of the Lambert fold,
    read through the evaluation bridge — the exact `+1` that orients the
    `ratio_chain` pivot. -/
theorem dev_cross_det (q i : Nat) :
    q * dev q (AP (2 * i + 1)) * (q * dev q (BP (2 * i + 2))) + 1
      = dev q (AP (2 * i + 2)) * dev q (BP (2 * i + 1)) := by
  have h := cf_det_even_nat (cothCF q) i
  rw [(cf_bridge q i).2.1, (cf_bridge q i).1, (cf_bridge q i).2.2.1,
      (cf_bridge q i).2.2.2] at h
  exact h.symm

private theorem pos_of_mul_pos {a b : Nat} (h : 1 ≤ a * b) : 1 ≤ b := by
  cases b with
  | zero => rw [Nat.mul_zero] at h; exact absurd h (Nat.not_succ_le_zero 0)
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)

/-- The `ratio_chain` pivot is positive: `dev (AP (2i+1)) ≥ 1` (`q ≥ 1`), from the
    bridge and the positivity of the convergent numerators. -/
theorem dev_AP_odd_pos (q : Nat) (hq : 1 ≤ q) (i : Nat) : 1 ≤ dev q (AP (2 * i + 1)) := by
  have h := E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus.cfPn_pos
    (cothCF q) (cothCF_pos q hq) (2 * i)
  rw [(cf_bridge q i).1] at h
  exact pos_of_mul_pos h

theorem v0Fac_pos (J : Nat) : ∀ n, 1 ≤ v0Fac J n
  | 0 => Nat.le_refl 1
  | n + 1 => by
    show 1 ≤ (2 * J + 2 * n + 3) * v0Fac J n
    exact Nat.le_trans (v0Fac_pos J n)
      (Nat.le_mul_of_pos_left (v0Fac J n) (Nat.succ_pos _))

/-! ## §5 — the assembly: the series below every odd convergent -/

/-- ★★★★★ **The order-transfer core**: at every truncation `J` and every odd weld
    level `2i+1`,

      `(2J+1)·q²·cosh_J·dev (BP (2i+2)) ≤ sinh_J·dev (AP (2i+2))`.

    The cosh row (times `dev BPpad`) is dominated by the sinh row (times `dev AP`):
    the head pairing by `cross_le` at level `2i+2` (padded), the `2J`-tail by
    `cross_le` at level `2i+1` chained through the `dev (AP (2i+1))` pivot via the
    det-one floor (`dev_cross_det`); the conversion weight `v0Fac` cancels. -/
theorem series_below_odd_core (q : Nat) (hq : 1 ≤ q) (i J : Nat) :
    (2 * J + 1) * (q * q * coshNum q J) * dev q (BP (2 * i + 2))
      ≤ sinhNum q J * dev q (AP (2 * i + 2)) := by
  have hlenA : (AP (2 * i + 2)).length = i + 2 := (AP_BP_length i).2.1
  have hlenB : (BP (2 * i + 2)).length = i + 1 := (AP_BP_length i).2.2.2
  have hlenA1 : (AP (2 * i + 1)).length = i + 1 := (AP_BP_length i).1
  have hlenB1 : (BP (2 * i + 1)).length = i + 1 := (AP_BP_length i).2.2.1
  -- X-piece: cross_le at level 2i+2 against the padded BP
  have hX : PF q (AP (2 * i + 2)) (2 * i + 1) J * (q * q * dev q (BP (2 * i + 2)))
      ≤ dev q (AP (2 * i + 2)) * PF q (BP (2 * i + 2)) (2 * i + 1) J := by
    have h := cross_le q (2 * i + 1) (AP (2 * i + 2)) (BP (2 * i + 2) ++ [0]) J
      (by rw [hlenA, length_append_zero, hlenB])
      (minorLE_AP_BPpad (2 * i + 2))
    rwa [PF_append_zero, dev_append_zero] at h
  -- tail cross: cross_le at level 2i+1
  have hY2 : PF q (AP (2 * i + 1)) (2 * i + 2) (J - 1) * dev q (BP (2 * i + 1))
      ≤ dev q (AP (2 * i + 1)) * PF q (BP (2 * i + 1)) (2 * i + 2) (J - 1) :=
    cross_le q (2 * i + 2) (AP (2 * i + 1)) (BP (2 * i + 1)) (J - 1)
      (by rw [hlenA1, hlenB1]) (minorLE_AP_BP (2 * i + 1))
  -- the pivot inequality: det-one floor
  have h1 : q * q * dev q (BP (2 * i + 2)) * dev q (AP (2 * i + 1))
      ≤ dev q (AP (2 * i + 2)) * dev q (BP (2 * i + 1)) := by
    refine Nat.le.intro (k := 1) ?_
    calc q * q * dev q (BP (2 * i + 2)) * dev q (AP (2 * i + 1)) + 1
        = q * dev q (AP (2 * i + 1)) * (q * dev q (BP (2 * i + 2))) + 1 := by ring_nat
      _ = dev q (AP (2 * i + 2)) * dev q (BP (2 * i + 1)) := dev_cross_det q i
  -- Y-piece: chained through the positive pivot
  have hY : q * q * dev q (BP (2 * i + 2)) * PF q (AP (2 * i + 1)) (2 * i + 2) (J - 1)
      ≤ dev q (AP (2 * i + 2)) * PF q (BP (2 * i + 1)) (2 * i + 2) (J - 1) :=
    ratio_chain h1
      (by
        rw [Nat.mul_comm (dev q (BP (2 * i + 1)))
          (PF q (AP (2 * i + 1)) (2 * i + 2) (J - 1))]
        exact hY2)
      (dev_AP_odd_pos q hq i)
  -- assemble the two rows
  have hsum : q * q * dev q (BP (2 * i + 2)) * (vFac J (2 * i + 1) * coshNum q J)
      ≤ dev q (AP (2 * i + 2)) * (v0Fac J (2 * i + 1) * sinhNum q J) := by
    rw [weld_pair_cosh q (2 * i + 1) J, weld_pair_sinh q (2 * i + 1) J,
        Nat.mul_add, Nat.mul_add]
    refine Nat.add_le_add ?_ ?_
    · calc q * q * dev q (BP (2 * i + 2)) * PF q (AP (2 * i + 2)) (2 * i + 1) J
          = PF q (AP (2 * i + 2)) (2 * i + 1) J
            * (q * q * dev q (BP (2 * i + 2))) := by ring_nat
        _ ≤ dev q (AP (2 * i + 2)) * PF q (BP (2 * i + 2)) (2 * i + 1) J := hX
    · calc q * q * dev q (BP (2 * i + 2))
            * (2 * J * PF q (AP (2 * i + 1)) (2 * i + 2) (J - 1))
          = 2 * J * (q * q * dev q (BP (2 * i + 2))
              * PF q (AP (2 * i + 1)) (2 * i + 2) (J - 1)) := by ring_nat
        _ ≤ 2 * J * (dev q (AP (2 * i + 2))
              * PF q (BP (2 * i + 1)) (2 * i + 2) (J - 1)) :=
            Nat.mul_le_mul_left _ hY
        _ = dev q (AP (2 * i + 2))
              * (2 * J * PF q (BP (2 * i + 1)) (2 * i + 2) (J - 1)) := by ring_nat
  -- cancel the conversion weight
  have hfin : v0Fac J (2 * i + 1)
        * ((2 * J + 1) * (q * q * coshNum q J) * dev q (BP (2 * i + 2)))
      ≤ v0Fac J (2 * i + 1) * (sinhNum q J * dev q (AP (2 * i + 2))) := by
    calc v0Fac J (2 * i + 1)
          * ((2 * J + 1) * (q * q * coshNum q J) * dev q (BP (2 * i + 2)))
        = q * q * dev q (BP (2 * i + 2))
          * ((2 * J + 1) * v0Fac J (2 * i + 1) * coshNum q J) := by ring_nat
      _ = q * q * dev q (BP (2 * i + 2)) * (vFac J (2 * i + 1) * coshNum q J) := by
          rw [vFac_eq]
      _ ≤ dev q (AP (2 * i + 2)) * (v0Fac J (2 * i + 1) * sinhNum q J) := hsum
      _ = v0Fac J (2 * i + 1) * (sinhNum q J * dev q (AP (2 * i + 2))) := by ring_nat
  exact Nat.le_of_mul_le_mul_left hfin (v0Fac_pos J (2 * i + 1))

/-- ★★★★★ **The `(A′)`-family, complete**: the truncated coth series sits below
    **every** odd convergent of the Lambert fold, at **every** truncation —

      `T_J · q_{2i+1} ≤ s_J · p_{2i+1}`   (`T_J = (2J+1)·q·cosh_J / sinh_J`).

    `CothSeriesCut.coth_series_below_r1` was the `i = 0` instance; the family is
    the upper half of the weld's order transfer. -/
theorem series_le_odd (q : Nat) (hq : 1 ≤ q) (i J : Nat) :
    TNum q J * cfQn (cothCF q) (2 * i + 1)
      ≤ sinhNum q J * cfPn (cothCF q) (2 * i + 1) := by
  rw [(cf_bridge q i).2.2.2, (cf_bridge q i).2.1]
  show (2 * J + 1) * q * coshNum q J * (q * dev q (BP (2 * i + 2)))
      ≤ sinhNum q J * dev q (AP (2 * i + 2))
  calc (2 * J + 1) * q * coshNum q J * (q * dev q (BP (2 * i + 2)))
      = (2 * J + 1) * (q * q * coshNum q J) * dev q (BP (2 * i + 2)) := by ring_nat
    _ ≤ sinhNum q J * dev q (AP (2 * i + 2)) := series_below_odd_core q hq i J

/-- The cut-level reading: the series fold reads `true` at every odd convergent,
    at every layer. -/
theorem coth_series_below_odd (q : Nat) (hq : 1 ≤ q) (i J : Nat) :
    (cothSeriesAb q hq).cut J (cfPn (cothCF q) (2 * i + 1))
      (cfQn (cothCF q) (2 * i + 1)) = true := by
  rw [cothSeriesCut_eq]
  exact decide_eq_true (series_le_odd q hq i J)

/-- Anchors: the tightest checked instance (`q = 1`, `i = 1`, `J = 3`):
    `T₃·q₃ = 7777·115 = 894355 ≤ 894373 = 5923·151 = s₃·p₃` — margin 18. -/
theorem series_le_odd_anchors :
    TNum 1 3 * cfQn (cothCF 1) 3 ≤ sinhNum 1 3 * cfPn (cothCF 1) 3
    ∧ TNum 1 3 = 7777 ∧ cfQn (cothCF 1) 3 = 115 ∧ sinhNum 1 3 = 5923
    ∧ cfPn (cothCF 1) 3 = 151 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## §6 — the choice function: a series `false` forces the CF limit `false`

The upper transfer at the **limit** level.  A strict series reading (`T_J > m/k`,
margin `≥ 1` in `Nat`) cannot coexist with *all* even convergents at-or-below
`m/k`: by `series_le_odd`, `m/k < T_J ≤ r_{2L+1}`, and the det-one floor makes the
odd–even gap at layer `L` exactly `1/(q_{2L}q_{2L+1})` — so once
`q_{2L}·q_{2L+1} > k·s_J` (the **choice function**, reached at
`L = k·s_J + k + 2` by the Fibonacci floor `q_n ≥ n`), the even convergent is
strictly past the probe and the CF limit reads `false`.  No measure, no LEM:
the schedule is explicit. -/

open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus
  (cothUnitCFCauchySeq cfEvenNum cfEvenDen cfQn_ge_self cfPn_pos)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut (cothSeriesAb)

private theorem le_of_add_le_add_left' {c a b : Nat} (h : c + a ≤ c + b) : a ≤ b :=
  E213.Tactic.NatHelper.le_of_add_le_add_left h

/-- ★★★★ **The squeeze**: a strict series reading at `(m, k)` together with
    `q_{2L}·q_{2L+1} > k·s_J` forces the layer-`L` even convergent strictly past
    the probe.  Chain: probe `< T_J ≤ r_{2L+1}` (`series_le_odd`), and the
    det-one floor `p_{2L+1}q_{2L} = p_{2L}q_{2L+1} + 1` converts the unit gap
    into the bound — were `r_{2L} ≤ m/k`, the gap `q_{2L}q_{2L+1} ≤ k·s_J`
    would follow, contradiction. -/
theorem even_past_probe (q : Nat) (hq : 1 ≤ q) (m k J L : Nat)
    (hser : sinhNum q J * m + 1 ≤ TNum q J * k)
    (hbig : k * sinhNum q J + 1
      ≤ cfQn (cothCF q) (2 * L) * cfQn (cothCF q) (2 * L + 1)) :
    cfQn (cothCF q) (2 * L) * m + 1 ≤ cfPn (cothCF q) (2 * L) * k := by
  rcases Nat.lt_or_ge (cfQn (cothCF q) (2 * L) * m) (cfPn (cothCF q) (2 * L) * k)
    with hlt | hge
  · exact hlt
  · exfalso
    have hU := series_le_odd q hq L J
    have hdet := cf_det_even_nat (cothCF q) L
    have key : sinhNum q J * m * (cfQn (cothCF q) (2*L) * cfQn (cothCF q) (2*L+1))
          + cfQn (cothCF q) (2*L) * cfQn (cothCF q) (2*L+1)
        ≤ sinhNum q J * m * (cfQn (cothCF q) (2*L) * cfQn (cothCF q) (2*L+1))
          + k * sinhNum q J := by
      calc sinhNum q J * m * (cfQn (cothCF q) (2*L) * cfQn (cothCF q) (2*L+1))
            + cfQn (cothCF q) (2*L) * cfQn (cothCF q) (2*L+1)
          = (sinhNum q J * m + 1)
            * (cfQn (cothCF q) (2*L) * cfQn (cothCF q) (2*L+1)) := by ring_nat
        _ ≤ TNum q J * k * (cfQn (cothCF q) (2*L) * cfQn (cothCF q) (2*L+1)) :=
            Nat.mul_le_mul hser (Nat.le_refl _)
        _ = k * cfQn (cothCF q) (2*L) * (TNum q J * cfQn (cothCF q) (2*L+1)) := by
            ring_nat
        _ ≤ k * cfQn (cothCF q) (2*L) * (sinhNum q J * cfPn (cothCF q) (2*L+1)) :=
            Nat.mul_le_mul_left _ hU
        _ = k * sinhNum q J * (cfPn (cothCF q) (2*L+1) * cfQn (cothCF q) (2*L)) := by
            ring_nat
        _ = k * sinhNum q J * (cfPn (cothCF q) (2*L) * cfQn (cothCF q) (2*L+1) + 1) := by
            rw [hdet]
        _ = sinhNum q J * cfQn (cothCF q) (2*L+1) * (cfPn (cothCF q) (2*L) * k)
            + k * sinhNum q J := by ring_nat
        _ ≤ sinhNum q J * cfQn (cothCF q) (2*L+1) * (cfQn (cothCF q) (2*L) * m)
            + k * sinhNum q J :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ hge) _
        _ = sinhNum q J * m * (cfQn (cothCF q) (2*L) * cfQn (cothCF q) (2*L+1))
            + k * sinhNum q J := by ring_nat
    have hqq : cfQn (cothCF q) (2*L) * cfQn (cothCF q) (2*L+1) ≤ k * sinhNum q J :=
      le_of_add_le_add_left' key
    exact Nat.not_succ_le_self _ (Nat.le_trans hbig hqq)

/-- ★★★★★ **A series `false` reading forces the CF limit `false`** — the upper
    transfer at the limit level, with the explicit choice layer
    `L = k·s_J + k + 2`.  Together with `series_le_odd` this is the closed upper
    half of the weld: the series fold can never exceed the Lambert real. -/
theorem cf_limit_false_of_series_false (q : Nat) (hq : 1 ≤ q) (m k J : Nat)
    (hser : (cothSeriesAb q hq).cut J m k = false) :
    (cothUnitCFCauchySeq q hq).limit m k = false := by
  cases k with
  | zero =>
    rw [(cothSeriesAb q hq).cut_resolution_zero J m] at hser
    exact Bool.noConfusion hser
  | succ k' =>
    rw [cothSeriesCut_eq] at hser
    have hser' : sinhNum q J * m + 1 ≤ TNum q J * (k' + 1) :=
      Nat.lt_of_not_le (of_decide_eq_false hser)
    have ha : ∀ i, 1 ≤ cothCF q (i + 1) := fun i => cothCF_pos q hq (i + 1)
    -- the choice layer
    have hbig : (k' + 1) * sinhNum q J + 1
        ≤ cfQn (cothCF q) (2 * ((k' + 1) * sinhNum q J + k' + 3))
          * cfQn (cothCF q) (2 * ((k' + 1) * sinhNum q J + k' + 3) + 1) := by
      have h2L : (k' + 1) * sinhNum q J + 1
          ≤ 2 * ((k' + 1) * sinhNum q J + k' + 3) := by
        refine Nat.le.intro (k := (k' + 1) * sinhNum q J + 2 * k' + 5) ?_
        ring_nat
      have hgrow := cfQn_ge_self (cothCF q) ha (2 * ((k' + 1) * sinhNum q J + k' + 3))
      have hone : 1 ≤ cfQn (cothCF q) (2 * ((k' + 1) * sinhNum q J + k' + 3) + 1) :=
        cfQn_pos (cothCF q) ha _
      calc (k' + 1) * sinhNum q J + 1
          ≤ 2 * ((k' + 1) * sinhNum q J + k' + 3) := h2L
        _ ≤ cfQn (cothCF q) (2 * ((k' + 1) * sinhNum q J + k' + 3)) := hgrow
        _ ≤ cfQn (cothCF q) (2 * ((k' + 1) * sinhNum q J + k' + 3))
            * cfQn (cothCF q) (2 * ((k' + 1) * sinhNum q J + k' + 3) + 1) :=
            Nat.le_mul_of_pos_right _ hone
    have hpast := even_past_probe q hq m (k' + 1) J
      ((k' + 1) * sinhNum q J + k' + 3) hser' hbig
    -- the layer-L cut reads false
    have hcsL : (cothUnitCFCauchySeq q hq).cs
        ((k' + 1) * sinhNum q J + k' + 3) m (k' + 1) = false := by
      apply decide_eq_false
      intro hcon
      exact Nat.not_succ_le_self _ (Nat.le_trans hpast hcon)
    -- transport to the modulus layer
    have heq := (cothUnitCFCauchySeq q hq).cauchy m (k' + 1) (k' + 1 + 2)
      ((k' + 1) * sinhNum q J + k' + 3)
      (Nat.le_refl _)
      (show (k' + 1) * sinhNum q J + k' + 3 ≥ k' + 1 + 2 from
        Nat.le_add_left (k' + 3) ((k' + 1) * sinhNum q J))
    show (cothUnitCFCauchySeq q hq).cs (k' + 1 + 2) m (k' + 1) = false
    rw [heq]
    exact hcsL

/-- The contrapositive packaging: wherever the CF limit reads `true`, the series
    fold reads `true` at **every** layer — the ∀-probe upper agreement
    (`two_pointings_agree`'s `3/2`-instance, now universal). -/
theorem series_true_of_cf_limit_true (q : Nat) (hq : 1 ≤ q) (m k : Nat)
    (hcf : (cothUnitCFCauchySeq q hq).limit m k = true) :
    ∀ J, (cothSeriesAb q hq).cut J m k = true := by
  intro J
  cases hs : (cothSeriesAb q hq).cut J m k with
  | true => rfl
  | false =>
    rw [cf_limit_false_of_series_false q hq m k J hs] at hcf
    exact Bool.noConfusion hcf

/-! ## §7 — the lower transfer: propagation, the `i = 0` instance, the matched base

The lower half (`r_{2i} ≤ T_J`) climbs for free: one `J`-step costs only the side
condition `devA ≤ 3·devB` (every even convergent sits below the first odd one),
so the whole family reduces to its **matched-truncation base** `J₀(i) = 2i + 1` —
the Padé phenomenon (the convergent matches the series to order `u^{2i}`, so the
cross deficit stays a `q`-cancelled sliver `(−5, −3, −1, …)` until exactly the
matched depth, then flips positive forever).  The `i = 0` instance closes
outright; the base family for `i ≥ 1` (`LowerBase`) is the isolated remaining
content of the weld, `decide`-verified on the accessible instances. -/

open E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpMoebius (det2_odd_nat)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionFloor (cfQn_pos)

/-- One `J`-step of the lower transfer: needs only `A ≤ 3B`. -/
theorem lower_step (q : Nat) {A B J : Nat} (hside : A ≤ 3 * B)
    (h : A * sinhNum q J ≤ (2 * J + 1) * B * coshNum q J) :
    A * sinhNum q (J + 1) ≤ (2 * (J + 1) + 1) * B * coshNum q (J + 1) := by
  show A * ((2 * J + 2) * (2 * J + 3) * q ^ 2 * sinhNum q J + 1)
      ≤ (2 * (J + 1) + 1) * B * ((2 * J + 1) * (2 * J + 2) * q ^ 2 * coshNum q J + 1)
  calc A * ((2 * J + 2) * (2 * J + 3) * q ^ 2 * sinhNum q J + 1)
      = (2 * J + 2) * (2 * J + 3) * q ^ 2 * (A * sinhNum q J) + A := by ring_nat
    _ ≤ (2 * J + 2) * (2 * J + 3) * q ^ 2 * ((2 * J + 1) * B * coshNum q J) + A :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ h) A
    _ ≤ (2 * J + 2) * (2 * J + 3) * q ^ 2 * ((2 * J + 1) * B * coshNum q J)
        + 3 * B := Nat.add_le_add_left hside _
    _ ≤ (2 * J + 2) * (2 * J + 3) * q ^ 2 * ((2 * J + 1) * B * coshNum q J)
        + (2 * J + 3) * B :=
        Nat.add_le_add_left (Nat.mul_le_mul_right B (Nat.le_add_left 3 (2 * J))) _
    _ = (2 * (J + 1) + 1) * B
        * ((2 * J + 1) * (2 * J + 2) * q ^ 2 * coshNum q J + 1) := by ring_nat

/-- The lower transfer propagates from any base layer. -/
theorem lower_of_base (q : Nat) {A B J0 : Nat} (hside : A ≤ 3 * B)
    (hbase : A * sinhNum q J0 ≤ (2 * J0 + 1) * B * coshNum q J0) :
    ∀ J, J0 ≤ J → A * sinhNum q J ≤ (2 * J + 1) * B * coshNum q J := by
  intro J hJ
  obtain ⟨t, rfl⟩ := Nat.le.dest hJ
  clear hJ
  induction t with
  | zero => exact hbase
  | succ s ih => exact lower_step q hside ih

/-- The odd convergents descend below the first one (`mono_of_step` on the
    reciprocal system, fed by the odd two-step determinant). -/
theorem odd_le_first (q : Nat) (hq : 1 ≤ q) (i : Nat) :
    cfPn (cothCF q) (2 * i + 1) * cfQn (cothCF q) 1
      ≤ cfPn (cothCF q) 1 * cfQn (cothCF q) (2 * i + 1) := by
  have ha : ∀ j, 1 ≤ cothCF q (j + 1) := fun j => cothCF_pos q hq (j + 1)
  have h := E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus.mono_of_step
    (a := fun L => cfQn (cothCF q) (2 * L + 1))
    (d := fun L => cfPn (cothCF q) (2 * L + 1))
    (fun L => Nat.mul_pos (cfQn_pos (cothCF q) ha (2 * L + 1))
      (cfPn_pos (cothCF q) (cothCF_pos q hq) (2 * L + 1)))
    (fun n => by
      show cfQn (cothCF q) (2 * n + 1) * cfPn (cothCF q) (2 * (n + 1) + 1)
          ≤ cfQn (cothCF q) (2 * (n + 1) + 1) * cfPn (cothCF q) (2 * n + 1)
      calc cfQn (cothCF q) (2 * n + 1) * cfPn (cothCF q) (2 * (n + 1) + 1)
          = cfPn (cothCF q) (2 * n + 3) * cfQn (cothCF q) (2 * n + 1) :=
            Nat.mul_comm _ _
        _ ≤ cfPn (cothCF q) (2 * n + 3) * cfQn (cothCF q) (2 * n + 1)
            + cothCF q (2 * n + 3) := Nat.le_add_right _ _
        _ = cfPn (cothCF q) (2 * n + 1) * cfQn (cothCF q) (2 * n + 3) :=
            (det2_odd_nat (cothCF q) n).symm
        _ = cfQn (cothCF q) (2 * (n + 1) + 1) * cfPn (cothCF q) (2 * n + 1) :=
            Nat.mul_comm _ _)
    0 i (Nat.zero_le i)
  calc cfPn (cothCF q) (2 * i + 1) * cfQn (cothCF q) 1
      = cfQn (cothCF q) (2 * 0 + 1) * cfPn (cothCF q) (2 * i + 1) := by
        rw [Nat.mul_comm]
    _ ≤ cfQn (cothCF q) (2 * i + 1) * cfPn (cothCF q) (2 * 0 + 1) := h
    _ = cfPn (cothCF q) 1 * cfQn (cothCF q) (2 * i + 1) := by rw [Nat.mul_comm]

/-- Every even convergent sits below the first odd one (chain the adjacent
    det-one step through the odd pivot). -/
theorem even_le_first_odd (q : Nat) (hq : 1 ≤ q) (i : Nat) :
    cfPn (cothCF q) (2 * i) * cfQn (cothCF q) 1
      ≤ cfQn (cothCF q) (2 * i) * cfPn (cothCF q) 1 := by
  have ha : ∀ j, 1 ≤ cothCF q (j + 1) := fun j => cothCF_pos q hq (j + 1)
  refine ratio_chain (u := cfPn (cothCF q) (2 * i + 1))
    (v := cfQn (cothCF q) (2 * i + 1)) ?_ ?_ (cfQn_pos (cothCF q) ha (2 * i + 1))
  · refine Nat.le.intro (k := 1) ?_
    rw [Nat.mul_comm (cfQn (cothCF q) (2 * i)) (cfPn (cothCF q) (2 * i + 1))]
    exact (cf_det_even_nat (cothCF q) i).symm
  · calc cfPn (cothCF q) (2 * i + 1) * cfQn (cothCF q) 1
        ≤ cfPn (cothCF q) 1 * cfQn (cothCF q) (2 * i + 1) := odd_le_first q hq i
      _ = cfQn (cothCF q) (2 * i + 1) * cfPn (cothCF q) 1 := Nat.mul_comm _ _

/-- The side condition at the `dev` level: `devA ≤ 3·devB` at every odd index. -/
theorem devA_le_three_devB (q : Nat) (hq : 1 ≤ q) (i : Nat) :
    dev q (AP (2 * i + 1)) ≤ 3 * dev q (BP (2 * i + 1)) := by
  have h := even_le_first_odd q hq i
  rw [(cf_bridge q i).1, (cf_bridge q i).2.2.1] at h
  -- h : q·devA·q₁ ≤ devB·p₁ with q₁ = 3q, p₁ = 3q·q + 1 (surface forms)
  have h2 : 3 * (q * q) * dev q (AP (2 * i + 1))
      ≤ 3 * (q * q) * (3 * dev q (BP (2 * i + 1))) := by
    have hqq : 1 ≤ q * q := by
      calc 1 = 1 * 1 := rfl
        _ ≤ q * q := Nat.mul_le_mul hq hq
    calc 3 * (q * q) * dev q (AP (2 * i + 1))
        = q * dev q (AP (2 * i + 1)) * ((2 * 1 + 1) * q) := by ring_nat
      _ ≤ dev q (BP (2 * i + 1)) * ((2 * 1 + 1) * q * ((2 * 0 + 1) * q) + 1) := h
      _ = (3 * (q * q) + 1) * dev q (BP (2 * i + 1)) := by ring_nat
      _ ≤ (3 * (q * q) + 6 * (q * q)) * dev q (BP (2 * i + 1)) :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left
            (Nat.le_trans hqq (Nat.le_mul_of_pos_left (q * q) (by decide))) _)
      _ = 3 * (q * q) * (3 * dev q (BP (2 * i + 1))) := by ring_nat
  exact Nat.le_of_mul_le_mul_left h2
    (Nat.lt_of_lt_of_le (by decide)
      (Nat.le_mul_of_pos_right 3 (Nat.lt_of_lt_of_le (by decide)
        (Nat.mul_le_mul hq hq))))

/-- The `i = 0` lower transfer, closed outright: `s_J ≤ (2J+1)·c_J` at every `J`
    (the fold never drops below the zeroth convergent `r₀ = q`). -/
theorem lower_zero (q : Nat) : ∀ J, sinhNum q J ≤ (2 * J + 1) * coshNum q J := by
  intro J
  have h := lower_of_base q (A := 1) (B := 1) (J0 := 0)
    (by decide) (Nat.le_refl _) J (Nat.zero_le J)
  calc sinhNum q J = 1 * sinhNum q J := (Nat.one_mul _).symm
    _ ≤ (2 * J + 1) * 1 * coshNum q J := h
    _ = (2 * J + 1) * coshNum q J := by rw [Nat.mul_one]

/-- **The matched-truncation lower base** — the weld's one remaining brick: at
    `J₀(i) = 2i + 1` (and only from there) the truncated series captures the
    `2i`-th convergent.  The cross deficit below `J₀` is an exact `q`-cancelled
    sliver (level 3: `−5, −3, −1`, `q`-independent; level 5: `−(315q²+14), …,
    −(51q²+6)`) — the Padé matching of `Ã/B̃` to order `u^{2i}`; the flip at the
    matched depth is `decide`-verified on the accessible instances
    (`lower_base_anchors`) and open in general. -/
def LowerBase (q : Nat) : Prop :=
  ∀ i, dev q (AP (2 * i + 1)) * sinhNum q (2 * i + 1)
    ≤ (2 * (2 * i + 1) + 1) * dev q (BP (2 * i + 1)) * coshNum q (2 * i + 1)

/-! ## §10 — the lower-cross recursion backbone (toward `LowerBase`)

The quantity `R_J := (2J+1)·dB·c_J − dA·s_J` (with `dA = devA`, `dB = devB`,
`c = coshNum`, `s = sinhNum`) is the `LowerBase` cross: `LowerBase q ⟺ ∀ i,
R_{2i+1}(i) ≥ 0`.  Two structural facts close everything **except** the base
`R_{2i+1}(i) ≥ 0`:

  * the **linear recursion** `R_{J+1} = (2J+2)(2J+3)q²·R_J + E_{J+1}`, where
    `E_j := (2j+1)·dB − dA` — direct from the `coshNum`/`sinhNum` recursions
    (`R_recursion` below, subtraction-free form);
  * **`E_j ≥ 0` for `j ≥ 1`** (`E_nonneg`), since `dA ≤ 3·dB ≤ (2j+1)·dB`
    (`devA_le_three_devB`).

So `R_J` is nondecreasing-into-positivity past the matched depth, and the whole
`LowerBase` family reduces to the single base inequality `R_{2i+1}(i) ≥ 0`.
That base is the Padé-matched flip: by the **master identity**
`Σ_{s} (2N+1)!/(2N−2s+1)!·((2N−2s+1)·bpF n s − apF n s) = (−1)^{n−1}2^n N!/(N−n)!`
(`n = 2i+1`), the leading term of `R_{2i+1}(i)` is exactly the diagonal value
`L(2i+1, 2i+1) = (4i+2)!!` at `q^{2i}`, and the lower-order boundary terms are
dominated (geometric-halving style).  The master identity and the full bridge
are proven: `LambertMasterId` + `LambertBridge.lowerBase`
(`theory/math/analysis/lambert_weld.md`). -/

/-- ★★★ **The lower-cross linear recursion** (subtraction-free): for arbitrary
    `dA, dB`,
    `(2J+3)·dB·c_{J+1} + (2J+2)(2J+3)q²·(dA·s_J) + dA
       = (2J+2)(2J+3)q²·((2J+1)·dB·c_J) + (2J+3)·dB + dA·s_{J+1}` —
    i.e. `R_{J+1} = (2J+2)(2J+3)q²·R_J + ((2J+3)dB − dA)`, straight from the
    `coshNum`/`sinhNum` recursions. -/
theorem R_recursion (q J dA dB : Nat) :
    (2 * J + 3) * dB * coshNum q (J + 1)
        + (2 * J + 2) * (2 * J + 3) * q ^ 2 * (dA * sinhNum q J) + dA
      = (2 * J + 2) * (2 * J + 3) * q ^ 2 * ((2 * J + 1) * dB * coshNum q J)
        + (2 * J + 3) * dB + dA * sinhNum q (J + 1) := by
  show (2 * J + 3) * dB * ((2 * J + 1) * (2 * J + 2) * q ^ 2 * coshNum q J + 1)
        + (2 * J + 2) * (2 * J + 3) * q ^ 2 * (dA * sinhNum q J) + dA
      = (2 * J + 2) * (2 * J + 3) * q ^ 2 * ((2 * J + 1) * dB * coshNum q J)
        + (2 * J + 3) * dB
        + dA * ((2 * J + 2) * (2 * J + 3) * q ^ 2 * sinhNum q J + 1)
  ring_nat

/-- ★★★ **`E_j ≥ 0` for `j ≥ 1`**: `dev (AP (2i+1)) ≤ (2j+1)·dev (BP (2i+1))`
    (the lower-cross forcing term is nonnegative past the head) — from
    `devA_le_three_devB` and `3 ≤ 2j+1`. -/
theorem E_nonneg (q : Nat) (hq : 1 ≤ q) (i j : Nat) (hj : 1 ≤ j) :
    dev q (AP (2 * i + 1)) ≤ (2 * j + 1) * dev q (BP (2 * i + 1)) := by
  have h3 : 3 ≤ 2 * j + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 hj) 1
  exact Nat.le_trans (devA_le_three_devB q hq i) (Nat.mul_le_mul_right _ h3)

/-- The master-identity diagonal value, machine-checked at level `n = N = 3`
    (`i = 1`): the moved (subtraction-free) form
    `W(3,0)·7·bpF 3 0 + W(3,1)·5·bpF 3 1 = 48 + W(3,0)·apF 3 0 + W(3,1)·apF 3 1`
    (`315 = 48 + 315 − 48`), i.e. `L(3,3) = 48 = 6!!` — the leading coefficient of
    `R_3(1) = 48q² + 1`. -/
theorem master_diagonal_anchor :
    1 * (7 * bpF 3 0) + 42 * (5 * bpF 3 1) = 48 + 1 * apF 3 0 + 42 * apF 3 1 := by
  decide

/-- The base family holds on the accessible instances (`q = 1`: levels 3, 5, 7 with
    margins 49, 3911, 655502; `q = 2`: level 3, margin 193). -/
theorem lower_base_anchors :
    dev 1 (AP 3) * sinhNum 1 3 ≤ 7 * dev 1 (BP 3) * coshNum 1 3
    ∧ dev 1 (AP 5) * sinhNum 1 5 ≤ 11 * dev 1 (BP 5) * coshNum 1 5
    ∧ dev 2 (AP 3) * sinhNum 2 3 ≤ 7 * dev 2 (BP 3) * coshNum 2 3
    ∧ dev 1 (AP 7) * sinhNum 1 7 ≤ 15 * dev 1 (BP 7) * coshNum 1 7 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- ★★★★ **The lower transfer, reduced to its base**: given `LowerBase q`, the
    series sits above every even convergent from the matched depth on. -/
theorem series_ge_even_of_base (q : Nat) (hq : 1 ≤ q) (hbase : LowerBase q)
    (i J : Nat) (hJ : 2 * i + 1 ≤ J) :
    cfPn (cothCF q) (2 * i) * sinhNum q J ≤ cfQn (cothCF q) (2 * i) * TNum q J := by
  have h := lower_of_base q (devA_le_three_devB q hq i) (hbase i) J hJ
  rw [(cf_bridge q i).1, (cf_bridge q i).2.2.1]
  show q * dev q (AP (2 * i + 1)) * sinhNum q J
      ≤ dev q (BP (2 * i + 1)) * ((2 * J + 1) * q * coshNum q J)
  calc q * dev q (AP (2 * i + 1)) * sinhNum q J
      = q * (dev q (AP (2 * i + 1)) * sinhNum q J) := by ring_nat
    _ ≤ q * ((2 * J + 1) * dev q (BP (2 * i + 1)) * coshNum q J) :=
        Nat.mul_le_mul_left q h
    _ = dev q (BP (2 * i + 1)) * ((2 * J + 1) * q * coshNum q J) := by ring_nat

/-! ## §8 — the weld, conditional on the base: limit-cut equality and completion

`W1` (§6, unconditional) and `W2` (below, from the base) compose into the
separation schedule `I k = 2(k+2) + 1`: any series `false` shows at `I k`.  The
series fold then completes through `AbCutSeq.toCauchySep`, and its limit agrees
with the Lambert CF limit on **every** probe — the weld.  The entire remaining
content is `LowerBase`. -/

open E213.Lib.Math.NumberSystems.Real213.RateModulus (rcut)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus
  (cfEvenNum cfEvenDen)
open E213.Meta.Nat.NatRing213 (nat_mul_lt_mul_left)
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)

/-- `W2` (conditional): a `false` CF limit forces the series `false` at the
    explicit layer `2(k+2)+1` — the modulus-layer even convergent is strictly
    past the probe, and from the matched depth the series has caught it. -/
theorem series_false_of_cf_limit_false (q : Nat) (hq : 1 ≤ q)
    (hbase : LowerBase q) (m k : Nat)
    (hcf : (cothUnitCFCauchySeq q hq).limit m k = false) :
    (cothSeriesAb q hq).cut (2 * (k + 2) + 1) m k = false := by
  have hcf' : rcut (cfEvenNum (cothCF q)) (cfEvenDen (cothCF q)) (k + 2) m k
      = false := hcf
  have hlt : cfQn (cothCF q) (2 * (k + 2)) * m
      < cfPn (cothCF q) (2 * (k + 2)) * k :=
    Nat.lt_of_not_le (of_decide_eq_false hcf')
  have hT := series_ge_even_of_base q hq hbase (k + 2) (2 * (k + 2) + 1)
    (Nat.le_refl _)
  rw [cothSeriesCut_eq]
  apply decide_eq_false
  intro hcon
  have hs1 : 1 ≤ sinhNum q (2 * (k + 2) + 1) :=
    E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut.sinhNum_pos q _
  have hcycle : cfQn (cothCF q) (2 * (k + 2)) * (TNum q (2 * (k + 2) + 1) * k)
      < cfQn (cothCF q) (2 * (k + 2)) * (TNum q (2 * (k + 2) + 1) * k) := by
    calc cfQn (cothCF q) (2 * (k + 2)) * (TNum q (2 * (k + 2) + 1) * k)
        ≤ cfQn (cothCF q) (2 * (k + 2)) * (sinhNum q (2 * (k + 2) + 1) * m) :=
          Nat.mul_le_mul_left _ hcon
      _ = sinhNum q (2 * (k + 2) + 1) * (cfQn (cothCF q) (2 * (k + 2)) * m) := by
          ring_nat
      _ < sinhNum q (2 * (k + 2) + 1) * (cfPn (cothCF q) (2 * (k + 2)) * k) :=
          nat_mul_lt_mul_left hs1 hlt
      _ = cfPn (cothCF q) (2 * (k + 2)) * sinhNum q (2 * (k + 2) + 1) * k := by
          ring_nat
      _ ≤ cfQn (cothCF q) (2 * (k + 2)) * TNum q (2 * (k + 2) + 1) * k :=
          Nat.mul_le_mul_right k hT
      _ = cfQn (cothCF q) (2 * (k + 2)) * (TNum q (2 * (k + 2) + 1) * k) := by
          ring_nat
  exact absurd hcycle (Nat.lt_irrefl _)

/-- ★★★★★ **The weld, conditional on the base**: the coth series fold completes
    through the separation schedule `I k = 2(k+2)+1` — the schedule's
    certificate is `W2 ∘ W1`, both halves of the order transfer composed. -/
def cothSeriesCauchySepOfBase (q : Nat) (hq : 1 ≤ q) (hbase : LowerBase q) :
    CauchyCutSeq :=
  (cothSeriesAb q hq).toCauchySep (fun k => 2 * (k + 2) + 1)
    (fun m k _ i hf =>
      series_false_of_cf_limit_false q hq hbase m k
        (cf_limit_false_of_series_false q hq m k i hf))

/-- ★★★★★ **Limit-cut equality**: the completed series fold and the Lambert CF
    fold agree on **every** probe — `coth(1/q)`'s two pointings (series and
    continued fraction) are one real.  Stated against an arbitrary `LowerBase`
    witness; `LambertBridge.lowerBase` supplies it for every `q ≥ 1`
    (`LambertBridge.weld_closed` is the hypothesis-free form). -/
theorem weld_limit_agreement (q : Nat) (hq : 1 ≤ q) (hbase : LowerBase q)
    (m k : Nat) :
    (cothSeriesCauchySepOfBase q hq hbase).limit m k
      = (cothUnitCFCauchySeq q hq).limit m k := by
  cases hcf : (cothUnitCFCauchySeq q hq).limit m k with
  | true =>
    show (cothSeriesAb q hq).cut (2 * (k + 2) + 1) m k = true
    exact series_true_of_cf_limit_true q hq m k hcf _
  | false =>
    show (cothSeriesAb q hq).cut (2 * (k + 2) + 1) m k = false
    exact series_false_of_cf_limit_false q hq hbase m k hcf

/-! ## §9 — the weld Casoratian: lower cross and upper margin are det-one coupled

Write `R_J := (2J+1)·devB·c_J − devA·s_J` (the lower cross, `LowerBase`'s
quantity) and `M_J := P·s_J − (2J+1)q²·Q·c_J` (the upper `(U)`-margin), with
`devA/devB` the level-`2i+1` and `P/Q` the level-`2i+2` evaluations.  The pair
`(R_J, M_J)` evolves across levels `i` by **unimodular** steps, so its
truncation-Casoratian `R_{J+1}M_J − R_JM_{J+1}` is level-independent — and
equals the `tcross_id` quantity `K_J = (2J+3)c_{J+1}s_J − (2J+1)c_Js_{J+1}`.
Below in subtraction-free form (`X + K-cross = Y`): the proof is bilinearity
plus one firing of the det-one floor (`dev_cross_det`).  Consequences (the
blueprint's flip criterion): `K_J > |R_J|·M_{J+1} ⟹ R_{J+1} > 0`. -/

open E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut (tcross_id)

/-- ★★★★ **The weld Casoratian** (subtraction-free): with
    `X = RL·ML' + RR·MR' + RL'·MR + RR'·ML` and
    `Y = RL·MR' + RR·ML' + RL'·ML + RR'·MR` (primes = truncation `J+1`),
    `X + (2J+3)c_{J+1}s_J = Y + (2J+1)c_Js_{J+1}` — i.e.
    `R_{J+1}·M_J = R_J·M_{J+1} + K_J` over `ℤ`.  One det-one firing. -/
theorem weld_casoratian (q : Nat) (i J : Nat) :
    (2*J+1) * dev q (BP (2*i+1)) * coshNum q J
        * (dev q (AP (2*i+2)) * sinhNum q (J+1))
      + dev q (AP (2*i+1)) * sinhNum q J
        * ((2*J+3) * (q*q) * dev q (BP (2*i+2)) * coshNum q (J+1))
      + (2*J+3) * dev q (BP (2*i+1)) * coshNum q (J+1)
        * ((2*J+1) * (q*q) * dev q (BP (2*i+2)) * coshNum q J)
      + dev q (AP (2*i+1)) * sinhNum q (J+1)
        * (dev q (AP (2*i+2)) * sinhNum q J)
      + (2*J+3) * coshNum q (J+1) * sinhNum q J
    = (2*J+1) * dev q (BP (2*i+1)) * coshNum q J
        * ((2*J+3) * (q*q) * dev q (BP (2*i+2)) * coshNum q (J+1))
      + dev q (AP (2*i+1)) * sinhNum q J
        * (dev q (AP (2*i+2)) * sinhNum q (J+1))
      + (2*J+3) * dev q (BP (2*i+1)) * coshNum q (J+1)
        * (dev q (AP (2*i+2)) * sinhNum q J)
      + dev q (AP (2*i+1)) * sinhNum q (J+1)
        * ((2*J+1) * (q*q) * dev q (BP (2*i+2)) * coshNum q J)
      + (2*J+1) * coshNum q J * sinhNum q (J+1) := by
  have hdet : dev q (AP (2*i+2)) * dev q (BP (2*i+1))
      = q * q * dev q (AP (2*i+1)) * dev q (BP (2*i+2)) + 1 := by
    calc dev q (AP (2*i+2)) * dev q (BP (2*i+1))
        = q * dev q (AP (2*i+1)) * (q * dev q (BP (2*i+2))) + 1 :=
          (dev_cross_det q i).symm
      _ = q * q * dev q (AP (2*i+1)) * dev q (BP (2*i+2)) + 1 := by ring_nat
  have h1 : (2*J+1) * (coshNum q J * sinhNum q (J+1))
        * (dev q (AP (2*i+2)) * dev q (BP (2*i+1)))
      = (2*J+1) * (coshNum q J * sinhNum q (J+1))
        * (q * q * dev q (AP (2*i+1)) * dev q (BP (2*i+2)) + 1) := by
    rw [hdet]
  have h2 : (2*J+3) * (coshNum q (J+1) * sinhNum q J)
        * (dev q (AP (2*i+2)) * dev q (BP (2*i+1)))
      = (2*J+3) * (coshNum q (J+1) * sinhNum q J)
        * (q * q * dev q (AP (2*i+1)) * dev q (BP (2*i+2)) + 1) := by
    rw [hdet]
  calc (2*J+1) * dev q (BP (2*i+1)) * coshNum q J
          * (dev q (AP (2*i+2)) * sinhNum q (J+1))
        + dev q (AP (2*i+1)) * sinhNum q J
          * ((2*J+3) * (q*q) * dev q (BP (2*i+2)) * coshNum q (J+1))
        + (2*J+3) * dev q (BP (2*i+1)) * coshNum q (J+1)
          * ((2*J+1) * (q*q) * dev q (BP (2*i+2)) * coshNum q J)
        + dev q (AP (2*i+1)) * sinhNum q (J+1)
          * (dev q (AP (2*i+2)) * sinhNum q J)
        + (2*J+3) * coshNum q (J+1) * sinhNum q J
      = (2*J+1) * (coshNum q J * sinhNum q (J+1))
          * (dev q (AP (2*i+2)) * dev q (BP (2*i+1)))
        + (2*J+3) * (coshNum q (J+1) * sinhNum q J)
          * (q * q * dev q (AP (2*i+1)) * dev q (BP (2*i+2)) + 1)
        + ((2*J+1) * (2*J+3) * (q*q) * dev q (BP (2*i+1)) * dev q (BP (2*i+2))
            * coshNum q J * coshNum q (J+1)
          + dev q (AP (2*i+1)) * dev q (AP (2*i+2))
            * sinhNum q J * sinhNum q (J+1)) := by ring_nat
    _ = (2*J+1) * (coshNum q J * sinhNum q (J+1))
          * (q * q * dev q (AP (2*i+1)) * dev q (BP (2*i+2)) + 1)
        + (2*J+3) * (coshNum q (J+1) * sinhNum q J)
          * (dev q (AP (2*i+2)) * dev q (BP (2*i+1)))
        + ((2*J+1) * (2*J+3) * (q*q) * dev q (BP (2*i+1)) * dev q (BP (2*i+2))
            * coshNum q J * coshNum q (J+1)
          + dev q (AP (2*i+1)) * dev q (AP (2*i+2))
            * sinhNum q J * sinhNum q (J+1)) := by rw [h1, ← h2]
    _ = (2*J+1) * dev q (BP (2*i+1)) * coshNum q J
          * ((2*J+3) * (q*q) * dev q (BP (2*i+2)) * coshNum q (J+1))
        + dev q (AP (2*i+1)) * sinhNum q J
          * (dev q (AP (2*i+2)) * sinhNum q (J+1))
        + (2*J+3) * dev q (BP (2*i+1)) * coshNum q (J+1)
          * (dev q (AP (2*i+2)) * sinhNum q J)
        + dev q (AP (2*i+1)) * sinhNum q (J+1)
          * ((2*J+1) * (q*q) * dev q (BP (2*i+2)) * coshNum q J)
        + (2*J+1) * coshNum q J * sinhNum q (J+1) := by ring_nat

/-! ## §10 — the named ℤ Casoratian and the flip criterion

`weld_casoratian` is the subtraction-free `ℕ` shadow.  Over `ℤ` the same fact is the
clean unimodular recurrence the docstring names: with the lower cross `R_J` and the
upper margin `M_J` as honest signed quantities, `R_{J+1}·M_J = R_J·M_{J+1} + K_J`.
This is the foothold every consequence pivots on; the first is the **flip criterion**
(blueprint Discovery 1): once the Casoratian constant dominates the signed lower
contribution and the margin is positive, the next lower cross is forced positive. -/

open E213.Meta.Int213.Order
open E213.Meta.Int213.OrderMul

/-- The **lower cross** `R_J(i) = (2J+1)·devB_i·c_J − devA_i·s_J` over `ℤ` (`LowerBase`'s
    quantity, now signed — it may be negative before the flip). -/
def weldR (q i J : Nat) : Int :=
  (2 * (J : Int) + 1) * (dev q (BP (2*i+1)) : Int) * (coshNum q J : Int)
    - (dev q (AP (2*i+1)) : Int) * (sinhNum q J : Int)

/-- The **upper margin** `M_J(i) = P·s_J − (2J+1)q²·Q·c_J` over `ℤ`
    (`P = devA_{i+½}`, `Q = devB_{i+½}` at level `2i+2`). -/
def weldM (q i J : Nat) : Int :=
  (dev q (AP (2*i+2)) : Int) * (sinhNum q J : Int)
    - (2 * (J : Int) + 1) * ((q : Int) * (q : Int)) * (dev q (BP (2*i+2)) : Int)
        * (coshNum q J : Int)

/-- The **Casoratian constant** `K_J = (2J+3)·c_{J+1}·s_J − (2J+1)·c_J·s_{J+1}` over `ℤ`
    (the level-independent truncation-Casoratian of the pair `(R, M)`). -/
def weldK (q J : Nat) : Int :=
  (2 * (J : Int) + 3) * (coshNum q (J+1) : Int) * (sinhNum q J : Int)
    - (2 * (J : Int) + 1) * (coshNum q J : Int) * (sinhNum q (J+1) : Int)

/-- ★★★★★ **The weld Casoratian, named over `ℤ`**: `R_{J+1}·M_J = R_J·M_{J+1} + K_J`.
    One firing of the det-one floor (`dev_cross_det`, cast to `ℤ`): the whole
    difference factors as `K_J · (detpair − detval)`, and the floor makes the second
    factor vanish.  The clean unimodular recurrence behind the subtraction-free
    `weld_casoratian`. -/
theorem weld_casoratian_int (q i J : Nat) :
    weldR q i (J+1) * weldM q i J = weldR q i J * weldM q i (J+1) + weldK q J := by
  -- the det-one floor, cast to ℤ
  have hdetI : (dev q (AP (2*i+2)) : Int) * (dev q (BP (2*i+1)) : Int)
      = (q : Int) * (q : Int) * (dev q (AP (2*i+1)) : Int) * (dev q (BP (2*i+2)) : Int) + 1 := by
    have hc : (↑(dev q (AP (2*i+2)) * dev q (BP (2*i+1))) : Int)
        = ↑(q * dev q (AP (2*i+1)) * (q * dev q (BP (2*i+2))) + 1) :=
      congrArg Int.ofNat (dev_cross_det q i).symm
    rw [Int.ofNat_mul, Int.ofNat_add, Int.ofNat_one, Int.ofNat_mul, Int.ofNat_mul,
        Int.ofNat_mul] at hc
    rw [hc]; ring_intZ
  -- `ring_intZ` reads `↑(J+1)` and `↑J` as unrelated atoms; bridge the successor coefficient
  have hsucc : ((J + 1 : Nat) : Int) = (J : Int) + 1 := rfl
  -- the difference factors through the floor; the floor kills it
  have key : weldR q i (J+1) * weldM q i J - (weldR q i J * weldM q i (J+1) + weldK q J)
      = weldK q J * ((dev q (AP (2*i+2)) : Int) * (dev q (BP (2*i+1)) : Int)
          - ((q : Int) * (q : Int) * (dev q (AP (2*i+1)) : Int) * (dev q (BP (2*i+2)) : Int) + 1)) := by
    unfold weldR weldM weldK; rw [hsucc]; ring_intZ
  -- the floor `detpair = detval` collapses the factor (avoiding `ring_intZ`'s `·0`/`0+` blind spot)
  have hzero : weldR q i (J+1) * weldM q i J - (weldR q i J * weldM q i (J+1) + weldK q J) = 0 := by
    rw [key, hdetI, E213.Meta.Int213.Order.sub_self_zero, E213.Meta.Int213.PolyIntM.mul_zeroZ]
  -- `A − (B+C) = 0 ⟹ A = B + C` (the descent rearrangement, `int_eq_of_add_neg`)
  have hgoal := int_eq_of_add_neg
    (show weldR q i (J+1) * weldM q i J + -(weldR q i J * weldM q i (J+1) + weldK q J) = 0
      from hzero)
  rw [Int.add_zero] at hgoal
  exact hgoal

/-- `0 < x·c` with `0 < c` forces `0 < x` (right cancellation of a positive factor). -/
private theorem pos_of_mul_pos_right {x c : Int} (h : 0 < x * c) (hc : 0 < c) : 0 < x := by
  have hle : (0 : Int) ≤ x := by
    refine le_of_mul_le_mul_right_pos ?_ hc
    rw [E213.Meta.Int213.zero_mul]; exact le_of_lt h
  rcases pos_zero_or_neg x with hx | hx | hx
  · exact hx
  · rw [hx, E213.Meta.Int213.zero_mul] at h; exact absurd h (int_lt_irrefl 0)
  · exact absurd hle (not_le_of_lt hx)

/-- `0 ≤ x·c` with `0 < c` forces `0 ≤ x` (non-strict right cancellation). -/
private theorem nonneg_of_mul_nonneg_right {x c : Int} (h : 0 ≤ x * c) (hc : 0 < c) : 0 ≤ x := by
  refine le_of_mul_le_mul_right_pos ?_ hc
  rw [E213.Meta.Int213.zero_mul]; exact h

/-- ★★★★ **The flip criterion** (blueprint Discovery 1, signed form).  If the upper
    margin is positive (`0 < M_J`) and the Casoratian constant outweighs the signed
    lower contribution (`−(R_J·M_{J+1}) < K_J`), then the next lower cross is positive
    (`0 < R_{J+1}`).  Sign-flip forcing straight from `weld_casoratian_int`:
    `R_{J+1}·M_J = R_J·M_{J+1} + K_J > 0`, then cancel the positive `M_J`.

    (The blueprint's `K_J > |R_J|·M_{J+1}` is the `0 ≤ M_{J+1}` specialisation, since
    `−R_J ≤ |R_J|`; this signed form is sharper and hypothesis-free in the sign of `R_J`.) -/
theorem weld_flip_criterion (q i J : Nat) (hMJ : 0 < weldM q i J)
    (hdom : - (weldR q i J * weldM q i (J+1)) < weldK q J) :
    0 < weldR q i (J+1) := by
  have hpos : 0 < weldR q i (J+1) * weldM q i J := by
    rw [weld_casoratian_int]
    have h1 : (0 : Int) < weldK q J - (-(weldR q i J * weldM q i (J+1))) := sub_pos_of_lt hdom
    rw [show weldK q J - (-(weldR q i J * weldM q i (J+1)))
          = weldR q i J * weldM q i (J+1) + weldK q J from by ring_intZ] at h1
    exact h1
  exact pos_of_mul_pos_right hpos hMJ

/-- The Casoratian constant is non-negative: `0 ≤ K_J`.  This is exactly the truncated-coth
    monotonicity `t_mono` (`(2J+1)·c_J·s_{J+1} ≤ (2J+3)·c_{J+1}·s_J`) cast to `ℤ`. -/
theorem weldK_nonneg (q J : Nat) : 0 ≤ weldK q J := by
  -- cast each `ℕ` triple product into the atom-form `weldK` uses
  have cast3 : ∀ (X c s : Nat), (↑(X * c * s) : Int) = (X : Int) * (c : Int) * (s : Int) := by
    intro X c s; rw [Int.ofNat_mul, Int.ofNat_mul]
  have hcoef3 : ((2 * J + 3 : Nat) : Int) = 2 * (J : Int) + 3 := by
    rw [Int.ofNat_add, Int.ofNat_mul]; rfl
  have hcoef1 : ((2 * J + 1 : Nat) : Int) = 2 * (J : Int) + 1 := by
    rw [Int.ofNat_add, Int.ofNat_mul]; rfl
  have e : weldK q J = ((2*J+3) * coshNum q (J+1) * sinhNum q J : Nat)
                     - ((2*J+1) * coshNum q J * sinhNum q (J+1) : Nat) := by
    unfold weldK
    rw [cast3 (2*J+3) (coshNum q (J+1)) (sinhNum q J),
        cast3 (2*J+1) (coshNum q J) (sinhNum q (J+1)),
        hcoef3, hcoef1]
  rw [e]
  exact le_zero_of_nonneg (sub_nonneg_of_le
    (ofNat_le_of_le (E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut.t_mono q J)))

/-- The upper margin is non-negative: `0 ≤ M_J`.  This is exactly `series_below_odd_core`
    (`(2J+1)·q²·c_J·Q ≤ s_J·P`, the upper half of the weld's order transfer) cast to `ℤ` — an
    **elementary** fact (cross-`le` + the det-one floor `dev_cross_det`), not the `LambertBridge`
    budget machinery.  So one of the two inputs to `weld_lowerbase_propagate` is bridge-free; the
    residual independence question is its *strictness* `0 < M_J` and the base `0 < R_0`. -/
theorem weldM_nonneg (q : Nat) (hq : 1 ≤ q) (i J : Nat) : 0 ≤ weldM q i J := by
  have hcoef1 : ((2 * J + 1 : Nat) : Int) = 2 * (J : Int) + 1 := by
    rw [Int.ofNat_add, Int.ofNat_mul]; rfl
  have e : weldM q i J
      = (↑(sinhNum q J * dev q (AP (2*i+2))) : Int)
        - ↑((2 * J + 1) * (q * q * coshNum q J) * dev q (BP (2*i+2))) := by
    unfold weldM
    rw [Int.ofNat_mul, Int.ofNat_mul, Int.ofNat_mul, Int.ofNat_mul, Int.ofNat_mul, hcoef1]
    ring_intZ
  rw [e]
  exact le_zero_of_nonneg (sub_nonneg_of_le (ofNat_le_of_le (series_below_odd_core q hq i J)))

/-! ### The det-floor resolves the margin's near-cancellation (the `R`–`sinh` Wronskian)

The upper margin `M_J = P·s_J − (2J+1)q²·Q·c_J` is a **small near-cancellation** (`M_0 = P − q²Q`
with `q²Q ≈ P`).  The det-one floor (`dev_cross_det`: `P·devB = q²·devA·Q + 1`) resolves it
*exactly* into the explicit sinh sequence:

  `M_J · devB = s_J − q²·Q·R_J`   (`weldM_devB`),

and substituting into the Casoratian collapses the `q²Q·R_J R_{J+1}` cross-terms, leaving the
**`M`-free Wronskian of the lower cross and `sinh`**:

  `R_{J+1}·s_J − R_J·s_{J+1} = devB·K_J`   (`weld_rs_wronskian`).

So the lower cross `R` and the *explicit* sinh numerator form a Casoratian pair with multiplier
`devB·K_J` — a cleaner spine than the `M`-margin view, and the structural reason `M > 0` is free
pre-flip (`s_J > q²Q·R_J` whenever `R_J ≤ 0`). -/

/-- ★★★★ **The margin is the det-floor residue against `sinh`**: `M_J·devB = s_J − q²·Q·R_J`.
    Resolves the `M`-near-cancellation exactly (one firing of `dev_cross_det`). -/
theorem weldM_devB (q i J : Nat) :
    weldM q i J * (dev q (BP (2*i+1)) : Int)
      = (sinhNum q J : Int)
        - (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i J := by
  have hdetI : (dev q (AP (2*i+2)) : Int) * (dev q (BP (2*i+1)) : Int)
      = (q : Int) * (q : Int) * (dev q (AP (2*i+1)) : Int) * (dev q (BP (2*i+2)) : Int) + 1 := by
    have hc : (↑(dev q (AP (2*i+2)) * dev q (BP (2*i+1))) : Int)
        = ↑(q * dev q (AP (2*i+1)) * (q * dev q (BP (2*i+2))) + 1) :=
      congrArg Int.ofNat (dev_cross_det q i).symm
    rw [Int.ofNat_mul, Int.ofNat_add, Int.ofNat_one, Int.ofNat_mul, Int.ofNat_mul,
        Int.ofNat_mul] at hc
    rw [hc]; ring_intZ
  have key : weldM q i J * (dev q (BP (2*i+1)) : Int)
        - ((sinhNum q J : Int) - (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i J)
      = (sinhNum q J : Int)
        * ((dev q (AP (2*i+2)) : Int) * (dev q (BP (2*i+1)) : Int)
           - ((q : Int) * (q : Int) * (dev q (AP (2*i+1)) : Int) * (dev q (BP (2*i+2)) : Int) + 1)) := by
    unfold weldM weldR; ring_intZ
  have hzero : weldM q i J * (dev q (BP (2*i+1)) : Int)
        - ((sinhNum q J : Int) - (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i J) = 0 := by
    rw [key, hdetI, E213.Meta.Int213.Order.sub_self_zero, E213.Meta.Int213.PolyIntM.mul_zeroZ]
  have hgoal := int_eq_of_add_neg
    (show weldM q i J * (dev q (BP (2*i+1)) : Int)
        + -((sinhNum q J : Int) - (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i J) = 0
      from hzero)
  rw [Int.add_zero] at hgoal
  exact hgoal

/-- ★★★★★ **The cosh companion of `weldM_devB`** — the det-floor *unimodular transform*.
    `(2J+1)·c_J = P·R_J + devA·M_J`.  With `weldM_devB` (`s_J = q²Q·R_J + devB·M_J`) this exhibits
    the **convergent/series pair** `(s_J, (2J+1)·c_J)` as the image of the **residual pair**
    `(R_J, M_J)` under the CF-determinant matrix `[[q²Q, devB],[P, devA]]`, whose determinant is
    `q²Q·devA − P·devB = −1` (the det-one floor `dev_cross_det`) — *unimodular*.  Consequence: the
    three Wronskians (`weld_rs_wronskian` R·sinh, `weldM_s_wronskian` M·sinh, `weldM_wronskian`
    M·cosh) are **one** Casoratian `K_J` (`weld_casoratian_int`, the `[R,M]` step-determinant) read
    in the two bases; the coupling constants `devB, q²Q, P` are exactly the transform's entries. -/
theorem weld_cosh_RM (q i J : Nat) :
    (2 * (J : Int) + 1) * (coshNum q J : Int)
      = (dev q (AP (2*i+2)) : Int) * weldR q i J + (dev q (AP (2*i+1)) : Int) * weldM q i J := by
  have hdetI : (dev q (AP (2*i+2)) : Int) * (dev q (BP (2*i+1)) : Int)
      = (q : Int) * (q : Int) * (dev q (AP (2*i+1)) : Int) * (dev q (BP (2*i+2)) : Int) + 1 := by
    have hc : (↑(dev q (AP (2*i+2)) * dev q (BP (2*i+1))) : Int)
        = ↑(q * dev q (AP (2*i+1)) * (q * dev q (BP (2*i+2))) + 1) :=
      congrArg Int.ofNat (dev_cross_det q i).symm
    rw [Int.ofNat_mul, Int.ofNat_add, Int.ofNat_one, Int.ofNat_mul, Int.ofNat_mul,
        Int.ofNat_mul] at hc
    rw [hc]; ring_intZ
  have key : (2 * (J : Int) + 1) * (coshNum q J : Int)
        - ((dev q (AP (2*i+2)) : Int) * weldR q i J + (dev q (AP (2*i+1)) : Int) * weldM q i J)
      = (coshNum q J : Int) * (2 * (J : Int) + 1)
        * (((q : Int) * (q : Int) * (dev q (AP (2*i+1)) : Int) * (dev q (BP (2*i+2)) : Int) + 1)
           - (dev q (AP (2*i+2)) : Int) * (dev q (BP (2*i+1)) : Int)) := by
    unfold weldR weldM; ring_intZ
  have hzero : (2 * (J : Int) + 1) * (coshNum q J : Int)
        - ((dev q (AP (2*i+2)) : Int) * weldR q i J + (dev q (AP (2*i+1)) : Int) * weldM q i J) = 0 := by
    rw [key, hdetI, E213.Meta.Int213.Order.sub_self_zero, E213.Meta.Int213.PolyIntM.mul_zeroZ]
  have hgoal := int_eq_of_add_neg
    (show (2 * (J : Int) + 1) * (coshNum q J : Int)
        + -((dev q (AP (2*i+2)) : Int) * weldR q i J + (dev q (AP (2*i+1)) : Int) * weldM q i J) = 0
      from hzero)
  rw [Int.add_zero] at hgoal
  exact hgoal

/-- ★★★★★ **The `R`–`sinh` Wronskian** (`M`-free): `R_{J+1}·s_J − R_J·s_{J+1} = devB·K_J`.  The
    lower cross and the explicit sinh numerator are a Casoratian pair — the det-floor having
    eliminated the upper margin and its near-cancellation.  Derived from `weld_casoratian_int`
    and `weldM_devB` (the `q²Q·R_J·R_{J+1}` cross-terms cancel). -/
theorem weld_rs_wronskian (q i J : Nat) :
    weldR q i (J+1) * (sinhNum q J : Int) - weldR q i J * (sinhNum q (J+1) : Int)
      = (dev q (BP (2*i+1)) : Int) * weldK q J := by
  have es : (sinhNum q J : Int)
      = weldM q i J * (dev q (BP (2*i+1)) : Int)
        + (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i J := by
    rw [weldM_devB]; ring_intZ
  have es1 : (sinhNum q (J+1) : Int)
      = weldM q i (J+1) * (dev q (BP (2*i+1)) : Int)
        + (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i (J+1) := by
    rw [weldM_devB]; ring_intZ
  rw [es, es1,
      show weldR q i (J+1)
            * (weldM q i J * (dev q (BP (2*i+1)) : Int)
               + (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i J)
          - weldR q i J
            * (weldM q i (J+1) * (dev q (BP (2*i+1)) : Int)
               + (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i (J+1))
          = (dev q (BP (2*i+1)) : Int) * (weldR q i (J+1) * weldM q i J)
            - (dev q (BP (2*i+1)) : Int) * (weldR q i J * weldM q i (J+1)) from by ring_intZ,
      weld_casoratian_int]
  ring_intZ

/-- ★★★★ **The margin–sinh Wronskian** (the third Casoratian pair): `s_{J+1}·M_J − s_J·M_{J+1}
    = q²·Q·K_J`.  From `weldM_devB` (substituting `s = M·devB + q²Q·R`) the `devB·M·M` terms cancel
    and the residue is `q²Q·(R_{J+1}·M_J − R_J·M_{J+1}) = q²Q·K_J` (`weld_casoratian_int`).  Its
    rearrangement `(M_J − M_{J+1})·s_J = q²Q·K_J − (s_{J+1}−s_J)·M_J` shows `M`-monotonicity
    (`M_{J+1} ≤ M_J`) is **equivalent** to `(s_{J+1}−s_J)·M_J ≤ q²Q·K_J` — exact, but self-referential
    (no ring discharge); the antitone fact itself is a separate quantitative induction. -/
theorem weldM_s_wronskian (q i J : Nat) :
    (sinhNum q (J+1) : Int) * weldM q i J - (sinhNum q J : Int) * weldM q i (J+1)
      = (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldK q J := by
  have es : (sinhNum q J : Int)
      = weldM q i J * (dev q (BP (2*i+1)) : Int)
        + (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i J := by
    rw [weldM_devB]; ring_intZ
  have es1 : (sinhNum q (J+1) : Int)
      = weldM q i (J+1) * (dev q (BP (2*i+1)) : Int)
        + (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i (J+1) := by
    rw [weldM_devB]; ring_intZ
  rw [es, es1,
      show (weldM q i (J+1) * (dev q (BP (2*i+1)) : Int)
              + (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i (J+1)) * weldM q i J
          - (weldM q i J * (dev q (BP (2*i+1)) : Int)
              + (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i J) * weldM q i (J+1)
          = (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * (weldR q i (J+1) * weldM q i J)
            - (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * (weldR q i J * weldM q i (J+1))
          from by ring_intZ,
      weld_casoratian_int]
  ring_intZ

/-- ★★★★ **The margin Wronskian** (`M`-side, pure ring — no det-floor):
    `(2J+3)·c_{J+1}·M_J − (2J+1)·c_J·M_{J+1} = P·K_J`.  The `q²Q·c·c` terms cancel identically;
    the margin `M` and `cosh` are a Casoratian pair with the same source `K_J` (scaled by `P`),
    mirroring the `R`–sinh Wronskian.  Identity "(W)" toward `Core`. -/
theorem weldM_wronskian (q i J : Nat) :
    (2 * (J : Int) + 3) * (coshNum q (J+1) : Int) * weldM q i J
      - (2 * (J : Int) + 1) * (coshNum q J : Int) * weldM q i (J+1)
    = (dev q (AP (2*i+2)) : Int) * weldK q J := by
  have hsucc : ((J + 1 : Nat) : Int) = (J : Int) + 1 := rfl
  unfold weldM weldK
  rw [hsucc]; ring_intZ

/-- ★★★★★ **The master bilinear Casoratian** (pure ℤ ring — the one identity behind *all* weld
    Wronskians).  For any constants `a₁ a₂ b₁ b₂` and any pair `(x_J, y_J)` with step values
    `x0,x1,y0,y1`, the cross-determinant of the two linear combinations `X = a₁x+a₂y`,
    `Y = b₁x+b₂y` is the `(a₁b₂−a₂b₁)`-multiple of the pair's own Casoratian `x1·y0 − x0·y1`:

      `(a₁x1+a₂y1)(b₁x0+b₂y0) − (a₁x0+a₂y0)(b₁x1+b₂y1) = (a₁b₂−a₂b₁)(x1·y0 − x0·y1)`.

    With the **weight-normalized cosh** `ĉ_J := (2J+1)c_J`, the weld's clean pair is `(ĉ, s)` and
    `K_J = ĉ_{J+1}s_J − ĉ_J s_{J+1}` (= `weldK`, the `q²`-cancelled Casoratian).  `R_J = devB·ĉ_J −
    devA·s_J` and `M_J = −q²Q·ĉ_J + P·s_J` are constant-coefficient combinations of that one pair, so
    **every** residual cross is `det(coeff-rows)·K_J`: `R×ĉ = devA·K`, `R×s = devB·K`, `M×ĉ = P·K`,
    `M×s = q²Q·K`, and `R×M = (P·devB − q²·devA·Q)·K = 1·K` — the last coupling being the **det-one
    floor** (`dev_cross_det`), the unimodularity that makes `weld_casoratian_int`'s RHS *exactly*
    `K_J` with no lower-order correction.  This single ring identity subsumes `weld_casoratian_int`,
    `weld_rs_wronskian`, `weldM_s_wronskian`, `weldM_wronskian` (and the once-"anomalous" `R×c`,
    clean as `R×ĉ`).  Classical underpinning: the CF-convergent matrix is unimodular; the genuinely
    213-native content is the weight `ĉ` collapsing all crosses to one bilinear, with the `+1`
    residue unit as the determinant. -/
theorem weld_bilinear_casoratian (a₁ a₂ b₁ b₂ x0 x1 y0 y1 : Int) :
    (a₁ * x1 + a₂ * y1) * (b₁ * x0 + b₂ * y0) - (a₁ * x0 + a₂ * y0) * (b₁ * x1 + b₂ * y1)
      = (a₁ * b₂ - a₂ * b₁) * (x1 * y0 - x0 * y1) := by
  ring_intZ

/-! ### The weld is one instance of the master bilinear (coth in the `(ĉ, s)` basis)

The coth weld is `weld_bilinear_casoratian` specialized to the normalized pair `(ĉ, s)` and the
unimodular coefficient rows.  The same `weld_bilinear_casoratian` applies to **any** CF-vs-series
weld — `exp(2/q)`, `tan(1/q)`, any holonomic ratio — once its normalized pair and (constant) CF
coefficient rows are supplied; only the *coupling* `a₁b₂−a₂b₁` changes (it is the CF determinant,
`= 1` for coth's unimodular convergents, `= 2·a_n` for the `exp(2/q)` Möbius fold). -/

/-- The **weight-normalized cosh** `ĉ_J = (2J+1)·c_J` — the slot making `(ĉ, s)` the weld's clean
    Casoratian pair. -/
def weldCh (q J : Nat) : Int := (2 * (J : Int) + 1) * (coshNum q J : Int)

/-- `R_J = devB·ĉ_J + (−devA)·s_J` in the normalized basis. -/
theorem weldR_basis (q i J : Nat) :
    weldR q i J = (dev q (BP (2*i+1)) : Int) * weldCh q J
      + (-(dev q (AP (2*i+1)) : Int)) * (sinhNum q J : Int) := by
  unfold weldR weldCh; ring_intZ

/-- `M_J = (−q²Q)·ĉ_J + P·s_J` in the normalized basis. -/
theorem weldM_basis (q i J : Nat) :
    weldM q i J = (-((q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int))) * weldCh q J
      + (dev q (AP (2*i+2)) : Int) * (sinhNum q J : Int) := by
  unfold weldM weldCh; ring_intZ

/-- `K_J = ĉ_{J+1}·s_J − ĉ_J·s_{J+1}` — the Casoratian of the normalized pair `(ĉ, s)`. -/
theorem weldK_basis (q J : Nat) :
    weldK q J = weldCh q (J+1) * (sinhNum q J : Int) - weldCh q J * (sinhNum q (J+1) : Int) := by
  have hsucc : ((J + 1 : Nat) : Int) = (J : Int) + 1 := rfl
  unfold weldK weldCh; rw [hsucc]; ring_intZ

/-- ★★★★★ **The weld Casoratian as a bilinear instance** (the unification, as a theorem).
    `R_{J+1}·M_J − R_J·M_{J+1} = K_J` follows from `weld_bilinear_casoratian` with rows
    `R = (devB, −devA)`, `M = (−q²Q, P)` against the pair `(ĉ, s)`: the coupling
    `devB·P − (−devA)(−q²Q) = P·devB − q²·devA·Q` equals `1` by the det-one floor
    (`dev_cross_det`), so the cross is exactly `K_J`. -/
theorem weld_casoratian_bilinear (q i J : Nat) :
    weldR q i (J+1) * weldM q i J - weldR q i J * weldM q i (J+1) = weldK q J := by
  rw [weldR_basis q i (J+1), weldR_basis q i J, weldM_basis q i J, weldM_basis q i (J+1),
      weld_bilinear_casoratian (dev q (BP (2*i+1)) : Int) (-(dev q (AP (2*i+1)) : Int))
        (-((q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int))) (dev q (AP (2*i+2)) : Int)
        (weldCh q J) (weldCh q (J+1)) (sinhNum q J : Int) (sinhNum q (J+1) : Int),
      ← weldK_basis]
  -- coupling = P·devB − q²·devA·Q = 1 (det-one floor)
  have hdetI : (dev q (AP (2*i+2)) : Int) * (dev q (BP (2*i+1)) : Int)
      = (q : Int) * (q : Int) * (dev q (AP (2*i+1)) : Int) * (dev q (BP (2*i+2)) : Int) + 1 := by
    have hc : (↑(dev q (AP (2*i+2)) * dev q (BP (2*i+1))) : Int)
        = ↑(q * dev q (AP (2*i+1)) * (q * dev q (BP (2*i+2))) + 1) :=
      congrArg Int.ofNat (dev_cross_det q i).symm
    rw [Int.ofNat_mul, Int.ofNat_add, Int.ofNat_one, Int.ofNat_mul, Int.ofNat_mul,
        Int.ofNat_mul] at hc
    rw [hc]; ring_intZ
  rw [show (dev q (BP (2*i+1)) : Int) * (dev q (AP (2*i+2)) : Int)
        - -(dev q (AP (2*i+1)) : Int) * -((q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int))
        = 1 from by
      rw [show (dev q (BP (2*i+1)) : Int) * (dev q (AP (2*i+2)) : Int)
            = (dev q (AP (2*i+2)) : Int) * (dev q (BP (2*i+1)) : Int) from by ring_intZ, hdetI]
      ring_intZ,
    E213.Meta.Int213.PolyIntM.one_mulZ]

/-- ★★★★★ **`LowerBase` reduces to a single `M`-free inequality** (cleanest form, via the
    `R`–sinh Wronskian).  `0 ≤ R_{J+1}` follows from the *single* inequality
    `(−R_J)·s_{J+1} ≤ devB·K_J` and `sinh > 0` (trivial) — no `M`, no ratio descent.
    Directly from `weld_rs_wronskian` (`R_{J+1}·s_J = R_J·s_{J+1} + devB·K_J`): the right side
    is `≥ 0` by the hypothesis, and `s_J > 0` cancels.  At `J = 2i` this is the bridge-free
    last-step certificate of `LowerBase`, stated in the explicit sinh sequence. -/
theorem weld_lowerbase_reduction_rs (q i J : Nat)
    (hsingle : -(weldR q i J) * (sinhNum q (J+1) : Int) ≤ (dev q (BP (2*i+1)) : Int) * weldK q J) :
    0 ≤ weldR q i (J+1) := by
  have hsJ : (0 : Int) < (sinhNum q J : Int) :=
    ofNat_le_of_le (E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut.sinhNum_pos q J)
  have h1 : 0 ≤ weldR q i (J+1) * (sinhNum q J : Int) := by
    have heq : weldR q i (J+1) * (sinhNum q J : Int)
        = weldR q i J * (sinhNum q (J+1) : Int) + (dev q (BP (2*i+1)) : Int) * weldK q J := by
      have hw := weld_rs_wronskian q i J
      rw [show weldR q i (J+1) * (sinhNum q J : Int)
            = (weldR q i (J+1) * (sinhNum q J : Int) - weldR q i J * (sinhNum q (J+1) : Int))
              + weldR q i J * (sinhNum q (J+1) : Int) from by ring_intZ, hw]
      ring_intZ
    rw [heq]
    have h2 := sub_nonneg_of_le hsingle
    rw [show (dev q (BP (2*i+1)) : Int) * weldK q J - -(weldR q i J) * (sinhNum q (J+1) : Int)
          = weldR q i J * (sinhNum q (J+1) : Int) + (dev q (BP (2*i+1)) : Int) * weldK q J
          from by ring_intZ] at h2
    exact le_zero_of_nonneg h2
  exact nonneg_of_mul_nonneg_right h1 hsJ

/-- ★★★ **The single descent step** (unconditional): `R_J·M_{J+1} ≤ R_{J+1}·M_J`.  From
    `weld_casoratian_int` (`R_{J+1}·M_J = R_J·M_{J+1} + K_J`) and `0 ≤ K_J` (`weldK_nonneg`):
    the cross strictly cannot *fall* — the ratio `R/M` climbs (pre-flip, with `R < 0`, this is
    the magnitude `|R|` *descending*). -/
theorem weld_descent_step (q i J : Nat) :
    weldR q i J * weldM q i (J+1) ≤ weldR q i (J+1) * weldM q i J := by
  rw [weld_casoratian_int]
  have h := add_le_add_left (weldK_nonneg q J) (weldR q i J * weldM q i (J+1))
  rwa [Int.add_zero] at h

/-- ★★★★ **Ratio descent** (blueprint Discovery 1, telescoped, any anchor `J₀`): with positive
    margins (`0 < M_j` for every `j`), the climbing single step telescopes forward to
    `R_{J₀}·M_{J₀+d} ≤ R_{J₀+d}·M_{J₀}` — the ratio `R/M` is non-decreasing.  At `J₀ = 0`
    (pre-flip, `R < 0`) this reads `|R_d|·M_0 ≤ |R_0|·M_d`, a magnitude descent.  Each rung
    chains `weld_descent_step` through the positive margins (`mul`-monotonicity up, `M`-cancel
    down). -/
theorem weld_ratio_descent (q i : Nat) (hM : ∀ j, 0 < weldM q i j) (J0 : Nat) :
    ∀ d, weldR q i J0 * weldM q i (J0 + d) ≤ weldR q i (J0 + d) * weldM q i J0 := by
  intro d
  induction d with
  | zero => exact le_refl _
  | succ d ih =>
    have ih' := mul_le_mul_right_nonneg ih (weldM q i (J0+d+1)) (le_of_lt (hM (J0+d+1)))
    have step' := mul_le_mul_right_nonneg (weld_descent_step q i (J0+d)) (weldM q i J0)
      (le_of_lt (hM J0))
    have chain : weldR q i J0 * weldM q i (J0+d+1) * weldM q i (J0+d)
               ≤ weldR q i (J0+d+1) * weldM q i J0 * weldM q i (J0+d) := by
      rw [show weldR q i J0 * weldM q i (J0+d+1) * weldM q i (J0+d)
            = weldR q i J0 * weldM q i (J0+d) * weldM q i (J0+d+1) from by ring_intZ,
          show weldR q i (J0+d+1) * weldM q i J0 * weldM q i (J0+d)
            = weldR q i (J0+d+1) * weldM q i (J0+d) * weldM q i J0 from by ring_intZ]
      refine le_trans ih' (le_trans ?_ step')
      rw [show weldR q i (J0+d) * weldM q i J0 * weldM q i (J0+d+1)
            = weldR q i (J0+d) * weldM q i (J0+d+1) * weldM q i J0 from by ring_intZ]
      exact le_refl _
    exact le_of_mul_le_mul_right_pos chain (hM (J0+d))

/-- ★★★★ **Forward positivity persistence.**  Once the lower cross is positive at some
    truncation `J₀` (`0 < R_{J₀}`) and the margins stay positive, it is positive at every later
    truncation `J₀ + d` — the climbing ratio cannot return below `0`.  `0 < R_{J₀}·M_{J₀+d} ≤
    R_{J₀+d}·M_{J₀}` (`weld_ratio_descent`), then cancel `M_{J₀}`.

    **Note (why this is *not* a bridge-free `LowerBase`):** `LowerBase` is `0 ≤ R_{2i+1}`, and the
    cross starts *negative* — `R_0 = dev(BP_{2i+1}) − dev(AP_{2i+1}) ≤ 0` (`= 0` at `i=0`, `< 0`
    for `i ≥ 1`; checked by evaluation).  So persistence has no positive anchor at `J₀ = 0`; a
    bridge-free `LowerBase` would still have to certify that the climbing ratio reaches `≥ 0`
    *by* `J = 2i+1` — the quantitative flip-timing that is exactly the `LambertBridge` content.
    Persistence + the flip criterion are the structural half (the cross, once non-negative, stays
    so); the quantitative half stays open (item 3). -/
theorem weld_positivity_persists (q i : Nat) (hM : ∀ j, 0 < weldM q i j) (J0 : Nat)
    (hR : 0 < weldR q i J0) : ∀ d, 0 < weldR q i (J0 + d) := by
  intro d
  have h0 : 0 < weldR q i J0 * weldM q i (J0+d) := mul_pos hR (hM (J0+d))
  have h1 : 0 < weldR q i (J0+d) * weldM q i J0 :=
    lt_of_lt_of_le h0 (weld_ratio_descent q i hM J0 d)
  exact pos_of_mul_pos_right h1 (hM J0)

/-- ★★★★★ **`LowerBase` reduces to a single last-step inequality** (the empirically-discovered
    flip structure, item 3 sharpened).  The lower cross flips from negative to non-negative at
    **one** step `J → J+1` (evaluation shows it flips at exactly `J = 2i`, the last step before
    `N = 2i+1`).  So `LowerBase`'s content `0 ≤ R_{J+1}` follows — **bridge-free** — from positive
    margins plus the *single* inequality

      `(−R_0)·M_J·M_{J+1} ≤ K_J·M_0`.

    Proof: ratio descent (`R_0·M_J ≤ R_J·M_0`, free) scaled by `M_{J+1}`, the single inequality
    (`0 ≤ R_0·M_J·M_{J+1} + K_J·M_0`), and the Casoratian (`R_{J+1}·M_J = R_J·M_{J+1} + K_J`)
    assemble to `0 ≤ M_0·(R_{J+1}·M_J)`; cancel the positive `M_0·M_J`.  This is the flip
    criterion run at the last step — no `LambertBridge` machinery.  It converts the open item 3
    from "reach `≥ 0` by `J = 2i+1`" (the whole telescoped sum) into **one** ℤ-native inequality,
    which holds with large slack in every evaluated case (`i ≤ 3`): the genuine, localized residue
    is `(−R_0)·M_{2i}·M_{2i+1} ≤ K_{2i}·M_0` (`K_{2i}` is factorially large; `−R_0`, the `M`'s are
    comparatively small). -/
theorem weld_lowerbase_reduction (q i J : Nat) (hM : ∀ j, 0 < weldM q i j)
    (hsingle : -(weldR q i 0) * (weldM q i J * weldM q i (J+1)) ≤ weldK q J * weldM q i 0) :
    0 ≤ weldR q i (J+1) := by
  -- ratio descent at anchor 0, scaled by the non-negative margin `M_{J+1}`
  have hrd : weldR q i 0 * weldM q i J ≤ weldR q i J * weldM q i 0 := by
    have h := weld_ratio_descent q i hM 0 J; rwa [Nat.zero_add] at h
  have hi : weldR q i 0 * weldM q i J * weldM q i (J+1)
          ≤ weldR q i J * weldM q i 0 * weldM q i (J+1) :=
    mul_le_mul_right_nonneg hrd (weldM q i (J+1)) (le_of_lt (hM (J+1)))
  -- the single inequality, rearranged to `0 ≤ R_0·M_J·M_{J+1} + K_J·M_0`
  have hLHS : 0 ≤ weldR q i 0 * weldM q i J * weldM q i (J+1) + weldK q J * weldM q i 0 := by
    have h := sub_nonneg_of_le hsingle
    rw [show weldK q J * weldM q i 0 - -(weldR q i 0) * (weldM q i J * weldM q i (J+1))
          = weldR q i 0 * weldM q i J * weldM q i (J+1) + weldK q J * weldM q i 0 from by ring_intZ] at h
    exact le_zero_of_nonneg h
  -- add `K_J·M_0` across the descent, chain past `0`
  have h2 : 0 ≤ weldR q i J * weldM q i 0 * weldM q i (J+1) + weldK q J * weldM q i 0 :=
    le_trans hLHS (add_le_add_right hi (weldK q J * weldM q i 0))
  -- the right side is `R_{J+1}·(M_0·M_J)` by the Casoratian
  have h3 : weldR q i J * weldM q i 0 * weldM q i (J+1) + weldK q J * weldM q i 0
          = weldR q i (J+1) * (weldM q i 0 * weldM q i J) := by
    rw [show weldR q i J * weldM q i 0 * weldM q i (J+1) + weldK q J * weldM q i 0
          = weldM q i 0 * (weldR q i J * weldM q i (J+1) + weldK q J) from by ring_intZ,
        ← weld_casoratian_int q i J]
    ring_intZ
  rw [h3] at h2
  -- cancel the positive `M_0·M_J`
  exact nonneg_of_mul_nonneg_right h2 (mul_pos (hM 0) (hM J))

/-- ★★★★★ **`LowerBase` ⟸ {M-monotonicity, Core}** (theorem-backed).  Given positive margins,
    `0 < q²Q`, the margin non-increasing to the flip (`M_{2i} ≤ M_0`), and the localized **Core**
    inequality `M_0·devB·M_{2i+1} ≤ q²·Q·K_{2i}`, the lower cross is non-negative at the flip:
    `0 ≤ R_{2i+1}` (= `LowerBase`).  (No `R_0 ≤ 0` needed — the det-floor identity carries the sign.)

    Mechanism: the det-floor residue at `J=0` (`weldM_devB`: `M_0·devB = 1 − q²Q·R_0`) gives
    `q²Q·(−R_0) = M_0·devB − 1`; then `(−R_0)·M_{2i}·M_{2i+1}·q²Q = (M_0·devB−1)·M_{2i}·M_{2i+1}
    ≤ M_0·devB·M_{2i}·M_{2i+1} ≤ M_0·devB·M_0·M_{2i+1} = (M_0·devB·M_{2i+1})·M_0 ≤ (q²Q·K)·M_0`
    (using `M_{2i} ≤ M_0` and `Core`), and cancelling `q²Q > 0` is exactly the master single
    inequality `weld_lowerbase_reduction` consumes.  Localizes `LowerBase`'s open content to the
    two quantitative residuals M-monotonicity and Core (both bridge-equivalent). -/
theorem weld_lowerbase_of_core (q i : Nat) (hM : ∀ j, 0 < weldM q i j)
    (hqQ : 0 < (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int))
    (hmono : weldM q i (2*i) ≤ weldM q i 0)
    (hcore : weldM q i 0 * (dev q (BP (2*i+1)) : Int) * weldM q i (2*i+1)
             ≤ (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldK q (2*i)) :
    0 ≤ weldR q i (2*i+1) := by
  have hM0  : (0 : Int) ≤ weldM q i 0        := le_of_lt (hM 0)
  have hM2i1 : (0 : Int) ≤ weldM q i (2*i+1) := le_of_lt (hM (2*i+1))
  -- det-floor residue: `M_0·devB = 1 − q²Q·R_0`
  have hR : weldM q i 0 * (dev q (BP (2*i+1)) : Int)
          = 1 - (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i 0 := by
    have h := weldM_devB q i 0
    rwa [show (sinhNum q 0 : Int) = 1 from rfl] at h
  -- `0 ≤ M_0·devB`
  have hM0dB : (0 : Int) ≤ weldM q i 0 * (dev q (BP (2*i+1)) : Int) := by
    have h := mul_le_mul_right_nonneg hM0 (dev q (BP (2*i+1)) : Int) (Int.ofNat_nonneg _)
    rwa [E213.Meta.Int213.zero_mul] at h
  -- `M_0·devB·(M_{2i}·M_{2i+1}) ≤ (q²Q·K)·M_0`  (via `M_{2i} ≤ M_0` then `Core ×M_0`)
  have hbig : weldM q i 0 * (dev q (BP (2*i+1)) : Int) * (weldM q i (2*i) * weldM q i (2*i+1))
            ≤ ((q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldK q (2*i)) * weldM q i 0 := by
    refine le_trans (mul_le_mul_left_nonneg
      (mul_le_mul_right_nonneg hmono (weldM q i (2*i+1)) hM2i1)
      (weldM q i 0 * (dev q (BP (2*i+1)) : Int)) hM0dB) ?_
    rw [show weldM q i 0 * (dev q (BP (2*i+1)) : Int) * (weldM q i 0 * weldM q i (2*i+1))
          = (weldM q i 0 * (dev q (BP (2*i+1)) : Int) * weldM q i (2*i+1)) * weldM q i 0 from by ring_intZ]
    exact mul_le_mul_right_nonneg hcore (weldM q i 0) hM0
  -- assemble the master single inequality, then cancel `q²Q`
  apply weld_lowerbase_reduction q i (2*i) hM
  refine le_of_mul_le_mul_right_pos
    (c := (q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int)) ?_ hqQ
  rw [show -(weldR q i 0) * (weldM q i (2*i) * weldM q i (2*i+1))
          * ((q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int))
        = (weldM q i 0 * (dev q (BP (2*i+1)) : Int) - 1)
          * (weldM q i (2*i) * weldM q i (2*i+1)) from by
      rw [show (weldM q i 0 * (dev q (BP (2*i+1)) : Int) - 1)
            = -((q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldR q i 0) from by
          rw [hR]; ring_intZ]; ring_intZ,
      show weldK q (2*i) * weldM q i 0 * ((q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int))
        = ((q : Int) * (q : Int) * (dev q (BP (2*i+2)) : Int) * weldK q (2*i)) * weldM q i 0 from by
      ring_intZ]
  -- now: `(M_0·devB−1)·(M_{2i}·M_{2i+1}) ≤ (q²Q·K)·M_0`  — subtract the nonneg `M_{2i}·M_{2i+1}`
  refine le_trans ?_ hbig
  rw [show (weldM q i 0 * (dev q (BP (2*i+1)) : Int) - 1) * (weldM q i (2*i) * weldM q i (2*i+1))
        = weldM q i 0 * (dev q (BP (2*i+1)) : Int) * (weldM q i (2*i) * weldM q i (2*i+1))
          - weldM q i (2*i) * weldM q i (2*i+1) from by ring_intZ]
  apply le_of_sub_nonneg
  rw [show weldM q i 0 * (dev q (BP (2*i+1)) : Int) * (weldM q i (2*i) * weldM q i (2*i+1))
        - (weldM q i 0 * (dev q (BP (2*i+1)) : Int) * (weldM q i (2*i) * weldM q i (2*i+1))
           - weldM q i (2*i) * weldM q i (2*i+1))
        = weldM q i (2*i) * weldM q i (2*i+1) from by ring_intZ]
  exact nonneg_of_le_zero (le_of_lt (mul_pos (hM (2*i)) (hM (2*i+1))))

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertOrder
