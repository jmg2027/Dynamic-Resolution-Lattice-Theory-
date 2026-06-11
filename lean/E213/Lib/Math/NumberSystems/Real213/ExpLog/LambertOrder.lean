import E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut
import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMinor
import E213.Meta.Nat.PolyNatMTactic

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

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertOrder
