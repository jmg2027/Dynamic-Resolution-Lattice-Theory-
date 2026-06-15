import E213.Lib.Math.NumberTheory.MobiusDivisorSum

/-!
# Möbius inversion for `muStruct` (∅-axiom)

★★★ Completes the Möbius framework for the structural Möbius `muStruct`:

  `mobius_inversion (f g) (n) (0<n) (hg : ∀m>0, g m = Σ_{e∣m} f e) :`
  `    f n = Σ_{d∣n} muStruct d · g (n/d)`

  `mobius_inversion_g (f) (n) (0<n) :`
  `    f n = Σ_{d∣n} muStruct d · Σ_{e∣(n/d)} f e`

The reusable core is the **divisor-pair swap** (Dirichlet-convolution
commutativity/associativity):

  `divisor_pair_swap (0<n) (h) : Σ_{d∣n}Σ_{e∣(n/d)} h d e = Σ_{e∣n}Σ_{d∣(n/e)} h d e`

— both sides equal `Σ over {(d,e) : d·e ∣ n}` (the symmetric `pairInd` flat sum,
via `pair_dvd_iff : 0<n → d∣n → (e ∣ n/d ↔ d·e ∣ n)` + `sumZ_fubini`).  Inversion
then: pull `muStruct(d)` in → swap → pull `f(e)` out → inner
`Σ_{d∣(n/e)} muStruct d = [n/e=1]` (`muStruct_divisor_sum`) `= [e=n]` → single-survivor
collapse at `e=n` gives `f(n)`.  All ∅-axiom (propext-dirty `by_cases` on `∣`
replaced by `Nat.decEq (n % d) 0` splits throughout).
-/

namespace E213.Lib.Math.NumberTheory.MobiusInversion

open E213.Lib.Math.NumberTheory.MobiusFunction (sumZ divisorSumZ)
open E213.Lib.Math.NumberTheory.MobiusPrimeCase
  (sumZ_succ sumZ_const_zero sumZ_congr sumZ_split_first)
open E213.Lib.Math.NumberTheory.EulerTotient (dvdInd)
open E213.Lib.Math.NumberTheory.GaussTotient (eqInd eqInd_self eqInd_ne mul_div_of_dvd dvd_mod_zero)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative
  (dvdInd_eq_one_iff dvdInd_eq_zero_iff dvdInd_zero_or_one le_of_dvd_pos')
open E213.Lib.Math.NumberTheory.MobiusDivisorSum
  (sumZ_add_func sumZ_mul_left sumZ_fubini sum_eqIndZ_weight_eq weighted_partition_by_keyZ
   sumZ_mul_right castOne_mul castZero_mul muStruct_divisor_sum)
open E213.Lib.Math.NumberTheory.MobiusMultiplicative (muStruct)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure mul_witness_iff_mod_eq_zero)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Beq213 (nat_beq_op_eq_false_of_ne)

/-! ## §1 — `pair_dvd_iff` -/

/-- For `0 < n` and `d ∣ n`: `e ∣ (n/d) ↔ d·e ∣ n`. -/
theorem pair_dvd_iff {n d e : Nat} (hn : 0 < n) (hd : d ∣ n) :
    e ∣ (n / d) ↔ d * e ∣ n := by
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · exfalso; obtain ⟨c, hc⟩ := hd; rw [h0, Nat.zero_mul] at hc
      exact Nat.lt_irrefl 0 (hc ▸ hn)
    · exact hpos
  have hcof : d * (n / d) = n := mul_div_of_dvd hd
  constructor
  · intro he
    obtain ⟨c, hc⟩ := he
    refine ⟨c, ?_⟩
    calc n = d * (n / d) := hcof.symm
      _ = d * (e * c) := by rw [hc]
      _ = d * e * c := (E213.Tactic.NatHelper.mul_assoc d e c).symm
  · intro hde
    obtain ⟨c, hc⟩ := hde
    refine ⟨c, ?_⟩
    have he1 : n = d * (e * c) := by
      rw [hc]; exact E213.Tactic.NatHelper.mul_assoc d e c
    rw [he1, mul_div_cancel_left_pure d (e * c) hd0]

/-! ## §2 — Range-extension for `sumZ` (zero tail) -/

/-- If `f j = 0` for all `m ≤ j < n` (`m ≤ n`), then `sumZ n f = sumZ m f`. -/
theorem sumZ_eq_of_tail_zero (f : Nat → Int) :
    ∀ (n m : Nat), m ≤ n → (∀ j, m ≤ j → j < n → f j = 0) → sumZ n f = sumZ m f
  | 0, m, hm, _ => by
    have hm0 : m = 0 := Nat.le_antisymm hm (Nat.zero_le m)
    rw [hm0]
  | n + 1, m, hm, hz => by
    cases Nat.lt_or_ge m (n + 1) with
    | inl hlt =>
      have hmn : m ≤ n := Nat.le_of_lt_succ hlt
      rw [sumZ_succ, hz n hmn (Nat.lt_succ_self n),
          E213.Meta.Int213.add_comm _ 0, E213.Meta.Int213.zero_add]
      exact sumZ_eq_of_tail_zero f n m hmn (fun j hj hjn => hz j hj (Nat.lt_succ_of_lt hjn))
    | inr hge =>
      have hmeq : m = n + 1 := Nat.le_antisymm hm hge
      rw [hmeq]

/-! ## §3 — Pair-divisibility indicator -/

/-- `pairInd a b n = [a·b ∣ n]` as an Int (via `eqInd (n % (a*b)) 0`). -/
def pairInd (a b n : Nat) : Int := (eqInd (n % (a * b)) 0 : Int)

/-- `pairInd a b n = 1 ↔ (a*b) ∣ n`. -/
theorem pairInd_eq_one_iff (a b n : Nat) : pairInd a b n = 1 ↔ (a * b) ∣ n := by
  show ((eqInd (n % (a * b)) 0 : Nat) : Int) = 1 ↔ (a * b) ∣ n
  constructor
  · intro h
    have hmod : n % (a * b) = 0 := by
      by_cases hc : n % (a * b) = 0
      · exact hc
      · exfalso
        have hz : ((eqInd (n % (a * b)) 0 : Nat) : Int) = 0 := by
          rw [eqInd_ne hc]; rfl
        rw [hz] at h; exact absurd h (by decide)
    obtain ⟨x, hx⟩ := (mul_witness_iff_mod_eq_zero (a * b) n).mpr hmod
    exact ⟨x, hx.symm⟩
  · intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hmod : n % (a * b) = 0 := dvd_mod_zero ⟨c, hc⟩
    show ((eqInd (n % (a * b)) 0 : Nat) : Int) = 1
    rw [hmod, eqInd_self]; rfl

/-- `pairInd a b n = 0 ↔ ¬ (a*b) ∣ n`. -/
theorem pairInd_eq_zero_iff (a b n : Nat) : pairInd a b n = 0 ↔ ¬ (a * b) ∣ n := by
  constructor
  · intro h hdvd
    have : pairInd a b n = 1 := (pairInd_eq_one_iff a b n).mpr hdvd
    rw [this] at h; exact absurd h (by decide)
  · intro h
    show ((eqInd (n % (a * b)) 0 : Nat) : Int) = 0
    have hmod : ¬ n % (a * b) = 0 := by
      intro hm
      obtain ⟨x, hx⟩ := (mul_witness_iff_mod_eq_zero (a * b) n).mpr hm
      exact h ⟨x, hx.symm⟩
    rw [eqInd_ne hmod]; rfl

/-- `pairInd a b n` is `0` or `1`. -/
theorem pairInd_zero_or_one (a b n : Nat) : pairInd a b n = 0 ∨ pairInd a b n = 1 := by
  show ((eqInd (n % (a * b)) 0 : Nat) : Int) = 0 ∨ ((eqInd (n % (a * b)) 0 : Nat) : Int) = 1
  show (((n % (a * b)) == 0).toNat : Int) = 0 ∨ (((n % (a * b)) == 0).toNat : Int) = 1
  cases ((n % (a * b)) == 0) with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

/-- `pairInd` is symmetric in its first two args. -/
theorem pairInd_comm (a b n : Nat) : pairInd a b n = pairInd b a n := by
  show (eqInd (n % (a * b)) 0 : Int) = (eqInd (n % (b * a)) 0 : Int)
  rw [Nat.mul_comm a b]

/-! ## §4 — Inner sum bridge -/

/-- For `d ∣ n` (`d = jd+1`): the inner divisor indicator on `n/d` equals the pair
    indicator `pairInd d (je+1) n`. -/
theorem dvdInd_eq_pairInd {n d : Nat} (hn : 0 < n) (hd : d ∣ n) (je : Nat) :
    ((dvdInd je (n / d) : Nat) : Int) = pairInd d (je + 1) n := by
  cases dvdInd_zero_or_one je (n / d) with
  | inr h1 =>
    have hd1 : (je + 1) ∣ (n / d) := (dvdInd_eq_one_iff je (n / d)).mp h1
    have hdvd : d * (je + 1) ∣ n := (pair_dvd_iff hn hd).mp hd1
    rw [h1, (pairInd_eq_one_iff d (je + 1) n).mpr hdvd]; rfl
  | inl h0 =>
    have hnd : ¬ (je + 1) ∣ (n / d) := (dvdInd_eq_zero_iff je (n / d)).mp h0
    have hndvd : ¬ d * (je + 1) ∣ n := fun hdvd => hnd ((pair_dvd_iff hn hd).mpr hdvd)
    rw [h0, (pairInd_eq_zero_iff d (je + 1) n).mpr hndvd]; rfl

/-- The pair indicator tail vanishes: for `d ∣ n`, `d = jd+1`, and `je ≥ n/d`,
    `pairInd d (je+1) n = 0`. -/
theorem pairInd_tail_zero {n d : Nat} (hn : 0 < n) (hd : d ∣ n) (hd0 : 0 < d)
    {je : Nat} (hge : n / d ≤ je) : pairInd d (je + 1) n = 0 := by
  refine (pairInd_eq_zero_iff d (je + 1) n).mpr (fun hdvd => ?_)
  -- d*(je+1) ∣ n  ⟹  je+1 ∣ n/d  ⟹  je+1 ≤ n/d  ⟹  je < n/d, contradiction
  have hdd : (je + 1) ∣ (n / d) := (pair_dvd_iff hn hd).mpr hdvd
  have hndpos : 0 < n / d := by
    have hcof : d * (n / d) = n := mul_div_of_dvd hd
    rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
    · exfalso; rw [h0, Nat.mul_zero] at hcof; exact Nat.lt_irrefl 0 (hcof ▸ hn)
    · exact hpos
  have hle : je + 1 ≤ n / d := le_of_dvd_pos' hndpos hdd
  exact Nat.lt_irrefl je (Nat.lt_of_lt_of_le (Nat.lt_succ_self je) (Nat.le_trans hle hge))

/-- **Inner bridge**: for a divisor `d = jd+1` of `n`,
    `dvdInd jd n · divisorSumZ (n/d) (h d) = Σ_{je<n} pairInd d (je+1) n · h d (je+1)`. -/
theorem inner_bridge {n : Nat} (hn : 0 < n) (h : Nat → Nat → Int) (jd : Nat)
    (hdvd : (jd + 1) ∣ n) :
    (dvdInd jd n : Int) * divisorSumZ (n / (jd + 1)) (fun e => h (jd + 1) e)
      = sumZ n (fun je => pairInd (jd + 1) (je + 1) n * h (jd + 1) (je + 1)) := by
  have hd0 : 0 < jd + 1 := Nat.succ_pos jd
  have hdvdInd1 : dvdInd jd n = 1 := (dvdInd_eq_one_iff jd n).mpr hdvd
  rw [hdvdInd1, castOne_mul]
  -- divisorSumZ (n/d) (h d) = sumZ (n/d) (fun je => dvdInd je (n/d) * h d (je+1))
  show sumZ (n / (jd + 1)) (fun je => (dvdInd je (n / (jd + 1)) : Int) * h (jd + 1) (je + 1))
      = sumZ n (fun je => pairInd (jd + 1) (je + 1) n * h (jd + 1) (je + 1))
  -- RHS over range n collapses to range n/d (tail zero)
  have hndle : n / (jd + 1) ≤ n :=
    E213.Meta.Nat.NatDiv213.div_le_self_pos n (jd + 1) hd0
  rw [sumZ_eq_of_tail_zero (fun je => pairInd (jd + 1) (je + 1) n * h (jd + 1) (je + 1))
      n (n / (jd + 1)) hndle
      (fun je hge _ => by
        show pairInd (jd + 1) (je + 1) n * h (jd + 1) (je + 1) = 0
        rw [pairInd_tail_zero hn hdvd hd0 hge, E213.Meta.Int213.zero_mul])]
  -- now pointwise on [0, n/d): dvdInd je (n/d) = pairInd d (je+1) n
  exact sumZ_congr (n / (jd + 1)) _ _ (fun je _ => by
    rw [dvdInd_eq_pairInd hn hdvd je])

/-- `a ∣ n → a*b ∣ n` is what we negate: `¬ a ∣ n → ¬ a*b ∣ n`. -/
theorem not_dvd_of_factor_not_dvd {a b n : Nat} (ha : ¬ a ∣ n) : ¬ a * b ∣ n := by
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  exact ha ⟨b * c, by rw [hc]; exact (E213.Tactic.NatHelper.mul_assoc a b c)⟩

/-- **Inner bridge, non-divisor case**: if `(jd+1) ∤ n` both sides are `0`. -/
theorem inner_bridge_nondvd {n : Nat} (h : Nat → Nat → Int) (jd : Nat)
    (hnd : ¬ (jd + 1) ∣ n) :
    (dvdInd jd n : Int) * divisorSumZ (n / (jd + 1)) (fun e => h (jd + 1) e)
      = sumZ n (fun je => pairInd (jd + 1) (je + 1) n * h (jd + 1) (je + 1)) := by
  have hdvdInd0 : dvdInd jd n = 0 := (dvdInd_eq_zero_iff jd n).mpr hnd
  rw [hdvdInd0, castZero_mul]
  -- RHS is all-zero
  have hz : sumZ n (fun je => pairInd (jd + 1) (je + 1) n * h (jd + 1) (je + 1))
      = sumZ n (fun _ => (0 : Int)) :=
    sumZ_congr n _ _ (fun je _ => by
      have hpz : pairInd (jd + 1) (je + 1) n = 0 :=
        (pairInd_eq_zero_iff (jd + 1) (je + 1) n).mpr (not_dvd_of_factor_not_dvd hnd)
      rw [hpz, E213.Meta.Int213.zero_mul])
  rw [hz, sumZ_const_zero n]

/-- **Inner bridge, all cases**. -/
theorem inner_bridge_all {n : Nat} (hn : 0 < n) (h : Nat → Nat → Int) (jd : Nat) :
    (dvdInd jd n : Int) * divisorSumZ (n / (jd + 1)) (fun e => h (jd + 1) e)
      = sumZ n (fun je => pairInd (jd + 1) (je + 1) n * h (jd + 1) (je + 1)) := by
  cases Nat.decEq (n % (jd + 1)) 0 with
  | isTrue hmod =>
    have hdvd : (jd + 1) ∣ n := by
      obtain ⟨x, hx⟩ := (mul_witness_iff_mod_eq_zero (jd + 1) n).mpr hmod
      exact ⟨x, hx.symm⟩
    exact inner_bridge hn h jd hdvd
  | isFalse hmod =>
    have hnd : ¬ (jd + 1) ∣ n := fun hd => hmod (dvd_mod_zero hd)
    exact inner_bridge_nondvd h jd hnd

/-! ## §5 — The pair bridge: nested divisor sum = flat pair sum -/

/-- ★★ **Pair bridge**: for `0 < n`,
    `Σ_{d∣n} Σ_{e∣(n/d)} h d e = Σ_{jd<n} Σ_{je<n} pairInd (jd+1) (je+1) n · h (jd+1) (je+1)`. -/
theorem pair_bridge {n : Nat} (hn : 0 < n) (h : Nat → Nat → Int) :
    divisorSumZ n (fun d => divisorSumZ (n / d) (fun e => h d e))
      = sumZ n (fun jd => sumZ n (fun je =>
          pairInd (jd + 1) (je + 1) n * h (jd + 1) (je + 1))) := by
  show sumZ n (fun jd => (dvdInd jd n : Int)
        * divisorSumZ (n / (jd + 1)) (fun e => h (jd + 1) e))
      = sumZ n (fun jd => sumZ n (fun je =>
          pairInd (jd + 1) (je + 1) n * h (jd + 1) (je + 1)))
  exact sumZ_congr n _ _ (fun jd _ => inner_bridge_all hn h jd)

/-! ## §6 — The divisor-pair interchange (Dirichlet-convolution core) -/

/-- ★★ **Divisor-pair swap**: for `0 < n`,
    `Σ_{d∣n} Σ_{e∣(n/d)} h d e = Σ_{e∣n} Σ_{d∣(n/e)} h d e`. -/
theorem divisor_pair_swap {n : Nat} (hn : 0 < n) (h : Nat → Nat → Int) :
    divisorSumZ n (fun d => divisorSumZ (n / d) (fun e => h d e))
      = divisorSumZ n (fun e => divisorSumZ (n / e) (fun d => h d e)) := by
  rw [pair_bridge hn h]
  -- RHS: apply pair_bridge to h' a b = h b a
  rw [pair_bridge hn (fun a b => h b a)]
  -- LHS now: Σ_jd Σ_je pairInd (jd+1)(je+1) n · h (jd+1)(je+1)
  -- RHS now: Σ_je Σ_jd pairInd (je+1)(jd+1) n · h (jd+1)(je+1)
  rw [sumZ_fubini (fun jd je =>
        pairInd (jd + 1) (je + 1) n * h (jd + 1) (je + 1)) n n]
  exact sumZ_congr n _ _ (fun je _ =>
    sumZ_congr n _ _ (fun jd _ => by
      rw [pairInd_comm (jd + 1) (je + 1) n]))

/-! ## §7 — Pulling constants through `divisorSumZ` -/

/-- Pull a left Int constant through `divisorSumZ`:
    `divisorSumZ m (fun d => c · k d) = c · divisorSumZ m k`. -/
theorem divisorSumZ_const_mul (c : Int) (m : Nat) (k : Nat → Int) :
    divisorSumZ m (fun d => c * k d) = c * divisorSumZ m k := by
  show sumZ m (fun j => (dvdInd j m : Int) * (c * k (j + 1)))
      = c * sumZ m (fun j => (dvdInd j m : Int) * k (j + 1))
  rw [sumZ_mul_left c m (fun j => (dvdInd j m : Int) * k (j + 1))]
  exact sumZ_congr m _ _ (fun j _ => by
    -- dvdInd · (c · k) = c · (dvdInd · k)
    generalize (dvdInd j m : Int) = D
    generalize k (j + 1) = K
    ring_intZ)

/-! ## §8 — `n/e = 1 ⟺ e = n` and the final survivor collapse -/

/-- For `e ∣ n` (`0 < n`): `n / e = 1 ↔ e = n`. -/
theorem div_eq_one_iff_eq {n e : Nat} (hn : 0 < n) (he : e ∣ n) :
    n / e = 1 ↔ e = n := by
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · exfalso; obtain ⟨c, hc⟩ := he; rw [h0, Nat.zero_mul] at hc
      exact Nat.lt_irrefl 0 (hc ▸ hn)
    · exact hpos
  have hcof : e * (n / e) = n := mul_div_of_dvd he
  constructor
  · intro h1
    rw [h1, Nat.mul_one] at hcof; exact hcof
  · intro hen
    subst hen
    have hh : e * 1 / e = 1 := mul_div_cancel_left_pure e 1 he0
    rw [Nat.mul_one] at hh; exact hh

/-- **Survivor pointwise**: for `je < n`,
    `dvdInd je n · (f (je+1) · [(n/(je+1)) = 1]) = [je = n-1] · f n`. -/
theorem survivor_pointwise {n : Nat} (hn : 0 < n) (f : Nat → Int) (je : Nat) :
    (dvdInd je n : Int) * (f (je + 1) * ((((n / (je + 1)) == 1).toNat : Nat) : Int))
      = (eqInd (n - 1) je : Int) * f n := by
  have hn1 : n - 1 + 1 = n := E213.Tactic.NatHelper.sub_one_add_one (Nat.ne_of_gt hn)
  cases Nat.decEq je (n - 1) with
  | isTrue hjeq =>
    subst hjeq
    -- je = n-1 ⟹ je+1 = n
    rw [eqInd_self]
    have hdvd : (n - 1 + 1) ∣ n := by rw [hn1]; exact ⟨1, (Nat.mul_one n).symm⟩
    have hd1 : dvdInd (n - 1) n = 1 := (dvdInd_eq_one_iff (n - 1) n).mpr hdvd
    have hdivself : n / (n - 1 + 1) = 1 := by
      rw [hn1]
      have hh : n * 1 / n = 1 := mul_div_cancel_left_pure n 1 hn
      rw [Nat.mul_one] at hh; exact hh
    rw [hd1, hdivself, hn1]
    show ((1 : Nat) : Int) * (f n * (((1 : Nat) == 1).toNat : Int)) = ((1 : Nat) : Int) * f n
    show (1 : Int) * (f n * (1 : Int)) = (1 : Int) * f n
    generalize f n = F
    ring_intZ
  | isFalse hjne =>
    rw [eqInd_ne (fun he : n - 1 = je => hjne he.symm), castZero_mul]
    -- show LHS = 0
    cases dvdInd_zero_or_one je n with
    | inl h0 => rw [h0, castZero_mul]
    | inr h1 =>
      have hdvd : (je + 1) ∣ n := (dvdInd_eq_one_iff je n).mp h1
      -- je+1 ≠ n, since je ≠ n-1
      have hne : je + 1 ≠ n := by
        intro heq
        apply hjne
        rw [← heq]; exact (E213.Tactic.NatHelper.add_sub_cancel_right je 1).symm
      have hdivne : n / (je + 1) ≠ 1 := fun h1' =>
        hne ((div_eq_one_iff_eq hn hdvd).mp h1')
      have hindzero : (((n / (je + 1)) == 1).toNat : Int) = 0 := by
        rw [nat_beq_op_eq_false_of_ne hdivne]; rfl
      rw [hindzero, E213.Meta.Int213.PolyIntM.mul_zeroZ,
          E213.Meta.Int213.PolyIntM.mul_zeroZ]

/-! ## §9 — Inner evaluation against `muStruct_divisor_sum`, gated -/

/-- For a divisor `e = je+1` of `n` (`0 < n`):
    `divisorSumZ (n/e) (fun d => muStruct d · f e) = f e · [(n/e) = 1]`. -/
theorem inner_eval_dvd {n : Nat} (hn : 0 < n) (f : Nat → Int) {je : Nat}
    (hdvd : (je + 1) ∣ n) :
    divisorSumZ (n / (je + 1)) (fun d => muStruct d * f (je + 1))
      = f (je + 1) * ((((n / (je + 1)) == 1).toNat : Nat) : Int) := by
  have hndpos : 0 < n / (je + 1) := by
    have hcof : (je + 1) * (n / (je + 1)) = n := mul_div_of_dvd hdvd
    rcases Nat.eq_zero_or_pos (n / (je + 1)) with h0 | hpos
    · exfalso; rw [h0, Nat.mul_zero] at hcof; exact Nat.lt_irrefl 0 (hcof ▸ hn)
    · exact hpos
  -- commute integrand: muStruct d * f e = f e * muStruct d
  have hcomm : divisorSumZ (n / (je + 1)) (fun d => muStruct d * f (je + 1))
      = divisorSumZ (n / (je + 1)) (fun d => f (je + 1) * muStruct d) := by
    show sumZ (n / (je + 1)) (fun j => (dvdInd j (n / (je + 1)) : Int)
          * (muStruct (j + 1) * f (je + 1)))
        = sumZ (n / (je + 1)) (fun j => (dvdInd j (n / (je + 1)) : Int)
          * (f (je + 1) * muStruct (j + 1)))
    exact sumZ_congr (n / (je + 1)) _ _ (fun j _ => by
      generalize (dvdInd j (n / (je + 1)) : Int) = D
      generalize muStruct (j + 1) = M
      generalize f (je + 1) = F
      ring_intZ)
  rw [hcomm, divisorSumZ_const_mul (f (je + 1)) (n / (je + 1)) muStruct,
      muStruct_divisor_sum (n / (je + 1)) hndpos]

/-- The gated inner-term identity, all `je`. -/
theorem inner_term_eval {n : Nat} (hn : 0 < n) (f : Nat → Int) (je : Nat) :
    (dvdInd je n : Int) * divisorSumZ (n / (je + 1)) (fun d => muStruct d * f (je + 1))
      = (dvdInd je n : Int)
        * (f (je + 1) * ((((n / (je + 1)) == 1).toNat : Nat) : Int)) := by
  cases Nat.decEq (n % (je + 1)) 0 with
  | isTrue hmod =>
    have hdvd : (je + 1) ∣ n := by
      obtain ⟨x, hx⟩ := (mul_witness_iff_mod_eq_zero (je + 1) n).mpr hmod
      exact ⟨x, hx.symm⟩
    rw [inner_eval_dvd hn f hdvd]
  | isFalse hmod =>
    have hnd : ¬ (je + 1) ∣ n := fun hd => hmod (dvd_mod_zero hd)
    have h0 : dvdInd je n = 0 := (dvdInd_eq_zero_iff je n).mpr hnd
    rw [h0, castZero_mul, castZero_mul]

/-! ## §10 — ★★★ Möbius inversion -/

/-- ★★★ **Möbius inversion** (g-defined form): for `0 < n`,
    `f n = Σ_{d∣n} muStruct(d) · (Σ_{e∣(n/d)} f e)`. -/
theorem mobius_inversion_g (f : Nat → Int) (n : Nat) (hn : 0 < n) :
    f n = divisorSumZ n (fun d => muStruct d * divisorSumZ (n / d) f) := by
  -- Step 1: pull muStruct(d) into the inner sum
  have hstep1 : divisorSumZ n (fun d => muStruct d * divisorSumZ (n / d) f)
      = divisorSumZ n (fun d => divisorSumZ (n / d) (fun e => muStruct d * f e)) := by
    show sumZ n (fun jd => (dvdInd jd n : Int)
          * (muStruct (jd + 1) * divisorSumZ (n / (jd + 1)) f))
        = sumZ n (fun jd => (dvdInd jd n : Int)
          * divisorSumZ (n / (jd + 1)) (fun e => muStruct (jd + 1) * f e))
    exact sumZ_congr n _ _ (fun jd _ => by
      rw [divisorSumZ_const_mul (muStruct (jd + 1)) (n / (jd + 1)) f])
  rw [hstep1, divisor_pair_swap hn (fun d e => muStruct d * f e)]
  -- now: Σ_e Σ_d muStruct d * f e, evaluate inner via muStruct_divisor_sum
  have hstep2 : divisorSumZ n (fun e => divisorSumZ (n / e) (fun d => muStruct d * f e))
      = divisorSumZ n (fun e => f e * ((((n / e) == 1).toNat : Nat) : Int)) := by
    show sumZ n (fun je => (dvdInd je n : Int)
          * divisorSumZ (n / (je + 1)) (fun d => muStruct d * f (je + 1)))
        = sumZ n (fun je => (dvdInd je n : Int)
          * (f (je + 1) * ((((n / (je + 1)) == 1).toNat : Nat) : Int)))
    exact sumZ_congr n _ _ (fun je _ => inner_term_eval hn f je)
  rw [hstep2]
  -- collapse to f n
  have hcollapse : divisorSumZ n (fun e => f e * ((((n / e) == 1).toNat : Nat) : Int))
      = f n := by
    show sumZ n (fun je => (dvdInd je n : Int)
          * (f (je + 1) * ((((n / (je + 1)) == 1).toNat : Nat) : Int)))
        = f n
    rw [sumZ_congr n _ (fun je => (eqInd (n - 1) je : Int) * f n)
        (fun je _ => survivor_pointwise hn f je)]
    exact sum_eqIndZ_weight_eq n (n - 1) (f n)
      (Nat.lt_of_lt_of_le (Nat.sub_lt hn Nat.one_pos) (Nat.le_refl n))
  rw [hcollapse]

/-- ★★★ **Möbius inversion** (hypothesis form): if `g m = Σ_{e∣m} f e` for all
    `0 < m`, then `f n = Σ_{d∣n} muStruct(d) · g(n/d)` (`0 < n`). -/
theorem mobius_inversion (f g : Nat → Int) (n : Nat) (hn : 0 < n)
    (hg : ∀ m, 0 < m → g m = divisorSumZ m f) :
    f n = divisorSumZ n (fun d => muStruct d * g (n / d)) := by
  rw [mobius_inversion_g f n hn]
  -- replace g(n/d) by divisorSumZ (n/d) f on the divisor support
  show sumZ n (fun jd => (dvdInd jd n : Int) * (muStruct (jd + 1) * divisorSumZ (n / (jd + 1)) f))
      = sumZ n (fun jd => (dvdInd jd n : Int) * (muStruct (jd + 1) * g (n / (jd + 1))))
  refine sumZ_congr n _ _ (fun jd _ => ?_)
  cases Nat.decEq (n % (jd + 1)) 0 with
  | isTrue hmod =>
    have hdvd : (jd + 1) ∣ n := by
      obtain ⟨x, hx⟩ := (mul_witness_iff_mod_eq_zero (jd + 1) n).mpr hmod
      exact ⟨x, hx.symm⟩
    have hndpos : 0 < n / (jd + 1) := by
      have hcof : (jd + 1) * (n / (jd + 1)) = n := mul_div_of_dvd hdvd
      rcases Nat.eq_zero_or_pos (n / (jd + 1)) with h0 | hpos
      · exfalso; rw [h0, Nat.mul_zero] at hcof; exact Nat.lt_irrefl 0 (hcof ▸ hn)
      · exact hpos
    rw [hg (n / (jd + 1)) hndpos]
  | isFalse hmod =>
    have hnd : ¬ (jd + 1) ∣ n := fun hd => hmod (dvd_mod_zero hd)
    have h0 : dvdInd jd n = 0 := (dvdInd_eq_zero_iff jd n).mpr hnd
    rw [h0, castZero_mul, castZero_mul]

end E213.Lib.Math.NumberTheory.MobiusInversion
