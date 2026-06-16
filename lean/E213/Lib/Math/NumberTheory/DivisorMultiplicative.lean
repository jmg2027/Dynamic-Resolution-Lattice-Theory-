import E213.Meta.Nat.Gcd213
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Meta.Nat.PolyNatMTactic
import E213.Lib.Math.NumberTheory.EulerTotient
import E213.Lib.Math.NumberTheory.SumOfDivisors
import E213.Lib.Math.Combinatorics.SumReshape
import E213.Lib.Math.NumberTheory.FactorialLcmIdentity
import E213.Lib.Math.NumberTheory.GaussTotient
import E213.Lib.Math.NumberTheory.DivisorProductReindex

/-!
# Divisor-product reindex + σ/τ multiplicativity (∅-axiom)

★★★ Closes the divisor-product programme:
the sparse-fiber reindex tool, and the general multiplicativity of σ and τ.

  * ★★★ `divisor_product_reindex` : for coprime `a,b` (`0<a`, `0<b`),
        `divisorSum (a·b) f = Σ_{i<a}Σ_{k<b} dvdInd i a · dvdInd k b · f((i+1)(k+1))`.
  * ★★★ `sigma_mul` : `gcd(a,b)=1 → 0<a → 0<b → sigma (a·b) = sigma a · sigma b`.
  * ★★★ `tau_mul`   : likewise for τ.

The missing tool was a **sparse-fiber sum reindex over `sumTo`** (the divisor fiber
`{j : gcd(j+1,a)=e}` is non-contiguous, so `sumTo_reshape` cannot isolate it).  Built
via a *double partition-by-key collapsing each cell to a single survivor*: the outer
key `gcd(j+1,a)` and inner key `gcd(j+1,b)` partition `[0,ab)`; the
divisor-factorization bijection `j+1 = gcd(j+1,a)·gcd(j+1,b)` (`DivisorProductReindex`)
pins the unique survivor `j = e(k+1)−1` per cell (`cell_pointwise`), and each cell sum
collapses by `sum_eqInd_weight_eq`.  σ/τ then discharge the conditional
`sigma_mul_of_reindex`/`tau_mul_of_reindex`.  The same reindex unlocks the general
Möbius divisor-sum and Möbius inversion.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.DivisorMultiplicative

open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213
  (gcd213_dvd_left gcd213_dvd_right gcd213_greatest gcd213_comm gcd213_self
   gcd213_mul_left coprime_dvd_of_dvd_mul dvd_antisymm_213 mul_assoc_213)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
  (dvd_trans_213 eq_one_of_dvd_one coprime_mul_of_coprime
   coprime_of_coprime_mul_left coprime_of_coprime_mul_right coprime_mul_iff
   gcd213_one_right)
open E213.Lib.Math.NumberTheory.EulerTotient (divisorSum dvdInd)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_congr sumTo_mul_left sumTo_split_first)
open E213.Lib.Math.NumberTheory.GaussTotient
  (eqInd eqInd_self eqInd_ne mul_div_of_dvd gcd_succ_pos)
open E213.Lib.Math.NumberTheory.FactorialLcmIdentity
  (sumTo_const_zero sumTo_fubini)
open E213.Lib.Math.NumberTheory.DivisorProductReindex
  (gcd_mul_coprime divisor_factorization divisor_factors_coprime
   gcd_fiber_forward sum_eqInd_weight_eq weighted_partition_by_key
   gcd_eq_left_of_dvd coprime_of_dvd_left)

/-- `dvdInd d n = 1 ↔ (d+1) ∣ n`: `dvdInd` is 1 exactly on divisors. -/
theorem dvdInd_eq_one_iff (d n : Nat) : dvdInd d n = 1 ↔ (d + 1) ∣ n := by
  constructor
  · intro h
    have hmod : n % (d + 1) = 0 := by
      show n % (d + 1) = 0
      by_cases hc : n % (d + 1) = 0
      · exact hc
      · exfalso
        have : dvdInd d n = 0 := by
          show (n % (d + 1) == 0).toNat = 0
          rw [E213.Meta.Nat.Beq213.nat_beq_op_eq_false_of_ne hc]; rfl
        rw [this] at h; exact Nat.noConfusion h
    obtain ⟨x, hx⟩ := (E213.Meta.Nat.NatDiv213.mul_witness_iff_mod_eq_zero (d + 1) n).mpr hmod
    exact ⟨x, hx.symm⟩
  · intro h
    obtain ⟨c, hc⟩ := h
    have hmod : n % (d + 1) = 0 :=
      E213.Lib.Math.NumberTheory.GaussTotient.dvd_mod_zero ⟨c, hc⟩
    show (n % (d + 1) == 0).toNat = 1
    rw [hmod, show ((0 : Nat) == 0) = true from decide_eq_true rfl]; rfl

/-- `dvdInd d n = 0 ↔ ¬ (d+1) ∣ n`. -/
theorem dvdInd_eq_zero_iff (d n : Nat) : dvdInd d n = 0 ↔ ¬ (d + 1) ∣ n := by
  constructor
  · intro h hdvd
    have : dvdInd d n = 1 := (dvdInd_eq_one_iff d n).mpr hdvd
    rw [this] at h; exact Nat.noConfusion h.symm
  · intro h
    show (n % (d + 1) == 0).toNat = 0
    have hmod : ¬ n % (d + 1) = 0 := by
      intro hm
      obtain ⟨x, hx⟩ := (E213.Meta.Nat.NatDiv213.mul_witness_iff_mod_eq_zero (d + 1) n).mpr hm
      exact h ⟨x, hx.symm⟩
    rw [E213.Meta.Nat.Beq213.nat_beq_op_eq_false_of_ne hmod]; rfl

/-- `gcd(e,b)=1 → gcd(e*m, b) = gcd(m, b)` (strip a coprime factor from a gcd). -/
theorem gcd_strip_coprime_factor {e b m : Nat} (heb : gcd213 e b = 1) :
    gcd213 (e * m) b = gcd213 m b := by
  apply dvd_antisymm_213
  · have hdb : gcd213 (e * m) b ∣ b := gcd213_dvd_right (e * m) b
    have hdem : gcd213 (e * m) b ∣ e * m := gcd213_dvd_left (e * m) b
    have hcop_e : gcd213 (gcd213 (e * m) b) e = 1 := by
      have hdvd1 : gcd213 (gcd213 (e * m) b) e ∣ e :=
        gcd213_dvd_right (gcd213 (e * m) b) e
      have hdvd2 : gcd213 (gcd213 (e * m) b) e ∣ b :=
        dvd_trans_213 (gcd213_dvd_left (gcd213 (e * m) b) e) hdb
      have hdvd3 : gcd213 (gcd213 (e * m) b) e ∣ gcd213 e b :=
        gcd213_greatest e b _ hdvd1 hdvd2
      exact eq_one_of_dvd_one (heb ▸ hdvd3)
    have hdm : gcd213 (e * m) b ∣ m := coprime_dvd_of_dvd_mul hcop_e hdem
    exact gcd213_greatest m b _ hdm hdb
  · have hdm : gcd213 m b ∣ m := gcd213_dvd_left m b
    have hdb : gcd213 m b ∣ b := gcd213_dvd_right m b
    have hdem : gcd213 m b ∣ e * m := dvd_trans_213 hdm ⟨e, Nat.mul_comm e m⟩
    exact gcd213_greatest (e * m) b _ hdem hdb

/-- `e ∣ a, gcd(a,b)=1 → gcd(e,b)=1`. -/
theorem coprime_factor_right {a b e : Nat} (hab : gcd213 a b = 1) (hea : e ∣ a) :
    gcd213 e b = 1 := coprime_of_dvd_left hab hea

/-- **Survivor gates**: for `e ∣ a`, `gcd(a,b)=1`, `0 < e`, `(k+1) ∣ b`:
    `gcd(e(k+1),a)=e`, `gcd(e(k+1),b)=k+1`, and `e(k+1) ∣ a·b`. -/
theorem survivor_gates {a b e k : Nat} (hab : gcd213 a b = 1)
    (hea : e ∣ a) (hepos : 0 < e) (hkb : (k + 1) ∣ b) :
    gcd213 (e * (k + 1)) a = e
    ∧ gcd213 (e * (k + 1)) b = k + 1
    ∧ e * (k + 1) ∣ a * b := by
  refine ⟨gcd_fiber_forward hab hea hkb hepos, ?_, ?_⟩
  · have heb : gcd213 e b = 1 := coprime_factor_right hab hea
    rw [gcd_strip_coprime_factor heb]
    exact gcd_eq_left_of_dvd hkb
  · obtain ⟨ca, hca⟩ := hea
    obtain ⟨cb, hcb⟩ := hkb
    refine ⟨ca * cb, ?_⟩
    rw [hca, hcb]
    ring_nat

open E213.Tactic.NatHelper (sub_one_add_one)

/-- `dvdInd d n` is `0` or `1`. -/
theorem dvdInd_zero_or_one (d n : Nat) : dvdInd d n = 0 ∨ dvdInd d n = 1 := by
  show (n % (d + 1) == 0).toNat = 0 ∨ (n % (d + 1) == 0).toNat = 1
  cases (n % (d + 1) == 0) with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

/-- **Cell pointwise identity** (the divisor-factorization bijection, termwise):
    each flat index `j` either misses (both sides `0`) or sits at the unique survivor
    `j = e(k+1)−1`. -/
theorem cell_pointwise {a b e k : Nat} (hab : gcd213 a b = 1) (hea : e ∣ a)
    (hepos : 0 < e) (f : Nat → Nat) (j : Nat) :
    eqInd (gcd213 (j + 1) b) (k + 1)
        * (eqInd (gcd213 (j + 1) a) e * (dvdInd j (a * b) * f (j + 1)))
      = eqInd (e * (k + 1) - 1) j * (dvdInd k b * f (e * (k + 1))) := by
  have hj0 : e * (k + 1) - 1 + 1 = e * (k + 1) :=
    sub_one_add_one (Nat.ne_of_gt (Nat.mul_pos hepos (Nat.succ_pos k)))
  cases Nat.decEq j (e * (k + 1) - 1) with
  | isTrue hjeq =>
    have hj1 : j + 1 = e * (k + 1) := by rw [hjeq]; exact hj0
    subst hjeq
    rw [eqInd_self, hj1]
    cases dvdInd_zero_or_one k b with
    | inr hdk =>
      have hkb : (k + 1) ∣ b := (dvdInd_eq_one_iff k b).mp hdk
      obtain ⟨hga, hgb, hdvdab⟩ := survivor_gates hab hea hepos hkb
      rw [hga, hgb, eqInd_self, eqInd_self,
          (dvdInd_eq_one_iff (e * (k + 1) - 1) (a * b)).mpr (hj1 ▸ hdvdab), hdk]
      generalize f (e * (k + 1)) = F
      ring_nat
    | inl hdk =>
      have hkb : ¬ (k + 1) ∣ b := (dvdInd_eq_zero_iff k b).mp hdk
      have heb : gcd213 e b = 1 := coprime_factor_right hab hea
      have hgne : gcd213 (e * (k + 1)) b ≠ k + 1 := by
        rw [gcd_strip_coprime_factor heb]
        intro hgeq
        exact hkb (hgeq ▸ gcd213_dvd_right (k + 1) b)
      rw [eqInd_ne hgne, Nat.zero_mul, hdk, Nat.zero_mul, Nat.mul_zero]
  | isFalse hjne =>
    rw [eqInd_ne (fun he => hjne he.symm), Nat.zero_mul]
    cases dvdInd_zero_or_one j (a * b) with
    | inl hd0 => rw [hd0, Nat.zero_mul, Nat.mul_zero, Nat.mul_zero]
    | inr hd1 =>
      have hdvdab : (j + 1) ∣ a * b := (dvdInd_eq_one_iff j (a * b)).mp hd1
      have hfact : j + 1 = gcd213 (j + 1) a * gcd213 (j + 1) b :=
        divisor_factorization hab hdvdab
      cases Nat.decEq (gcd213 (j + 1) a) e with
      | isFalse hga => rw [eqInd_ne hga, Nat.zero_mul, Nat.mul_zero]
      | isTrue hga =>
        cases Nat.decEq (gcd213 (j + 1) b) (k + 1) with
        | isFalse hgb => rw [eqInd_ne hgb, Nat.zero_mul]
        | isTrue hgb =>
          exfalso
          have hj1 : j + 1 = e * (k + 1) := by rw [hfact, hga, hgb]
          have hjsurv : j = e * (k + 1) - 1 := by
            rw [← hj1]; exact (E213.Tactic.NatHelper.add_sub_cancel_right j 1).symm
          exact hjne hjsurv

/-- `e ∣ a → 0 < a → e ≤ a` (∅-axiom; `Nat.le_of_dvd` carries propext). -/
theorem le_of_dvd_pos' {e a : Nat} (ha : 0 < a) (h : e ∣ a) : e ≤ a := by
  obtain ⟨c, hc⟩ := h
  have hc0 : 0 < c := by
    cases c with
    | zero => rw [Nat.mul_zero] at hc; exact absurd (hc ▸ ha) (Nat.lt_irrefl 0)
    | succ c' => exact Nat.succ_pos c'
  have hle : e * 1 ≤ e * c := Nat.mul_le_mul_left e hc0
  rw [Nat.mul_one] at hle
  rw [hc]; exact hle

/-- **Single-cell sum**: the inner sum at fixed `k` collapses to the survivor term. -/
theorem cell_sum {a b e k : Nat} (hab : gcd213 a b = 1) (hea : e ∣ a)
    (hepos : 0 < e) (ha : 0 < a) (hb : 0 < b) (f : Nat → Nat) :
    sumTo (a * b) (fun j => eqInd (gcd213 (j + 1) b) (k + 1)
        * (eqInd (gcd213 (j + 1) a) e * (dvdInd j (a * b) * f (j + 1))))
      = dvdInd k b * f (e * (k + 1)) := by
  rw [sumTo_congr (a * b) _
      (fun j => eqInd (e * (k + 1) - 1) j * (dvdInd k b * f (e * (k + 1))))
      (fun j _ => cell_pointwise hab hea hepos f j)]
  cases dvdInd_zero_or_one k b with
  | inr hdk =>
    have hkb : (k + 1) ∣ b := (dvdInd_eq_one_iff k b).mp hdk
    have hea_le : e ≤ a := le_of_dvd_pos' ha hea
    have hkb_le : k + 1 ≤ b := le_of_dvd_pos' hb hkb
    have hprod_le : e * (k + 1) ≤ a * b := Nat.mul_le_mul hea_le hkb_le
    have hprod_pos : 0 < e * (k + 1) := Nat.mul_pos hepos (Nat.succ_pos k)
    have hlt : e * (k + 1) - 1 < a * b :=
      Nat.lt_of_lt_of_le (Nat.sub_lt hprod_pos Nat.one_pos) hprod_le
    exact sum_eqInd_weight_eq (a * b) (e * (k + 1) - 1) (dvdInd k b * f (e * (k + 1))) hlt
  | inl hdk =>
    rw [hdk, Nat.zero_mul]
    rw [sumTo_congr (a * b)
        (fun j => eqInd (e * (k + 1) - 1) j * 0) (fun _ => 0) (fun j _ => Nat.mul_zero _)]
    exact sumTo_const_zero (a * b)

/-- **Class collapse**: the `e`-class of the flat sum collapses to the inner `b`-sum. -/
theorem class_collapse {a b e : Nat} (hab : gcd213 a b = 1) (hea : e ∣ a)
    (hepos : 0 < e) (ha : 0 < a) (hb : 0 < b) (f : Nat → Nat) :
    sumTo (a * b) (fun j => eqInd (gcd213 (j + 1) a) e * (dvdInd j (a * b) * f (j + 1)))
      = sumTo b (fun k => dvdInd k b * f (e * (k + 1))) := by
  have hkey : ∀ j, j < a * b → gcd213 (j + 1) b < b + 1 := by
    intro j _
    exact Nat.lt_succ_of_le (le_of_dvd_pos' hb (gcd213_dvd_right (j + 1) b))
  rw [weighted_partition_by_key (fun j => gcd213 (j + 1) b)
      (fun j => eqInd (gcd213 (j + 1) a) e * (dvdInd j (a * b) * f (j + 1))) (a * b) (b + 1) hkey]
  rw [sumTo_split_first b
      (fun v => sumTo (a * b) (fun j =>
        eqInd (gcd213 (j + 1) b) v
          * (eqInd (gcd213 (j + 1) a) e * (dvdInd j (a * b) * f (j + 1)))))]
  have hhead : sumTo (a * b) (fun j =>
      eqInd (gcd213 (j + 1) b) 0
        * (eqInd (gcd213 (j + 1) a) e * (dvdInd j (a * b) * f (j + 1)))) = 0 := by
    rw [sumTo_congr (a * b) _ (fun _ => 0) (fun j _ => ?_)]
    · exact sumTo_const_zero (a * b)
    · rw [eqInd_ne (Nat.ne_of_gt (gcd_succ_pos j b)), Nat.zero_mul]
  rw [hhead, Nat.zero_add]
  exact sumTo_congr b _ _ (fun k _ => cell_sum hab hea hepos ha hb f)

/-- **Class zero** (non-divisor `e`): if `e ∤ a` the `e`-class vanishes. -/
theorem class_zero {a b e : Nat} (hea : ¬ e ∣ a) (f : Nat → Nat) :
    sumTo (a * b) (fun j => eqInd (gcd213 (j + 1) a) e * (dvdInd j (a * b) * f (j + 1))) = 0 := by
  rw [sumTo_congr (a * b) _ (fun _ => 0) (fun j _ => ?_)]
  · exact sumTo_const_zero (a * b)
  · refine (Nat.mul_eq_zero).mpr (Or.inl ?_)
    refine eqInd_ne (fun heq => hea ?_)
    exact heq ▸ gcd213_dvd_right (j + 1) a

/-- **Outer term** (each `i`-row): the `(i+1)`-class equals the gated inner `b`-sum. -/
theorem outer_term {a b : Nat} (hab : gcd213 a b = 1) (ha : 0 < a) (hb : 0 < b)
    (f : Nat → Nat) (i : Nat) :
    sumTo (a * b) (fun j =>
        eqInd (gcd213 (j + 1) a) (i + 1) * (dvdInd j (a * b) * f (j + 1)))
      = sumTo b (fun k => dvdInd i a * dvdInd k b * f ((i + 1) * (k + 1))) := by
  cases Nat.decEq (dvdInd i a) 1 with
  | isTrue hdi =>
    have hia : (i + 1) ∣ a := (dvdInd_eq_one_iff i a).mp hdi
    rw [class_collapse hab hia (Nat.succ_pos i) ha hb f]
    refine sumTo_congr b _ _ (fun k _ => ?_)
    rw [hdi, Nat.one_mul]
  | isFalse hdi0 =>
    have hia : ¬ (i + 1) ∣ a := by
      intro hd; exact hdi0 ((dvdInd_eq_one_iff i a).mpr hd)
    have hdi : dvdInd i a = 0 := by
      cases dvdInd_zero_or_one i a with
      | inl h => exact h
      | inr h => exact absurd h hdi0
    rw [class_zero hia f]
    rw [sumTo_congr b _ (fun _ => 0) (fun k _ => ?_)]
    · exact (sumTo_const_zero b).symm
    · rw [hdi, Nat.zero_mul, Nat.zero_mul]

/-- ★★★ **The divisor-product reindex** — the one missing tool.
    For coprime `a,b` (`0 < a`, `0 < b`):
    `divisorSum (a·b) f = Σ_{i<a}Σ_{k<b} dvdInd i a · dvdInd k b · f((i+1)(k+1))`. -/
theorem divisor_product_reindex (a b : Nat) (hab : gcd213 a b = 1)
    (ha : 0 < a) (hb : 0 < b) (f : Nat → Nat) :
    divisorSum (a * b) f
      = sumTo a (fun i => sumTo b (fun k =>
          dvdInd i a * dvdInd k b * f ((i + 1) * (k + 1)))) := by
  show sumTo (a * b) (fun j => dvdInd j (a * b) * f (j + 1))
      = sumTo a (fun i => sumTo b (fun k =>
          dvdInd i a * dvdInd k b * f ((i + 1) * (k + 1))))
  have hkey : ∀ j, j < a * b → gcd213 (j + 1) a < a + 1 := by
    intro j _
    exact Nat.lt_succ_of_le (le_of_dvd_pos' ha (gcd213_dvd_right (j + 1) a))
  rw [weighted_partition_by_key (fun j => gcd213 (j + 1) a)
      (fun j => dvdInd j (a * b) * f (j + 1)) (a * b) (a + 1) hkey]
  rw [sumTo_split_first a
      (fun v => sumTo (a * b) (fun j =>
        eqInd (gcd213 (j + 1) a) v * (dvdInd j (a * b) * f (j + 1))))]
  have hhead : sumTo (a * b) (fun j =>
      eqInd (gcd213 (j + 1) a) 0 * (dvdInd j (a * b) * f (j + 1))) = 0 := by
    rw [sumTo_congr (a * b) _ (fun _ => 0) (fun j _ => ?_)]
    · exact sumTo_const_zero (a * b)
    · rw [eqInd_ne (Nat.ne_of_gt (gcd_succ_pos j a)), Nat.zero_mul]
  rw [hhead, Nat.zero_add]
  exact sumTo_congr a _ _ (fun i _ => outer_term hab ha hb f i)

open E213.Lib.Math.NumberTheory.SumOfDivisors (sigma tau)
open E213.Lib.Math.NumberTheory.DivisorProductReindex (sigma_mul_of_reindex tau_mul_of_reindex)

/-- ★★★ **σ is multiplicative over coprime products**:
    `gcd(a,b)=1 → 0<a → 0<b → sigma (a·b) = sigma a · sigma b`. -/
theorem sigma_mul {a b : Nat} (hab : gcd213 a b = 1) (ha : 0 < a) (hb : 0 < b) :
    sigma (a * b) = sigma a * sigma b :=
  sigma_mul_of_reindex (divisor_product_reindex a b hab ha hb (fun d => d))

/-- ★★★ **τ is multiplicative over coprime products**:
    `gcd(a,b)=1 → 0<a → 0<b → tau (a·b) = tau a · tau b`. -/
theorem tau_mul {a b : Nat} (hab : gcd213 a b = 1) (ha : 0 < a) (hb : 0 < b) :
    tau (a * b) = tau a * tau b := by
  refine tau_mul_of_reindex ?_
  exact divisor_product_reindex a b hab ha hb (fun _ => 1)

/-- Smoke: σ(12)=σ(4)·σ(3)=28, σ(15)=σ(3)·σ(5)=24, τ(12)=τ(4)·τ(3)=6, via the theorems. -/
theorem mul_smoke :
    sigma 12 = sigma 4 * sigma 3
    ∧ sigma 15 = sigma 3 * sigma 5
    ∧ tau 12 = tau 4 * tau 3 :=
  ⟨sigma_mul (a := 4) (b := 3) (by decide) (by decide) (by decide),
   sigma_mul (a := 3) (b := 5) (by decide) (by decide) (by decide),
   tau_mul (a := 4) (b := 3) (by decide) (by decide) (by decide)⟩

end E213.Lib.Math.NumberTheory.DivisorMultiplicative
