import E213.Lib.Math.NumberTheory.MobiusMultiplicative
import E213.Lib.Math.NumberTheory.MobiusPrimeCase
import E213.Lib.Math.NumberTheory.DivisorMultiplicative
import E213.Lib.Math.NumberTheory.MobiusFunction
import E213.Meta.Nat.VpSeparation
import E213.Meta.Nat.VpMul
import E213.Meta.Nat.Valuation
import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor

/-!
# General Möbius divisor-sum `Σ_{d∣n} μ(d) = [n=1]` (∅-axiom)

★★★ For the structurally-defined Möbius `muStruct` (`MobiusMultiplicative.lean`):

  `muStruct_divisor_sum (n) (0<n) : divisorSumZ n muStruct = (n == 1).toNat`

i.e. `Σ_{d∣n} muStruct d = [n=1]`.  Closes the general Möbius divisor-sum (the
`corpus-mu` version remains gated by the open `muStruct = mu` bridge — frontier
`mobius_divisor_sum_general.md`).  Built on the just-closed divisor-product reindex.

Key reusable pieces (all PURE):
  * `divisorSumZ_product_reindex` — the Int (`sumZ`) divisor-product reindex for
    `g : Nat → Int` (the Int mirror of `DivisorMultiplicative.divisor_product_reindex`,
    with an Int `sumZ` toolkit: `sumZ_fubini`, `weighted_partition_by_keyZ`, …).
  * `muStruct_divisorSum_mul` — multiplicative divisor-sum
    `D(muStruct)(a·b) = D(muStruct)(a)·D(muStruct)(b)` for coprime `a,b` (reindex + `muStruct_mul`).
  * `divisorSumZ_prime_pow_reindex` — `D(g)(p^k) = Σ_{i=0}^{k} g(pⁱ)` (partition by `vp`).
  * `muStruct_prime_pow` — `muStruct(pⁱ) = mFactor i` (window-product isolation).
  * `muStruct_divisorSum_prime_pow` — `D(muStruct)(p^k) = sumMF k` (= 0 for k≥1).
  * `exists_prime_pow_cofactor` — smallest-prime-power split `n>1 → n = p^k·m`, `k≥1`,
    `gcd(p^k,m)=1`, `m<n`.

Assembly: for `n>1` split `n = p^{k+1}·m`; then `D(muStruct)(n) =
D(muStruct)(p^{k+1})·D(muStruct)(m) = 0·_ = 0` directly (no strong induction needed,
since the prime-power value already vanishes for exponent ≥ 1).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.MobiusDivisorSum

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.Valuation (vp pow_vp_dvd vp_not_dvd_succ)
open E213.Meta.Nat.VpMul (IsPrime213 vp_self_pow)
open E213.Meta.Nat.VpSeparation (exists_prime_factor dvd_iff_one_le_vp)
open E213.Lib.Math.NumberTheory.MobiusMultiplicative
  (muStruct muStruct_one muStruct_mul guarded prodFrom mFactor
   sumMF sumMF_zero sumMF_succ_eq_zero)
open E213.Lib.Math.NumberTheory.GaussTotient (mul_div_of_dvd)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (coprime_pow_left)

/-! ## §1 — Smallest-prime-power cofactor split -/

/-- `Prime213 p → IsPrime213 p` (definitional transport). -/
theorem isPrime_of_prime {p : Nat} (hp : Prime213 p) : IsPrime213 p := hp

/-- ★ **Prime-power cofactor split**: every `n > 1` factors as `p^k · m` with `p`
    prime, `k ≥ 1`, `gcd(p^k, m) = 1`, `0 < m`, `m < n`. -/
theorem exists_prime_pow_cofactor {n : Nat} (hn : 1 < n) :
    ∃ p k m, Prime213 p ∧ 1 ≤ k ∧ 0 < m ∧ m < n
      ∧ gcd213 (p ^ k) m = 1 ∧ n = p ^ k * m := by
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  have hn2 : 2 ≤ n := hn
  obtain ⟨p, hpP, hpn⟩ := exists_prime_factor n n (Nat.le_refl n) hn2
  have hp : Prime213 p := hpP
  have hp2 : 2 ≤ p := hp.1
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  -- k = vp p n, ≥ 1
  have hk1 : 1 ≤ vp p n := (dvd_iff_one_le_vp hpP hn0).mp hpn
  -- p^k ∣ n
  have hpk_dvd : p ^ (vp p n) ∣ n := pow_vp_dvd p n
  -- m = n / p^k
  have hrecon : p ^ (vp p n) * (n / p ^ (vp p n)) = n := mul_div_of_dvd hpk_dvd
  refine ⟨p, vp p n, n / p ^ (vp p n), hp, hk1, ?_, ?_, ?_, hrecon.symm⟩
  · -- 0 < m
    rcases Nat.eq_zero_or_pos (n / p ^ (vp p n)) with h0 | hpos
    · exfalso; rw [h0, Nat.mul_zero] at hrecon; rw [← hrecon] at hn0
      exact Nat.lt_irrefl 0 hn0
    · exact hpos
  · -- m < n
    have hpk_ge2 : 2 ≤ p ^ (vp p n) := by
      have : p ^ 1 ≤ p ^ (vp p n) := Nat.pow_le_pow_right hp0 hk1
      rw [Nat.pow_one] at this
      exact Nat.le_trans hp2 this
    -- m = n / p^k < n  since p^k ≥ 2 and n > 0; use n = p^k * m, m ≥ 1 ⇒ if m = n then p^k = 1
    have hmpos : 0 < n / p ^ (vp p n) := by
      rcases Nat.eq_zero_or_pos (n / p ^ (vp p n)) with h0 | hpos
      · exfalso; rw [h0, Nat.mul_zero] at hrecon; rw [← hrecon] at hn0
        exact Nat.lt_irrefl 0 hn0
      · exact hpos
    -- m < p^k * m = n
    have hlt : n / p ^ (vp p n) < p ^ (vp p n) * (n / p ^ (vp p n)) := by
      have hgt1 : 1 < p ^ (vp p n) := Nat.lt_of_lt_of_le (by decide) hpk_ge2
      have h1 : 1 * (n / p ^ (vp p n)) < p ^ (vp p n) * (n / p ^ (vp p n)) :=
        Nat.mul_lt_mul_of_lt_of_le hgt1 (Nat.le_refl _) hmpos
      rwa [Nat.one_mul] at h1
    rwa [hrecon] at hlt
  · -- gcd (p^k) m = 1
    -- ¬ p ∣ m  (else p^(k+1) ∣ n)
    have hpm : ¬ p ∣ (n / p ^ (vp p n)) := by
      intro hd
      obtain ⟨c, hc⟩ := hd
      -- n = p^k * (p*c) = p^(k+1)*c
      have hpk1 : p ^ (vp p n + 1) ∣ n := by
        refine ⟨c, ?_⟩
        -- n = p^k*(p*c) = (p^k*p)*c = p^(k+1)*c
        calc n = p ^ (vp p n) * (n / p ^ (vp p n)) := hrecon.symm
          _ = p ^ (vp p n) * (p * c) := by rw [hc]
          _ = p ^ (vp p n) * p * c :=
                (E213.Tactic.NatHelper.mul_assoc (p ^ vp p n) p c).symm
          _ = p ^ (vp p n + 1) * c := by rw [Nat.pow_succ]
      exact vp_not_dvd_succ p n hp2 hn0 hpk1
    have hcop_p : gcd213 p (n / p ^ (vp p n)) = 1 :=
      E213.Lib.Math.NumberTheory.PrimeValuation.prime_coprime_of_not_dvd hp hpm
    exact coprime_pow_left hcop_p (vp p n)

/-! ## §2 — Int `sumZ` infrastructure (mirrors the Nat `sumTo` toolkit) -/

open E213.Lib.Math.NumberTheory.MobiusFunction (sumZ divisorSumZ)
open E213.Lib.Math.NumberTheory.MobiusPrimeCase
  (sumZ_succ sumZ_const_zero sumZ_congr sumZ_split_first)
open E213.Lib.Math.NumberTheory.EulerTotient (dvdInd)
open E213.Lib.Math.NumberTheory.GaussTotient (eqInd eqInd_self eqInd_ne)

/-- `sumZ` distributes over a pointwise sum of two functions
    (`MobiusFunction.sumZ` version). -/
theorem sumZ_add_func (n : Nat) (f g : Nat → Int) :
    sumZ n f + sumZ n g = sumZ n (fun k => f k + g k) := by
  induction n with
  | zero => show (0 : Int) + 0 = 0; rw [E213.Meta.Int213.zero_add]
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, sumZ_succ, ← ih]
    show sumZ m f + f m + (sumZ m g + g m) = sumZ m f + sumZ m g + (f m + g m)
    generalize sumZ m f = A; generalize sumZ m g = B
    generalize f m = C; generalize g m = D
    rw [E213.Meta.Int213.add_assoc A C (B + D), ← E213.Meta.Int213.add_assoc C B D,
        E213.Meta.Int213.add_comm C B, E213.Meta.Int213.add_assoc B C D,
        ← E213.Meta.Int213.add_assoc A B (C + D)]

/-- Pull an Int constant out of `sumZ` (`MobiusFunction.sumZ` version). -/
theorem sumZ_mul_left (a : Int) : ∀ (n : Nat) (f : Nat → Int),
    a * sumZ n f = sumZ n (fun k => a * f k)
  | 0, _ => by show a * 0 = (0 : Int); rw [E213.Meta.Int213.PolyIntM.mul_zeroZ]
  | n + 1, f => by
    show a * (sumZ n f + f n) = sumZ n (fun k => a * f k) + a * f n
    rw [E213.Meta.Int213.mul_add, sumZ_mul_left a n f]

/-- Int Fubini for `sumZ`. -/
theorem sumZ_fubini (f : Nat → Nat → Int) : ∀ m n,
    sumZ m (fun i => sumZ n (fun j => f i j))
      = sumZ n (fun j => sumZ m (fun i => f i j))
  | 0, n => by
      show (0 : Int) = sumZ n (fun j => sumZ 0 (fun i => f i j))
      have e1 : sumZ n (fun j => sumZ 0 (fun i => f i j)) = sumZ n (fun _ => (0 : Int)) :=
        sumZ_congr n _ _ (fun _ _ => rfl)
      rw [e1]; exact (sumZ_const_zero n).symm
  | m + 1, n => by
      show sumZ m (fun i => sumZ n (fun j => f i j)) + sumZ n (fun j => f m j)
        = sumZ n (fun j => sumZ (m + 1) (fun i => f i j))
      have e2 : sumZ n (fun j => sumZ m (fun i => f i j)) + sumZ n (fun j => f m j)
              = sumZ n (fun j => sumZ m (fun i => f i j) + f m j) :=
        sumZ_add_func n (fun j => sumZ m (fun i => f i j)) (fun j => f m j)
      have e3 : sumZ n (fun j => sumZ m (fun i => f i j) + f m j)
              = sumZ n (fun j => sumZ (m + 1) (fun i => f i j)) :=
        sumZ_congr n _ _ (fun _ _ => rfl)
      rw [sumZ_fubini f m n, e2, e3]

/-- `Σ_{v<B} (eqInd c v : Int)·w = w` when `c < B`. -/
theorem sum_eqIndZ_weight_eq : ∀ (B c : Nat) (w : Int), c < B →
    sumZ B (fun v => (eqInd c v : Int) * w) = w
  | 0, c, w, h => absurd h (Nat.not_lt_zero c)
  | B + 1, c, w, h => by
    show sumZ B (fun v => (eqInd c v : Int) * w) + (eqInd c B : Int) * w = w
    by_cases hcB : c < B
    · rw [sum_eqIndZ_weight_eq B c w hcB, eqInd_ne (Nat.ne_of_lt hcB)]
      show w + ((0 : Int)) * w = w
      rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.add_comm w 0,
          E213.Meta.Int213.zero_add]
    · have hceqB : c = B :=
        Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.le_of_not_lt hcB)
      have hzero : sumZ B (fun v => (eqInd c v : Int) * w) = 0 := by
        have hc : sumZ B (fun v => (eqInd c v : Int) * w) = sumZ B (fun _ => (0 : Int)) :=
          sumZ_congr B _ _ (fun v hv => by
            show (eqInd c v : Int) * w = 0
            rw [eqInd_ne (fun he : c = v => absurd (hceqB ▸ he : B = v) (Nat.ne_of_gt hv))]
            show ((0 : Int)) * w = 0
            exact E213.Meta.Int213.zero_mul w)
        rw [hc]; exact sumZ_const_zero B
      rw [hzero, hceqB, eqInd_self]
      show (0 : Int) + ((1 : Int)) * w = w
      rw [E213.Meta.Int213.zero_add, E213.Meta.Int213.PolyIntM.one_mulZ]

/-- **Weighted partition-by-key** (Int): `Σ_{j<n} w j = Σ_{v<B} Σ_{j<n} [key j=v]·w j`. -/
theorem weighted_partition_by_keyZ (key : Nat → Nat) (w : Nat → Int) (n B : Nat)
    (hb : ∀ j, j < n → key j < B) :
    sumZ n w
      = sumZ B (fun v => sumZ n (fun j => (eqInd (key j) v : Int) * w j)) := by
  rw [sumZ_fubini (fun v j => (eqInd (key j) v : Int) * w j) B n]
  exact sumZ_congr n w (fun j => sumZ B (fun v => (eqInd (key j) v : Int) * w j))
    (fun j hj => (sum_eqIndZ_weight_eq B (key j) (w j) (hb j hj)).symm)

/-! ## §3 — Int divisor-product reindex (mirror of `divisor_product_reindex`) -/

open E213.Meta.Nat.Gcd213 (gcd213_dvd_right)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative
  (dvdInd_eq_one_iff dvdInd_eq_zero_iff dvdInd_zero_or_one survivor_gates
   gcd_strip_coprime_factor coprime_factor_right le_of_dvd_pos')
open E213.Lib.Math.NumberTheory.DivisorProductReindex
  (divisor_factorization gcd_eq_left_of_dvd coprime_of_dvd_left)
open E213.Lib.Math.NumberTheory.GaussTotient (gcd_succ_pos)
open E213.Tactic.NatHelper (sub_one_add_one)

/-- `↑(1:Nat) * a = a` over Int. -/
theorem castOne_mul (a : Int) : ((1 : Nat) : Int) * a = a :=
  E213.Meta.Int213.PolyIntM.one_mulZ a

/-- `↑(0:Nat) * a = 0` over Int. -/
theorem castZero_mul (a : Int) : ((0 : Nat) : Int) * a = 0 :=
  E213.Meta.Int213.zero_mul a

/-- **Cell pointwise identity** (Int): each flat index `j` either misses (both
    sides `0`) or sits at the survivor `j = e(k+1)−1`. -/
theorem cell_pointwiseZ {a b e k : Nat} (hab : gcd213 a b = 1) (hea : e ∣ a)
    (hepos : 0 < e) (g : Nat → Int) (j : Nat) :
    (eqInd (gcd213 (j + 1) b) (k + 1) : Int)
        * ((eqInd (gcd213 (j + 1) a) e : Int) * ((dvdInd j (a * b) : Int) * g (j + 1)))
      = (eqInd (e * (k + 1) - 1) j : Int) * ((dvdInd k b : Int) * g (e * (k + 1))) := by
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
      repeat rw [castOne_mul]
    | inl hdk =>
      have hkb : ¬ (k + 1) ∣ b := (dvdInd_eq_zero_iff k b).mp hdk
      have heb : gcd213 e b = 1 := coprime_factor_right hab hea
      have hgne : gcd213 (e * (k + 1)) b ≠ k + 1 := by
        rw [gcd_strip_coprime_factor heb]
        intro hgeq
        exact hkb (hgeq ▸ gcd213_dvd_right (k + 1) b)
      rw [eqInd_ne hgne, hdk, castZero_mul, castZero_mul,
          E213.Meta.Int213.PolyIntM.mul_zeroZ]
  | isFalse hjne =>
    -- RHS: eqInd (survivor) j = 0  ⟹  RHS = 0
    rw [eqInd_ne (fun he : e * (k + 1) - 1 = j => hjne he.symm), castZero_mul]
    cases dvdInd_zero_or_one j (a * b) with
    | inl hd0 =>
      rw [hd0, castZero_mul, E213.Meta.Int213.PolyIntM.mul_zeroZ,
          E213.Meta.Int213.PolyIntM.mul_zeroZ]
    | inr hd1 =>
      have hdvdab : (j + 1) ∣ a * b := (dvdInd_eq_one_iff j (a * b)).mp hd1
      have hfact : j + 1 = gcd213 (j + 1) a * gcd213 (j + 1) b :=
        divisor_factorization hab hdvdab
      cases Nat.decEq (gcd213 (j + 1) a) e with
      | isFalse hga =>
        rw [eqInd_ne hga, castZero_mul, E213.Meta.Int213.PolyIntM.mul_zeroZ]
      | isTrue hga =>
        cases Nat.decEq (gcd213 (j + 1) b) (k + 1) with
        | isFalse hgb =>
          rw [eqInd_ne hgb, castZero_mul]
        | isTrue hgb =>
          exfalso
          have hj1 : j + 1 = e * (k + 1) := by rw [hfact, hga, hgb]
          have hjsurv : j = e * (k + 1) - 1 := by
            rw [← hj1]; exact (E213.Tactic.NatHelper.add_sub_cancel_right j 1).symm
          exact hjne hjsurv

/-- **Single-cell sum** (Int): the inner sum at fixed `k` collapses to the survivor. -/
theorem cell_sumZ {a b e k : Nat} (hab : gcd213 a b = 1) (hea : e ∣ a)
    (hepos : 0 < e) (ha : 0 < a) (hb : 0 < b) (g : Nat → Int) :
    sumZ (a * b) (fun j => (eqInd (gcd213 (j + 1) b) (k + 1) : Int)
        * ((eqInd (gcd213 (j + 1) a) e : Int) * ((dvdInd j (a * b) : Int) * g (j + 1))))
      = (dvdInd k b : Int) * g (e * (k + 1)) := by
  rw [sumZ_congr (a * b) _
      (fun j => (eqInd (e * (k + 1) - 1) j : Int)
        * ((dvdInd k b : Int) * g (e * (k + 1))))
      (fun j _ => cell_pointwiseZ hab hea hepos g j)]
  cases dvdInd_zero_or_one k b with
  | inr hdk =>
    have hkb : (k + 1) ∣ b := (dvdInd_eq_one_iff k b).mp hdk
    have hea_le : e ≤ a := le_of_dvd_pos' ha hea
    have hkb_le : k + 1 ≤ b := le_of_dvd_pos' hb hkb
    have hprod_le : e * (k + 1) ≤ a * b := Nat.mul_le_mul hea_le hkb_le
    have hprod_pos : 0 < e * (k + 1) := Nat.mul_pos hepos (Nat.succ_pos k)
    have hlt : e * (k + 1) - 1 < a * b :=
      Nat.lt_of_lt_of_le (Nat.sub_lt hprod_pos Nat.one_pos) hprod_le
    exact sum_eqIndZ_weight_eq (a * b) (e * (k + 1) - 1)
      ((dvdInd k b : Int) * g (e * (k + 1))) hlt
  | inl hdk =>
    have hz : sumZ (a * b)
        (fun j => (eqInd (e * (k + 1) - 1) j : Int)
          * (((dvdInd k b : Int)) * g (e * (k + 1))))
        = sumZ (a * b) (fun _ => (0 : Int)) :=
      sumZ_congr (a * b) _ _ (fun j _ => by
        rw [hdk, castZero_mul, E213.Meta.Int213.PolyIntM.mul_zeroZ])
    rw [hz, sumZ_const_zero (a * b), hdk, castZero_mul]

/-- **Class collapse** (Int): the `e`-class collapses to the inner `b`-sum. -/
theorem class_collapseZ {a b e : Nat} (hab : gcd213 a b = 1) (hea : e ∣ a)
    (hepos : 0 < e) (ha : 0 < a) (hb : 0 < b) (g : Nat → Int) :
    sumZ (a * b) (fun j =>
        (eqInd (gcd213 (j + 1) a) e : Int) * ((dvdInd j (a * b) : Int) * g (j + 1)))
      = sumZ b (fun k => (dvdInd k b : Int) * g (e * (k + 1))) := by
  have hkey : ∀ j, j < a * b → gcd213 (j + 1) b < b + 1 := by
    intro j _
    exact Nat.lt_succ_of_le (le_of_dvd_pos' hb (gcd213_dvd_right (j + 1) b))
  rw [weighted_partition_by_keyZ (fun j => gcd213 (j + 1) b)
      (fun j => (eqInd (gcd213 (j + 1) a) e : Int) * ((dvdInd j (a * b) : Int) * g (j + 1)))
      (a * b) (b + 1) hkey]
  rw [sumZ_split_first b
      (fun v => sumZ (a * b) (fun j =>
        (eqInd (gcd213 (j + 1) b) v : Int)
          * ((eqInd (gcd213 (j + 1) a) e : Int) * ((dvdInd j (a * b) : Int) * g (j + 1)))))]
  have hhead : sumZ (a * b) (fun j =>
      (eqInd (gcd213 (j + 1) b) 0 : Int)
        * ((eqInd (gcd213 (j + 1) a) e : Int) * ((dvdInd j (a * b) : Int) * g (j + 1)))) = 0 := by
    have hz : sumZ (a * b) (fun j =>
        (eqInd (gcd213 (j + 1) b) 0 : Int)
          * ((eqInd (gcd213 (j + 1) a) e : Int) * ((dvdInd j (a * b) : Int) * g (j + 1))))
        = sumZ (a * b) (fun _ => (0 : Int)) :=
      sumZ_congr (a * b) _ _ (fun j _ => by
        rw [eqInd_ne (Nat.ne_of_gt (gcd_succ_pos j b)), castZero_mul])
    rw [hz]; exact sumZ_const_zero (a * b)
  rw [hhead, E213.Meta.Int213.zero_add]
  exact sumZ_congr b _ _ (fun k _ => cell_sumZ hab hea hepos ha hb g)

/-- **Class zero** (Int): if `e ∤ a` the `e`-class vanishes. -/
theorem class_zeroZ {a b e : Nat} (hea : ¬ e ∣ a) (g : Nat → Int) :
    sumZ (a * b) (fun j =>
        (eqInd (gcd213 (j + 1) a) e : Int) * ((dvdInd j (a * b) : Int) * g (j + 1))) = 0 := by
  have hz : sumZ (a * b) (fun j =>
      (eqInd (gcd213 (j + 1) a) e : Int) * ((dvdInd j (a * b) : Int) * g (j + 1)))
      = sumZ (a * b) (fun _ => (0 : Int)) :=
    sumZ_congr (a * b) _ _ (fun j _ => by
      have hne : gcd213 (j + 1) a ≠ e := fun heq => hea (heq ▸ gcd213_dvd_right (j + 1) a)
      rw [eqInd_ne hne, castZero_mul])
  rw [hz]; exact sumZ_const_zero (a * b)

/-- **Outer term** (Int): each `i`-row equals the gated inner `b`-sum. -/
theorem outer_termZ {a b : Nat} (hab : gcd213 a b = 1) (ha : 0 < a) (hb : 0 < b)
    (g : Nat → Int) (i : Nat) :
    sumZ (a * b) (fun j =>
        (eqInd (gcd213 (j + 1) a) (i + 1) : Int) * ((dvdInd j (a * b) : Int) * g (j + 1)))
      = sumZ b (fun k =>
          (dvdInd i a : Int) * (dvdInd k b : Int) * g ((i + 1) * (k + 1))) := by
  cases Nat.decEq (dvdInd i a) 1 with
  | isTrue hdi =>
    have hia : (i + 1) ∣ a := (dvdInd_eq_one_iff i a).mp hdi
    rw [class_collapseZ hab hia (Nat.succ_pos i) ha hb g]
    refine sumZ_congr b _ _ (fun k _ => ?_)
    rw [hdi, castOne_mul]
  | isFalse hdi0 =>
    have hia : ¬ (i + 1) ∣ a := by
      intro hd; exact hdi0 ((dvdInd_eq_one_iff i a).mpr hd)
    have hdi : dvdInd i a = 0 := by
      cases dvdInd_zero_or_one i a with
      | inl h => exact h
      | inr h => exact absurd h hdi0
    rw [class_zeroZ hia g]
    have hz : sumZ b (fun k =>
        (dvdInd i a : Int) * (dvdInd k b : Int) * g ((i + 1) * (k + 1)))
        = sumZ b (fun _ => (0 : Int)) :=
      sumZ_congr b _ _ (fun k _ => by
        rw [hdi, castZero_mul, E213.Meta.Int213.zero_mul])
    rw [hz, sumZ_const_zero b]

/-- ★★★ **Int divisor-product reindex**: for coprime `a,b` (`0<a`, `0<b`),
    `divisorSumZ (a·b) g = Σ_{i<a}Σ_{k<b} dvdInd i a · dvdInd k b · g((i+1)(k+1))`. -/
theorem divisorSumZ_product_reindex (a b : Nat) (hab : gcd213 a b = 1)
    (ha : 0 < a) (hb : 0 < b) (g : Nat → Int) :
    divisorSumZ (a * b) g
      = sumZ a (fun i => sumZ b (fun k =>
          (dvdInd i a : Int) * (dvdInd k b : Int) * g ((i + 1) * (k + 1)))) := by
  show sumZ (a * b) (fun j => (dvdInd j (a * b) : Int) * g (j + 1))
      = sumZ a (fun i => sumZ b (fun k =>
          (dvdInd i a : Int) * (dvdInd k b : Int) * g ((i + 1) * (k + 1))))
  have hkey : ∀ j, j < a * b → gcd213 (j + 1) a < a + 1 := by
    intro j _
    exact Nat.lt_succ_of_le (le_of_dvd_pos' ha (gcd213_dvd_right (j + 1) a))
  rw [weighted_partition_by_keyZ (fun j => gcd213 (j + 1) a)
      (fun j => (dvdInd j (a * b) : Int) * g (j + 1)) (a * b) (a + 1) hkey]
  rw [sumZ_split_first a
      (fun v => sumZ (a * b) (fun j =>
        (eqInd (gcd213 (j + 1) a) v : Int) * ((dvdInd j (a * b) : Int) * g (j + 1))))]
  have hhead : sumZ (a * b) (fun j =>
      (eqInd (gcd213 (j + 1) a) 0 : Int) * ((dvdInd j (a * b) : Int) * g (j + 1))) = 0 := by
    have hz : sumZ (a * b) (fun j =>
        (eqInd (gcd213 (j + 1) a) 0 : Int) * ((dvdInd j (a * b) : Int) * g (j + 1)))
        = sumZ (a * b) (fun _ => (0 : Int)) :=
      sumZ_congr (a * b) _ _ (fun j _ => by
        rw [eqInd_ne (Nat.ne_of_gt (gcd_succ_pos j a)), castZero_mul])
    rw [hz]; exact sumZ_const_zero (a * b)
  rw [hhead, E213.Meta.Int213.zero_add]
  exact sumZ_congr a _ _ (fun i _ => outer_termZ hab ha hb g i)

/-! ## §4 — Multiplicative divisor-sum `D(muStruct)(a·b) = D(a)·D(b)` -/

open E213.Lib.Math.NumberTheory.DivisorProductReindex (divisor_factors_coprime)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative (dvdInd_eq_one_iff dvdInd_zero_or_one)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right gcd213_comm)

/-- Two divisors of coprime numbers are coprime: `(i+1)∣a`, `(k+1)∣b`, `gcd(a,b)=1`
    `⟹ gcd(i+1, k+1) = 1`. -/
theorem coprime_of_divisors {a b u v : Nat} (hab : gcd213 a b = 1)
    (hua : u ∣ a) (hvb : v ∣ b) : gcd213 u v = 1 := by
  have h1 : gcd213 u b = 1 := coprime_of_dvd_left hab hua
  have h2 : gcd213 b u = 1 := (gcd213_comm b u).trans h1
  have h3 : gcd213 v u = 1 := coprime_of_dvd_left h2 hvb
  exact (gcd213_comm u v).trans h3

/-- On the divisor support, the reindex integrand factors multiplicatively for
    `muStruct`: `dvdInd i a · dvdInd k b · muStruct((i+1)(k+1))
      = (dvdInd i a · muStruct(i+1)) · (dvdInd k b · muStruct(k+1))`. -/
theorem muStruct_cell_factor {a b : Nat} (hab : gcd213 a b = 1) (i k : Nat) :
    (dvdInd i a : Int) * (dvdInd k b : Int) * muStruct ((i + 1) * (k + 1))
      = ((dvdInd i a : Int) * muStruct (i + 1)) * ((dvdInd k b : Int) * muStruct (k + 1)) := by
  cases dvdInd_zero_or_one i a with
  | inl hi0 =>
    rw [hi0, castZero_mul]
    show (0 : Int) * muStruct ((i + 1) * (k + 1))
       = ((0 : Nat) : Int) * muStruct (i + 1) * ((dvdInd k b : Int) * muStruct (k + 1))
    rw [castZero_mul, E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_mul]
  | inr hi1 =>
    cases dvdInd_zero_or_one k b with
    | inl hk0 =>
      rw [hk0]
      show (dvdInd i a : Int) * ((0 : Int)) * muStruct ((i + 1) * (k + 1))
         = ((dvdInd i a : Int) * muStruct (i + 1)) * (((0 : Int)) * muStruct (k + 1))
      generalize (dvdInd i a : Int) = D
      generalize muStruct (i + 1) = M1
      generalize muStruct ((i + 1) * (k + 1)) = MP
      rw [E213.Meta.Int213.PolyIntM.mul_zeroZ, E213.Meta.Int213.zero_mul,
          E213.Meta.Int213.zero_mul, E213.Meta.Int213.PolyIntM.mul_zeroZ]
    | inr hk1 =>
      have hia : (i + 1) ∣ a := (dvdInd_eq_one_iff i a).mp hi1
      have hkb : (k + 1) ∣ b := (dvdInd_eq_one_iff k b).mp hk1
      have hcop : gcd213 (i + 1) (k + 1) = 1 := coprime_of_divisors hab hia hkb
      have hmm : muStruct ((i + 1) * (k + 1)) = muStruct (i + 1) * muStruct (k + 1) :=
        muStruct_mul (Nat.succ_pos i) (Nat.succ_pos k) hcop
      rw [hmm]
      generalize (dvdInd i a : Int) = D1
      generalize (dvdInd k b : Int) = D2
      generalize muStruct (i + 1) = M1
      generalize muStruct (k + 1) = M2
      -- D1 * D2 * (M1 * M2) = (D1 * M1) * (D2 * M2)
      rw [E213.Meta.Int213.mul_mul_mul_comm D1 D2 M1 M2]

/-- The inner `b`-sum factors out the `i`-dependent part:
    `Σ_k (di·g(i+1))·(dk·g(k+1)) = (di·g(i+1)) · Σ_k dk·g(k+1)`. -/
theorem inner_factor (c : Int) (b : Nat) (h : Nat → Int) :
    sumZ b (fun k => c * h k) = c * sumZ b h :=
  (sumZ_mul_left c b h).symm

/-- Pull a right Int constant out of `sumZ`. -/
theorem sumZ_mul_right (c : Int) : ∀ (n : Nat) (f : Nat → Int),
    sumZ n (fun k => f k * c) = sumZ n f * c
  | 0, _ => by show (0 : Int) = 0 * c; rw [E213.Meta.Int213.zero_mul]
  | n + 1, f => by
    show sumZ n (fun k => f k * c) + f n * c = (sumZ n f + f n) * c
    rw [sumZ_mul_right c n f, E213.Meta.Int213.add_mul]

/-- ★★★ **Multiplicative divisor-sum for `muStruct`**: for coprime `a,b > 0`,
    `divisorSumZ (a·b) muStruct = divisorSumZ a muStruct · divisorSumZ b muStruct`. -/
theorem muStruct_divisorSum_mul {a b : Nat} (hab : gcd213 a b = 1)
    (ha : 0 < a) (hb : 0 < b) :
    divisorSumZ (a * b) muStruct
      = divisorSumZ a muStruct * divisorSumZ b muStruct := by
  rw [divisorSumZ_product_reindex a b hab ha hb muStruct]
  -- rewrite each cell to the factored form
  have hcells : sumZ a (fun i => sumZ b (fun k =>
        (dvdInd i a : Int) * (dvdInd k b : Int) * muStruct ((i + 1) * (k + 1))))
      = sumZ a (fun i => sumZ b (fun k =>
        ((dvdInd i a : Int) * muStruct (i + 1)) * ((dvdInd k b : Int) * muStruct (k + 1)))) :=
    sumZ_congr a _ _ (fun i _ =>
      sumZ_congr b _ _ (fun k _ => muStruct_cell_factor hab i k))
  rw [hcells]
  -- factor out the i-part of each inner sum
  have hfactor : sumZ a (fun i => sumZ b (fun k =>
        ((dvdInd i a : Int) * muStruct (i + 1)) * ((dvdInd k b : Int) * muStruct (k + 1))))
      = sumZ a (fun i => ((dvdInd i a : Int) * muStruct (i + 1))
          * sumZ b (fun k => (dvdInd k b : Int) * muStruct (k + 1))) :=
    sumZ_congr a _ _ (fun i _ =>
      inner_factor ((dvdInd i a : Int) * muStruct (i + 1)) b
        (fun k => (dvdInd k b : Int) * muStruct (k + 1)))
  rw [hfactor]
  -- pull the constant b-sum out of the a-sum
  rw [sumZ_mul_right (sumZ b (fun k => (dvdInd k b : Int) * muStruct (k + 1))) a
        (fun i => (dvdInd i a : Int) * muStruct (i + 1))]
  show (sumZ a (fun i => (dvdInd i a : Int) * muStruct (i + 1)))
      * (sumZ b (fun k => (dvdInd k b : Int) * muStruct (k + 1)))
    = divisorSumZ a muStruct * divisorSumZ b muStruct
  rfl

/-! ## §5 — `muStruct` on a prime power: `muStruct(pⁱ) = mFactor i` -/

open E213.Lib.Math.NumberTheory.MobiusMultiplicative
  (primB guarded_prime guarded_nonprime guarded_one_of_gt prime_of_primB
   prodFrom_zero prodFrom_succ mFactor_zero)
open E213.Lib.Math.NumberTheory.MobiusMultiplicative (prodFrom)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (dvd_prime_pow_cases)

/-- If every candidate in a window contributes `guarded = 1`, the product is `1`. -/
theorem prodFrom_all_one (n start : Nat) :
    ∀ len, (∀ j, j < len → guarded (start + j) n = 1) → prodFrom start n len = 1
  | 0, _ => prodFrom_zero start n
  | len + 1, hone => by
    rw [prodFrom_succ, hone len (Nat.lt_succ_self len), E213.Meta.Int213.mul_one]
    exact prodFrom_all_one n start len (fun j hj => hone j (Nat.lt_succ_of_lt hj))

/-- **Product isolation**: if every candidate `start+j` (`j < len`) other than
    `start + off` contributes `guarded = 1`, the window product equals
    `guarded (start+off) n` (`off < len`). -/
theorem prodFrom_isolate (n start off : Nat) :
    ∀ len, off < len →
      (∀ j, j < len → start + j ≠ start + off → guarded (start + j) n = 1) →
      prodFrom start n len = guarded (start + off) n
  | 0, hoff, _ => absurd hoff (Nat.not_lt_zero off)
  | len + 1, hoff, hone => by
    rw [prodFrom_succ]
    cases Nat.lt_or_ge off len with
    | inl hlt =>
      have hlast : guarded (start + len) n = 1 :=
        hone len (Nat.lt_succ_self len)
          (fun he => absurd (E213.Tactic.NatHelper.add_left_cancel he)
            (Nat.ne_of_gt hlt))
      rw [hlast, E213.Meta.Int213.mul_one]
      exact prodFrom_isolate n start off len hlt
        (fun j hj hne => hone j (Nat.lt_succ_of_lt hj) hne)
    | inr hge =>
      have hoffeq : off = len := Nat.le_antisymm (Nat.le_of_lt_succ hoff) hge
      subst hoffeq
      have hprefix : prodFrom start n off = 1 :=
        prodFrom_all_one n start off (fun j hj =>
          hone j (Nat.lt_succ_of_lt hj)
            (fun he => absurd (E213.Tactic.NatHelper.add_left_cancel he) (Nat.ne_of_lt hj)))
      rw [hprefix, E213.Meta.Int213.PolyIntM.one_mulZ]

open E213.Lens.Number.Nat213.MultSystemValue (decNoFactor isPrime_iff)

/-- **Completeness of `primB`**: `Prime213 p → primB p = true`. -/
theorem primB_of_prime {p : Nat} (hp : Prime213 p) : primB p = true := by
  have hP : IsPrime213 p := hp
  obtain ⟨h2p, hnf⟩ := (isPrime_iff p).mp hP
  show (match Nat.decLe 2 p with
    | isFalse _ => false
    | isTrue _ => match decNoFactor p p with
      | isFalse _ => false
      | isTrue _ => true) = true
  cases h2 : Nat.decLe 2 p with
  | isFalse hf => exact absurd h2p hf
  | isTrue _ =>
    cases h3 : decNoFactor p p with
    | isFalse hnf' => exact absurd hnf hnf'
    | isTrue _ => rfl

open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpMul (vp_self_pow)

/-- A prime `q ≠ p` does not divide `pⁱ`. -/
theorem prime_ne_not_dvd_pow {p q : Nat} (hp : Prime213 p) (hq : Prime213 q)
    (hqp : q ≠ p) (i : Nat) : ¬ q ∣ p ^ i := by
  intro hd
  rcases dvd_prime_pow_cases p hp.1 hp.2 i q hd with h1 | hpq
  · exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hq.1))
  · rcases hq.2 p hpq with hp1 | hpe
    · exact absurd hp1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hp.1))
    · exact hqp hpe.symm

/-- `guarded q (pⁱ) = 1` for a candidate `q ≠ p` with `2 ≤ q`. -/
theorem guarded_pow_ne {p : Nat} (hp : Prime213 p) {q : Nat} (hqp : q ≠ p) (i : Nat) :
    guarded q (p ^ i) = 1 := by
  cases hqB : primB q with
  | false => exact guarded_nonprime hqB
  | true =>
    have hqpr : Prime213 q := prime_of_primB hqB
    have hpi_pos : 0 < p ^ i := Nat.pos_pow_of_pos i (Nat.lt_of_lt_of_le (by decide) hp.1)
    rw [guarded_prime hqB,
        vp_eq_zero_of_not_dvd hqpr hpi_pos (prime_ne_not_dvd_pow hp hqpr hqp i)]
    exact mFactor_zero

/-- `guarded p (pⁱ) = mFactor i` for a prime `p`. -/
theorem guarded_pow_self {p : Nat} (hp : Prime213 p) (i : Nat) :
    guarded p (p ^ i) = mFactor i := by
  rw [guarded_prime (primB_of_prime hp), vp_self_pow hp i]

/-- ★★★ **`muStruct` on a prime power**: `muStruct(pⁱ) = mFactor i` for prime `p`. -/
theorem muStruct_prime_pow {p : Nat} (hp : Prime213 p) (i : Nat) :
    muStruct (p ^ i) = mFactor i := by
  have hp2 : 2 ≤ p := hp.1
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  have hpi_pos : 0 < p ^ i := Nat.pos_pow_of_pos i hp0
  cases i with
  | zero =>
    -- p^0 = 1, muStruct 1 = 1 = mFactor 0
    show muStruct (p ^ 0) = mFactor 0
    rw [Nat.pow_zero, muStruct_one, mFactor_zero]
  | succ i' =>
    -- p ≤ p^(i'+1), window contains p at offset p-2
    have hp_le : p ≤ p ^ (i' + 1) := by
      have : p ^ 1 ≤ p ^ (i' + 1) := Nat.pow_le_pow_right hp0 (Nat.succ_le_succ (Nat.zero_le i'))
      rwa [Nat.pow_one] at this
    -- muStruct N = prodFrom 2 N N, isolate the q=p factor
    show prodFrom 2 (p ^ (i' + 1)) (p ^ (i' + 1)) = mFactor (i' + 1)
    have hoff : p - 2 < p ^ (i' + 1) :=
      Nat.lt_of_lt_of_le (Nat.sub_lt hp0 (by decide)) hp_le
    have hstartoff : 2 + (p - 2) = p := by
      rw [Nat.add_comm]; exact E213.Tactic.NatHelper.sub_add_cancel hp2
    rw [prodFrom_isolate (p ^ (i' + 1)) 2 (p - 2) (p ^ (i' + 1)) hoff (fun j _ hne => by
        -- candidate 2+j ≠ p ⟹ guarded = 1
        have hjp : 2 + j ≠ p := fun he => hne (by rw [he, hstartoff])
        exact guarded_pow_ne hp hjp (i' + 1))]
    rw [hstartoff]
    exact guarded_pow_self hp (i' + 1)

/-! ## §6 — Prime-power divisor reindex `D(g)(pᵏ) = Σ_{i=0}^{k} g(pⁱ)` -/

open E213.Meta.Nat.VpSeparation (vp_separation)
open E213.Meta.Nat.Valuation (pow_vp_dvd)

/-- For `q ≠ p` prime, `vp q (pᵐ) = 0`. -/
theorem vp_other_prime_pow {p q : Nat} (hp : Prime213 p) (hq : Prime213 q)
    (hqp : q ≠ p) (m : Nat) : vp q (p ^ m) = 0 := by
  have hpm_pos : 0 < p ^ m := Nat.pos_pow_of_pos m (Nat.lt_of_lt_of_le (by decide) hp.1)
  exact vp_eq_zero_of_not_dvd hq hpm_pos (prime_ne_not_dvd_pow hp hq hqp m)

/-- A divisor of `pᵏ` equals `p^(its p-valuation)`: `0 < d → d ∣ pᵏ → d = p^(vp p d)`. -/
theorem divisor_of_prime_pow_eq {p : Nat} (hp : Prime213 p) {k d : Nat}
    (hd : 0 < d) (hdvd : d ∣ p ^ k) : d = p ^ (vp p d) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hpvpd_pos : 0 < p ^ (vp p d) := Nat.pos_pow_of_pos (vp p d) hppos
  refine vp_separation hd hpvpd_pos (fun q hq => ?_)
  by_cases hqp : q = p
  · subst hqp
    rw [vp_self_pow hq (vp q d)]
  · -- both sides 0: q ∤ d (since d ∣ p^k, q ≠ p) and vp q (p^...) = 0
    have hqnp : ¬ q ∣ p ^ k := prime_ne_not_dvd_pow hp hq hqp k
    have hqnd : ¬ q ∣ d := fun hqd =>
      hqnp (E213.Meta.Nat.Valuation.dtrans hqd hdvd)
    rw [vp_eq_zero_of_not_dvd hq hd hqnd,
        vp_other_prime_pow hp hq hqp (vp p d)]

/-- `Σ_{i=0}^{k} g(pⁱ)`, the prime-power divisor sum target (inclusive upper bound). -/
def sumPowZ (g : Nat → Int) (p : Nat) : Nat → Int
  | 0     => g (p ^ 0)
  | k + 1 => sumPowZ g p k + g (p ^ (k + 1))

/-- `pᵃ ≤ pᵇ → a ≤ b` for `p ≥ 2` (strict monotonicity of powers, contrapositive). -/
theorem pow_le_pow_imp_le {p a b : Nat} (hp : 2 ≤ p) (h : p ^ a ≤ p ^ b) : a ≤ b := by
  rcases Nat.lt_or_ge b a with hlt | hge
  · exfalso
    have : p ^ (b + 1) ≤ p ^ a := Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hp) hlt
    have hb1 : p ^ b < p ^ (b + 1) := by
      rw [Nat.pow_succ]
      have hpb_pos : 0 < p ^ b := Nat.pos_pow_of_pos b (Nat.lt_of_lt_of_le (by decide) hp)
      have hstep : 1 * p ^ b < p * p ^ b :=
        Nat.mul_lt_mul_of_lt_of_le (Nat.lt_of_lt_of_le (by decide) hp)
          (Nat.le_refl (p ^ b)) hpb_pos
      rw [Nat.one_mul] at hstep
      rw [Nat.mul_comm (p ^ b) p]; exact hstep
    exact absurd (Nat.le_trans (Nat.le_trans hb1 this) h) (Nat.lt_irrefl _)
  · exact hge

/-- For `j < pᵏ`, `vp p (j+1) ≤ k`. -/
theorem vp_succ_le_of_lt_pow {p : Nat} (hp : Prime213 p) {k j : Nat} (hj : j < p ^ k) :
    vp p (j + 1) ≤ k := by
  have hp2 : 2 ≤ p := hp.1
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  have hj1_pos : 0 < j + 1 := Nat.succ_pos j
  have hpv_dvd : p ^ (vp p (j + 1)) ∣ (j + 1) := pow_vp_dvd p (j + 1)
  have hpv_le : p ^ (vp p (j + 1)) ≤ j + 1 := le_of_dvd_pos' hj1_pos hpv_dvd
  have hj1_le : j + 1 ≤ p ^ k := hj
  exact pow_le_pow_imp_le hp2 (Nat.le_trans hpv_le hj1_le)

/-- **Prime-power cell pointwise**: for `i ≤ k`, each flat `j` either misses (both
    sides 0) or sits at the survivor `j = pⁱ − 1`, contributing `g(pⁱ)`. -/
theorem pp_cell_pointwise {p : Nat} (hp : Prime213 p) {k : Nat} (i : Nat)
    (hik : i ≤ k) (g : Nat → Int) (j : Nat) :
    (eqInd (vp p (j + 1)) i : Int) * ((dvdInd j (p ^ k) : Int) * g (j + 1))
      = (eqInd (p ^ i - 1) j : Int) * g (p ^ i) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hpi_pos : 0 < p ^ i := Nat.pos_pow_of_pos i hppos
  have hpk_pos : 0 < p ^ k := Nat.pos_pow_of_pos k hppos
  have hsurv_succ : p ^ i - 1 + 1 = p ^ i := E213.Tactic.NatHelper.sub_one_add_one
    (Nat.ne_of_gt hpi_pos)
  have hpi_dvd_pk : p ^ i ∣ p ^ k := E213.Meta.Nat.Valuation.pow_dvd_of_le p hik
  cases Nat.decEq j (p ^ i - 1) with
  | isTrue hjeq =>
    subst hjeq
    rw [eqInd_self]
    have hj1 : p ^ i - 1 + 1 = p ^ i := hsurv_succ
    -- dvdInd = 1, vp = i
    have hdv : dvdInd (p ^ i - 1) (p ^ k) = 1 :=
      (dvdInd_eq_one_iff (p ^ i - 1) (p ^ k)).mpr (hj1 ▸ hpi_dvd_pk)
    have hvp : vp p (p ^ i - 1 + 1) = i := by rw [hj1, vp_self_pow hp i]
    rw [hdv, hvp, eqInd_self, hj1]
    rw [castOne_mul, castOne_mul]
  | isFalse hjne =>
    rw [eqInd_ne (fun he : p ^ i - 1 = j => hjne he.symm)]
    show _ = ((0 : Nat) : Int) * g (p ^ i)
    rw [castZero_mul]
    cases dvdInd_zero_or_one j (p ^ k) with
    | inl hd0 => rw [hd0, castZero_mul, E213.Meta.Int213.PolyIntM.mul_zeroZ]
    | inr hd1 =>
      have hdvd : (j + 1) ∣ p ^ k := (dvdInd_eq_one_iff j (p ^ k)).mp hd1
      have hj1_pos : 0 < j + 1 := Nat.succ_pos j
      -- if vp = i then j+1 = p^i ⟹ j = p^i - 1, contradiction
      cases Nat.decEq (vp p (j + 1)) i with
      | isFalse hvpne => rw [eqInd_ne hvpne, castZero_mul]
      | isTrue hvpe =>
        exfalso
        have heq : j + 1 = p ^ (vp p (j + 1)) :=
          divisor_of_prime_pow_eq hp hj1_pos hdvd
        rw [hvpe] at heq
        have hjsurv : j = p ^ i - 1 := by
          rw [← heq]; exact (E213.Tactic.NatHelper.add_sub_cancel_right j 1).symm
        exact hjne hjsurv

/-- **Prime-power fiber sum**: for `i ≤ k`, the `vp = i` fiber collapses to `g(pⁱ)`. -/
theorem pp_cell_sum {p : Nat} (hp : Prime213 p) {k : Nat} (i : Nat)
    (hik : i ≤ k) (g : Nat → Int) :
    sumZ (p ^ k) (fun j =>
        (eqInd (vp p (j + 1)) i : Int) * ((dvdInd j (p ^ k) : Int) * g (j + 1)))
      = g (p ^ i) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hpi_pos : 0 < p ^ i := Nat.pos_pow_of_pos i hppos
  have hpk_pos : 0 < p ^ k := Nat.pos_pow_of_pos k hppos
  rw [sumZ_congr (p ^ k) _
      (fun j => (eqInd (p ^ i - 1) j : Int) * g (p ^ i))
      (fun j _ => pp_cell_pointwise hp i hik g j)]
  have hlt : p ^ i - 1 < p ^ k := by
    have hpi_le : p ^ i ≤ p ^ k := le_of_dvd_pos' hpk_pos (E213.Meta.Nat.Valuation.pow_dvd_of_le p hik)
    exact Nat.lt_of_lt_of_le (Nat.sub_lt hpi_pos Nat.one_pos) hpi_le
  exact sum_eqIndZ_weight_eq (p ^ k) (p ^ i - 1) (g (p ^ i)) hlt

/-- `Σ_{i<k+1} g(pⁱ) = sumPowZ g p k`. -/
theorem sumZ_eq_sumPowZ (g : Nat → Int) (p : Nat) :
    ∀ k, sumZ (k + 1) (fun i => g (p ^ i)) = sumPowZ g p k
  | 0 => by
    show sumZ 1 (fun i => g (p ^ i)) = g (p ^ 0)
    show sumZ 0 (fun i => g (p ^ i)) + g (p ^ 0) = g (p ^ 0)
    show (0 : Int) + g (p ^ 0) = g (p ^ 0)
    rw [E213.Meta.Int213.zero_add]
  | k + 1 => by
    show sumZ (k + 2) (fun i => g (p ^ i)) = sumPowZ g p k + g (p ^ (k + 1))
    rw [sumZ_succ]
    show sumZ (k + 1) (fun i => g (p ^ i)) + g (p ^ (k + 1))
       = sumPowZ g p k + g (p ^ (k + 1))
    rw [sumZ_eq_sumPowZ g p k]

/-- ★★★ **Prime-power divisor reindex**: `divisorSumZ (pᵏ) g = Σ_{i=0}^{k} g(pⁱ)`. -/
theorem divisorSumZ_prime_pow_reindex {p : Nat} (hp : Prime213 p) (k : Nat) (g : Nat → Int) :
    divisorSumZ (p ^ k) g = sumPowZ g p k := by
  show sumZ (p ^ k) (fun j => (dvdInd j (p ^ k) : Int) * g (j + 1)) = sumPowZ g p k
  have hkey : ∀ j, j < p ^ k → vp p (j + 1) < k + 1 := by
    intro j hj
    exact Nat.lt_succ_of_le (vp_succ_le_of_lt_pow hp hj)
  rw [weighted_partition_by_keyZ (fun j => vp p (j + 1))
      (fun j => (dvdInd j (p ^ k) : Int) * g (j + 1)) (p ^ k) (k + 1) hkey]
  have hfibers : sumZ (k + 1) (fun i => sumZ (p ^ k) (fun j =>
        (eqInd (vp p (j + 1)) i : Int) * ((dvdInd j (p ^ k) : Int) * g (j + 1))))
      = sumZ (k + 1) (fun i => g (p ^ i)) :=
    sumZ_congr (k + 1) _ _ (fun i hi =>
      pp_cell_sum hp i (Nat.le_of_lt_succ hi) g)
  rw [hfibers, sumZ_eq_sumPowZ g p k]

/-! ## §7 — The prime-power value `D(muStruct)(pᵏ) = [k=0]` -/

/-- `sumPowZ muStruct p k = sumMF k`: the prime-power divisor sum of `muStruct`
    reduces to the abstract `Σ mFactor` (via `muStruct(pⁱ) = mFactor i`). -/
theorem sumPowZ_muStruct_eq_sumMF {p : Nat} (hp : Prime213 p) :
    ∀ k, sumPowZ muStruct p k = sumMF k
  | 0 => by
    show muStruct (p ^ 0) = sumMF 0
    rw [muStruct_prime_pow hp 0, sumMF_zero]; rfl
  | k + 1 => by
    show sumPowZ muStruct p k + muStruct (p ^ (k + 1)) = sumMF (k + 1)
    show sumPowZ muStruct p k + muStruct (p ^ (k + 1)) = sumMF k + mFactor (k + 1)
    rw [sumPowZ_muStruct_eq_sumMF hp k, muStruct_prime_pow hp (k + 1)]

/-- ★★★ **Prime-power value of the `muStruct` divisor sum**:
    `divisorSumZ (pᵏ) muStruct = sumMF k` ( = `1` if `k=0`, else `0`). -/
theorem muStruct_divisorSum_prime_pow {p : Nat} (hp : Prime213 p) (k : Nat) :
    divisorSumZ (p ^ k) muStruct = sumMF k := by
  rw [divisorSumZ_prime_pow_reindex hp k muStruct, sumPowZ_muStruct_eq_sumMF hp k]

/-- ★★★ **Prime-power value collapses to zero** for `k ≥ 1`:
    `divisorSumZ (p^(k+1)) muStruct = 0`. -/
theorem muStruct_divisorSum_prime_pow_succ {p : Nat} (hp : Prime213 p) (k : Nat) :
    divisorSumZ (p ^ (k + 1)) muStruct = 0 := by
  rw [muStruct_divisorSum_prime_pow hp (k + 1), sumMF_succ_eq_zero k]

/-! ## §8 — Assembly: the general structural Möbius divisor sum -/

/-- `divisorSumZ 1 muStruct = 1` (the only divisor of `1` is `1`, `muStruct 1 = 1`). -/
theorem muStruct_divisorSum_one : divisorSumZ 1 muStruct = 1 := by
  show sumZ 1 (fun j => (dvdInd j 1 : Int) * muStruct (j + 1)) = 1
  show sumZ 0 (fun j => (dvdInd j 1 : Int) * muStruct (j + 1))
      + (dvdInd 0 1 : Int) * muStruct (0 + 1) = 1
  show (0 : Int) + (dvdInd 0 1 : Int) * muStruct 1 = 1
  have hd : dvdInd 0 1 = 1 := (dvdInd_eq_one_iff 0 1).mpr ⟨1, rfl⟩
  rw [hd, muStruct_one, E213.Meta.Int213.zero_add, castOne_mul]

/-- ★★★ **General structural Möbius divisor sum**:
    `∀ n, 0 < n → divisorSumZ n muStruct = (if n = 1 then 1 else 0)`,
    expressed via the `Bool`-indicator `(n == 1)` cast to `Int`
    (`= 1` when `n = 1`, else `0`). -/
theorem muStruct_divisor_sum (n : Nat) (hn : 0 < n) :
    divisorSumZ n muStruct = ((n == 1).toNat : Int) := by
  cases Nat.lt_or_ge n 2 with
  | inl hlt =>
    -- n = 1
    have hn1 : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hn
    subst hn1
    rw [muStruct_divisorSum_one]; rfl
  | inr hge =>
    -- n ≥ 2: split off a prime power, divisor-sum is 0
    have hgt1 : 1 < n := hge
    obtain ⟨p, k, m, hp, hk1, hm0, _, hcop, hnpk⟩ := exists_prime_pow_cofactor hgt1
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := match k, hk1 with
      | j + 1, _ => ⟨j, rfl⟩
    have hpk_pos : 0 < p ^ (k' + 1) :=
      Nat.pos_pow_of_pos (k' + 1) (Nat.lt_of_lt_of_le (by decide) hp.1)
    -- n = p^(k'+1) * m  ⟹  D(n) = D(p^(k'+1)) * D(m) = 0 * _ = 0
    rw [hnpk, muStruct_divisorSum_mul hcop hpk_pos hm0,
        muStruct_divisorSum_prime_pow_succ hp k', E213.Meta.Int213.zero_mul]
    -- RHS: n ≥ 2 ⟹ (n == 1) = false ⟹ toNat = 0
    have hne1 : ¬ n = 1 := fun he => absurd (he ▸ hge) (by decide)
    rw [hnpk] at hne1
    show (0 : Int) = ((p ^ (k' + 1) * m == 1).toNat : Int)
    rw [E213.Meta.Nat.Beq213.nat_beq_op_eq_false_of_ne hne1]; rfl

end E213.Lib.Math.NumberTheory.MobiusDivisorSum
