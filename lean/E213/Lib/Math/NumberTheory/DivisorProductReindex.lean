import E213.Meta.Nat.Gcd213
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Meta.Nat.PolyNatMTactic
import E213.Lib.Math.NumberTheory.EulerTotient
import E213.Lib.Math.NumberTheory.SumOfDivisors
import E213.Lib.Math.Combinatorics.SumReshape
import E213.Lib.Math.NumberTheory.FactorialLcmIdentity
import E213.Lib.Math.NumberTheory.GaussTotient

/-!
# Divisor-product structure toward σ/τ multiplicativity (∅-axiom)

The reusable infrastructure for **multiplicative-function divisor sums**, built up
to the single remaining combinatorial gap (a sparse-fiber sum reindex).

  * ★★ `gcd_mul_coprime` — **gcd is multiplicative over coprime products**:
        `gcd(a,b)=1 → gcd(d, a·b) = gcd(d,a)·gcd(d,b)` (corpus-absent before; the
        corpus had only `gcd213_mul_left` scaling and `coprime_mul_iff`).
  * ★★ `divisor_factorization` — coprime `a,b`: every `d ∣ a·b` splits uniquely
        `d = gcd(d,a)·gcd(d,b)` (+ `divisor_factors_coprime` = injectivity witness).
  * `divisorSum_mul_as_grid` — the EASY direction: the `a×b` divisor-grid double
        sum factors as `divisorSum a f · divisorSum b f` (pure `sumTo` algebra).
  * ★ `weighted_partition_by_key` — reusable *weighted* disjoint-cover
        (`GaussTotient.count_partition_by_key` is the `w≡1` case).
  * ★★ `gcd_fiber_forward` — fiber condition `e∣a, gcd(a,b)=1, d₂∣b ⟹ gcd(e·d₂,a)=e`.
  * `sigma_mul_of_reindex`, `tau_mul_of_reindex` — conditional unlock: the reindex
        hypothesis ⟹ σ / τ multiplicative.

The
`divisor_product_reindex` `divisorSum (a·b) f = Σ_{i<a}Σ_{k<b} dvdInd i a·dvdInd k b·f((i+1)(k+1))`.
All forward arithmetic is in hand; the one missing ingredient is a general
**sum-reindex-by-bijection over `sumTo` for a sparse (non-contiguous) fiber**
(`sumTo_reshape` only isolates contiguous blocks, as in `GaussTotient.gcd_class_count`).
This single tool would land σ/τ multiplicativity, the general Möbius divisor-sum,
and Möbius inversion at once.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.DivisorProductReindex

open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213
  (gcd213_dvd_left gcd213_dvd_right gcd213_greatest gcd213_comm gcd213_self
   gcd213_mul_left coprime_dvd_of_dvd_mul dvd_antisymm_213 mul_assoc_213)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
  (dvd_trans_213 eq_one_of_dvd_one coprime_mul_of_coprime
   coprime_of_coprime_mul_left coprime_of_coprime_mul_right coprime_mul_iff
   gcd213_one_right)

/-! ## Basic divisor facts -/

/-- `d ∣ n → gcd213 d n = d`. -/
theorem gcd_eq_left_of_dvd {d n : Nat} (h : d ∣ n) : gcd213 d n = d := by
  apply dvd_antisymm_213
  · exact gcd213_dvd_left d n
  · exact gcd213_greatest d n d ⟨1, (Nat.mul_one d).symm⟩ h

/-- Coprime divisors of `n` have product dividing `n`. -/
theorem coprime_mul_dvd {g1 g2 n : Nat} (h1 : g1 ∣ n) (h2 : g2 ∣ n)
    (hc : gcd213 g1 g2 = 1) : g1 * g2 ∣ n := by
  obtain ⟨c, hc1⟩ := h1
  have hg2c : g2 ∣ c := by
    have hco : gcd213 g2 g1 = 1 := (gcd213_comm g2 g1).trans hc
    have hd : g2 ∣ g1 * c := hc1 ▸ h2
    exact coprime_dvd_of_dvd_mul hco hd
  obtain ⟨w, hw⟩ := hg2c
  exact ⟨w, by rw [hc1, hw, mul_assoc_213]⟩

/-- `gcd(a,b)=1 → gcd(gcd(d,a), gcd(d,b)) = 1`. -/
theorem coprime_gcd_gcd {a b d : Nat} (hab : gcd213 a b = 1) :
    gcd213 (gcd213 d a) (gcd213 d b) = 1 := by
  have hga : gcd213 (gcd213 d a) (gcd213 d b) ∣ a :=
    dvd_trans_213 (gcd213_dvd_left (gcd213 d a) (gcd213 d b)) (gcd213_dvd_right d a)
  have hgb : gcd213 (gcd213 d a) (gcd213 d b) ∣ b :=
    dvd_trans_213 (gcd213_dvd_right (gcd213 d a) (gcd213 d b)) (gcd213_dvd_right d b)
  have hgab : gcd213 (gcd213 d a) (gcd213 d b) ∣ gcd213 a b :=
    gcd213_greatest a b _ hga hgb
  exact eq_one_of_dvd_one (hab ▸ hgab)

/-! ## Forward divisibility -/

/-- **Forward divisibility**: if `x ∣ a·b` and `gcd(a,b)=1` then
    `x ∣ gcd(x,a)·gcd(x,b)`. -/
theorem dvd_gcd_mul_gcd {x a b : Nat} (hxab : x ∣ a * b) :
    x ∣ gcd213 x a * gcd213 x b := by
  have hkey : gcd213 x a * gcd213 x b
            = gcd213 (gcd213 x a * x) (gcd213 x a * b) := (gcd213_mul_left (gcd213 x a) x b).symm
  rw [hkey]
  refine gcd213_greatest (gcd213 x a * x) (gcd213 x a * b) x ?_ ?_
  · exact ⟨gcd213 x a, by rw [Nat.mul_comm]⟩
  · have h1 : x ∣ a * b := hxab
    have h2 : x ∣ x * b := ⟨b, rfl⟩
    have h3 : x ∣ gcd213 (a * b) (x * b) := gcd213_greatest (a * b) (x * b) x h1 h2
    have h4 : gcd213 (a * b) (x * b) = b * gcd213 a x := by
      rw [Nat.mul_comm a b, Nat.mul_comm x b]
      exact gcd213_mul_left b a x
    rw [h4] at h3
    rw [Nat.mul_comm (gcd213 x a) b, gcd213_comm x a]
    exact h3

/-! ## gcd-product multiplicativity -/

/-- ★★ **gcd is multiplicative over coprime products**:
    `gcd(a,b)=1 → gcd(d, a·b) = gcd(d,a)·gcd(d,b)`. -/
theorem gcd_mul_coprime {a b d : Nat} (hab : gcd213 a b = 1) :
    gcd213 d (a * b) = gcd213 d a * gcd213 d b := by
  apply dvd_antisymm_213
  · have hdvd_ab : gcd213 d (a * b) ∣ a * b := gcd213_dvd_right d (a * b)
    have hdvd_d : gcd213 d (a * b) ∣ d := gcd213_dvd_left d (a * b)
    have hstep : gcd213 d (a * b)
               ∣ gcd213 (gcd213 d (a * b)) a * gcd213 (gcd213 d (a * b)) b :=
      dvd_gcd_mul_gcd hdvd_ab
    have hfa : gcd213 (gcd213 d (a * b)) a ∣ gcd213 d a :=
      gcd213_greatest d a _
        (dvd_trans_213 (gcd213_dvd_left (gcd213 d (a * b)) a) hdvd_d)
        (gcd213_dvd_right (gcd213 d (a * b)) a)
    have hfb : gcd213 (gcd213 d (a * b)) b ∣ gcd213 d b :=
      gcd213_greatest d b _
        (dvd_trans_213 (gcd213_dvd_left (gcd213 d (a * b)) b) hdvd_d)
        (gcd213_dvd_right (gcd213 d (a * b)) b)
    obtain ⟨ua, hua⟩ := hfa
    obtain ⟨ub, hub⟩ := hfb
    have hprod : gcd213 (gcd213 d (a * b)) a * gcd213 (gcd213 d (a * b)) b
               ∣ gcd213 d a * gcd213 d b := by
      refine ⟨ua * ub, ?_⟩
      rw [hua, hub]
      ring_nat
    exact dvd_trans_213 hstep hprod
  · have hd : gcd213 d a * gcd213 d b ∣ d :=
      coprime_mul_dvd (gcd213_dvd_left d a) (gcd213_dvd_left d b)
        (coprime_gcd_gcd hab)
    have hab2 : gcd213 d a * gcd213 d b ∣ a * b := by
      obtain ⟨ca, hca⟩ := gcd213_dvd_right d a
      obtain ⟨cb, hcb⟩ := gcd213_dvd_right d b
      refine ⟨ca * cb, ?_⟩
      have hexpand : (gcd213 d a * ca) * (gcd213 d b * cb)
                   = gcd213 d a * gcd213 d b * (ca * cb) := by ring_nat
      rw [← hexpand, ← hca, ← hcb]
    exact gcd213_greatest d (a * b) _ hd hab2

/-- ★★ **Divisor factorization**: for coprime `a,b`, every `d ∣ a·b` factors as
    `d = gcd(d,a)·gcd(d,b)` (the unique coprime split). -/
theorem divisor_factorization {a b d : Nat} (hab : gcd213 a b = 1) (hd : d ∣ a * b) :
    d = gcd213 d a * gcd213 d b :=
  (gcd_eq_left_of_dvd hd).symm.trans (gcd_mul_coprime hab)

/-- The two factors of a divisor of `a·b` are themselves coprime. -/
theorem divisor_factors_coprime {a b d : Nat} (hab : gcd213 a b = 1) :
    gcd213 (gcd213 d a) (gcd213 d b) = 1 := coprime_gcd_gcd hab

theorem divisor_factor_dvd_left (a b d : Nat) : gcd213 d a ∣ a := gcd213_dvd_right d a
theorem divisor_factor_dvd_right (a b d : Nat) : gcd213 d b ∣ b := gcd213_dvd_right d b

/-! ## Grid double-sum = product of divisor-sums (the EASY direction) -/

open E213.Lib.Math.NumberTheory.EulerTotient (divisorSum dvdInd)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr sumTo_mul_left)

/-- The product `divisorSum a f · divisorSum b f` as a grid double sum. -/
theorem divisorSum_mul_as_grid (a b : Nat) (f : Nat → Nat) :
    divisorSum a f * divisorSum b f
      = sumTo a (fun i => sumTo b (fun k =>
          (dvdInd i a * f (i + 1)) * (dvdInd k b * f (k + 1)))) := by
  show (sumTo a (fun i => dvdInd i a * f (i + 1)))
        * (sumTo b (fun k => dvdInd k b * f (k + 1)))
      = sumTo a (fun i => sumTo b (fun k =>
          (dvdInd i a * f (i + 1)) * (dvdInd k b * f (k + 1))))
  rw [Nat.mul_comm (sumTo a (fun i => dvdInd i a * f (i + 1)))
        (sumTo b (fun k => dvdInd k b * f (k + 1)))]
  rw [sumTo_mul_left (sumTo b (fun k => dvdInd k b * f (k + 1))) a
        (fun i => dvdInd i a * f (i + 1))]
  refine sumTo_congr a _ _ (fun i _ => ?_)
  rw [Nat.mul_comm (sumTo b (fun k => dvdInd k b * f (k + 1))) (dvdInd i a * f (i + 1))]
  rw [sumTo_mul_left (dvdInd i a * f (i + 1)) b (fun k => dvdInd k b * f (k + 1))]

/-! ## Weighted partition-by-key (reusable) -/

open E213.Lib.Math.NumberTheory.GaussTotient (eqInd eqInd_self eqInd_ne)
open E213.Lib.Math.NumberTheory.FactorialLcmIdentity (sumTo_const_zero sumTo_fubini)

/-- `Σ_{v<B} [c=v]·w = w` when `c < B`. -/
theorem sum_eqInd_weight_eq : ∀ (B c w : Nat), c < B →
    sumTo B (fun v => eqInd c v * w) = w
  | 0, c, w, h => absurd h (Nat.not_lt_zero c)
  | B + 1, c, w, h => by
    show sumTo B (fun v => eqInd c v * w) + eqInd c B * w = w
    by_cases hcB : c < B
    · rw [sum_eqInd_weight_eq B c w hcB, eqInd_ne (Nat.ne_of_lt hcB), Nat.zero_mul,
          Nat.add_zero]
    · have hceqB : c = B :=
        Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.le_of_not_lt hcB)
      have hzero : sumTo B (fun v => eqInd c v * w) = 0 := by
        rw [sumTo_congr B (fun v => eqInd c v * w) (fun _ => 0) (fun v hv => ?_)]
        · exact sumTo_const_zero B
        · show eqInd c v * w = 0
          rw [eqInd_ne (fun he : c = v => absurd (hceqB ▸ he : B = v) (Nat.ne_of_gt hv)),
              Nat.zero_mul]
      rw [hzero, hceqB, eqInd_self, Nat.one_mul, Nat.zero_add]

/-- ★ **Weighted partition-by-key**:
    `Σ_{j<n} w j = Σ_{v<B} Σ_{j<n} [key j = v]·w j` (when `key j < B`). -/
theorem weighted_partition_by_key (key w : Nat → Nat) (n B : Nat)
    (hb : ∀ j, j < n → key j < B) :
    sumTo n w
      = sumTo B (fun v => sumTo n (fun j => eqInd (key j) v * w j)) := by
  rw [sumTo_fubini (fun v j => eqInd (key j) v * w j) B n]
  exact sumTo_congr n w (fun j => sumTo B (fun v => eqInd (key j) v * w j))
    (fun j hj => (sum_eqInd_weight_eq B (key j) (w j) (hb j hj)).symm)

/-! ## Fiber-condition arithmetic -/

open E213.Lib.Math.NumberTheory.GaussTotient (mul_div_of_dvd)

/-- `gcd(a,b)=1 → a' ∣ a → gcd(a',b)=1`. -/
theorem coprime_of_dvd_left {a b a' : Nat} (hab : gcd213 a b = 1) (h : a' ∣ a) :
    gcd213 a' b = 1 := by
  obtain ⟨c, hc⟩ := h
  have hba : gcd213 b a = 1 := (gcd213_comm b a).trans hab
  rw [hc] at hba
  have hba' : gcd213 b a' = 1 := coprime_of_coprime_mul_left hba
  exact (gcd213_comm a' b).trans hba'

/-- ★★ **Fiber condition (forward)**: for `e ∣ a`, `gcd(a,b)=1`, `d₂ ∣ b`,
    `gcd(e·d₂, a) = e`. -/
theorem gcd_fiber_forward {a b e d2 : Nat} (hab : gcd213 a b = 1)
    (hea : e ∣ a) (hd2 : d2 ∣ b) (hepos : 0 < e) : gcd213 (e * d2) a = e := by
  have hcof : e * (a / e) = a := mul_div_of_dvd hea
  have ha'dvd : (a / e) ∣ a := ⟨e, by rw [Nat.mul_comm]; exact hcof.symm⟩
  have hcop_a'b : gcd213 (a / e) b = 1 := coprime_of_dvd_left hab ha'dvd
  have hcop_a'd2 : gcd213 (a / e) d2 = 1 := by
    obtain ⟨c, hc⟩ := hd2
    rw [hc] at hcop_a'b
    exact coprime_of_coprime_mul_left hcop_a'b
  have hcop_d2a' : gcd213 d2 (a / e) = 1 := (gcd213_comm d2 (a / e)).trans hcop_a'd2
  calc gcd213 (e * d2) a
      = gcd213 (e * d2) (e * (a / e)) := by rw [hcof]
    _ = e * gcd213 d2 (a / e) := gcd213_mul_left e d2 (a / e)
    _ = e * 1 := by rw [hcop_d2a']
    _ = e := Nat.mul_one e

/-! ## Conditional multiplicativity: reindex ⟹ `sigma_mul` / `tau_mul` -/

open E213.Lib.Math.NumberTheory.SumOfDivisors (sigma tau)

/-- ★ **Conditional `sigma`-multiplicativity**: given the divisor-product reindex
    for `f = id` on `a·b`, `sigma (a·b) = sigma a · sigma b`. -/
theorem sigma_mul_of_reindex {a b : Nat}
    (Hreindex : divisorSum (a * b) (fun d => d)
      = sumTo a (fun i => sumTo b (fun k =>
          dvdInd i a * dvdInd k b * ((i + 1) * (k + 1))))) :
    sigma (a * b) = sigma a * sigma b := by
  show divisorSum (a * b) (fun d => d) = divisorSum a (fun d => d) * divisorSum b (fun d => d)
  rw [divisorSum_mul_as_grid a b (fun d => d), Hreindex]
  refine sumTo_congr a _ _ (fun i _ => sumTo_congr b _ _ (fun k _ => ?_))
  generalize dvdInd i a = DA
  generalize dvdInd k b = DB
  ring_nat

/-- ★ **Conditional `tau`-multiplicativity**: given the divisor-product reindex
    for `f ≡ 1`, `tau (a·b) = tau a · tau b`. -/
theorem tau_mul_of_reindex {a b : Nat}
    (Hreindex : divisorSum (a * b) (fun _ => 1)
      = sumTo a (fun i => sumTo b (fun k =>
          dvdInd i a * dvdInd k b * (1 * 1)))) :
    tau (a * b) = tau a * tau b := by
  show divisorSum (a * b) (fun _ => 1) = divisorSum a (fun _ => 1) * divisorSum b (fun _ => 1)
  rw [divisorSum_mul_as_grid a b (fun _ => 1), Hreindex]
  refine sumTo_congr a _ _ (fun i _ => sumTo_congr b _ _ (fun k _ => ?_))
  generalize dvdInd i a = DA
  generalize dvdInd k b = DB
  ring_nat

end E213.Lib.Math.NumberTheory.DivisorProductReindex
