import E213.Lib.Math.NumberTheory.DirichletConvolution
import E213.Lib.Math.NumberTheory.SummatoryMultiplicative
import E213.Lib.Math.NumberTheory.MobiusDivisorSum

/-!
# Dirichlet convolution of two multiplicative functions is multiplicative (∅-axiom)

★★★ `dconv_mul` : `f,g` multiplicative on coprime pairs ⟹ `f∗g` multiplicative:
  `gcd(a,b)=1 → 0<a → 0<b → dconv f g (a·b) = dconv f g a · dconv f g b`.

This is the central structural theorem of the Dirichlet ring (the multiplicative
counterpart of `dirichlet_comm`/`dirichlet_assoc`).  The Nat `summatory_mul` is the
`g≡1` special case; this is the full convolution version over `Int`.

Engine (all reused):
  * `MobiusDivisorSum.divisorSumZ_product_reindex` — Int grid reindex (for ANY `G`),
    applied with `G(d) = f(d)·g((a·b)/d)`.
  * `MobiusDivisorSum.coprime_of_divisors` — cell coprimality `gcd(i+1,k+1)=1`.
  * `DivisorMultiplicative.dvdInd_zero_or_one`/`dvdInd_eq_one_iff` — cell case split.

The ONLY new ingredient over `summatory_mul`/`muStruct_divisorSum_mul` is the
**cofactor split** `(a·b)/((i+1)(k+1)) = (a/(i+1))·(b/(k+1))` and the coprimality of
the cofactors `a/(i+1) ⊥ b/(k+1)`, giving `g(cofactor) = g(a/(i+1))·g(b/(k+1))`.
-/

namespace E213.Lib.Math.NumberTheory.DirichletMultiplicative

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.MobiusFunction (sumZ divisorSumZ)
open E213.Lib.Math.NumberTheory.MobiusPrimeCase (sumZ_congr sumZ_const_zero)
open E213.Lib.Math.NumberTheory.EulerTotient (dvdInd)
open E213.Lib.Math.NumberTheory.GaussTotient (mul_div_of_dvd)
open E213.Lib.Math.NumberTheory.DirichletConvolution (dconv)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative
  (dvdInd_eq_one_iff dvdInd_zero_or_one coprime_factor_right)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum
  (divisorSumZ_product_reindex coprime_of_divisors castZero_mul castOne_mul
   inner_factor sumZ_mul_right)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure)

/-! ## §1 — Cofactor split (the new ingredient) -/

/-- **Cofactor split**: for `u ∣ a`, `v ∣ b` (`0<u`, `0<v`),
    `(a·b)/(u·v) = (a/u)·(b/v)`. -/
theorem cofactor_split {a b u v : Nat} (hua : u ∣ a) (hvb : v ∣ b)
    (hu : 0 < u) (hv : 0 < v) :
    (a * b) / (u * v) = (a / u) * (b / v) := by
  have hau : u * (a / u) = a := mul_div_of_dvd hua
  have hbv : v * (b / v) = b := mul_div_of_dvd hvb
  have huv : 0 < u * v := Nat.mul_pos hu hv
  -- a·b = (u·v)·((a/u)·(b/v))
  have hrw : a * b = (u * v) * ((a / u) * (b / v)) := by
    calc a * b = (u * (a / u)) * (v * (b / v)) := by rw [hau, hbv]
      _ = (u * v) * ((a / u) * (b / v)) :=
        E213.Tactic.NatHelper.mul_mul_mul_comm_213 u (a / u) v (b / v)
  rw [hrw, mul_div_cancel_left_pure (u * v) ((a / u) * (b / v)) huv]

/-! ## §2 — Cofactor coprimality -/

/-- **Cofactor coprimality**: divisors `u/`, `v/` of coprime `a,b` have coprime
    cofactors `(a/u) ⊥ (b/v)` (since `a/u ∣ a`, `b/v ∣ b`). -/
theorem cofactor_coprime {a b u v : Nat} (hab : gcd213 a b = 1)
    (hua : u ∣ a) (hvb : v ∣ b) : gcd213 (a / u) (b / v) = 1 := by
  have hda : (a / u) ∣ a := ⟨u, (mul_div_of_dvd hua).symm.trans (Nat.mul_comm u (a / u))⟩
  have hdb : (b / v) ∣ b := ⟨v, (mul_div_of_dvd hvb).symm.trans (Nat.mul_comm v (b / v))⟩
  exact coprime_of_divisors hab hda hdb

/-! ## §3 — Cell factorization with the cofactor `g`-split -/

/-- **Cell factorization** for two multiplicative `f,g`: on each surviving grid cell
    `d = (i+1)(k+1)` the integrand `dvdInd i a · dvdInd k b · (f(d)·g((a·b)/d))` factors
    into the `a`-cell `(dvdInd i a · (f(i+1)·g(a/(i+1))))` times the `b`-cell.
    Guarded by `dvdInd`-value case split so `hf`/`hg`/the cofactor split are used only
    on surviving cells. -/
theorem cell_factor (f g : Nat → Int)
    (hf : ∀ x y, gcd213 x y = 1 → f (x * y) = f x * f y)
    (hg : ∀ x y, gcd213 x y = 1 → g (x * y) = g x * g y)
    {a b : Nat} (hab : gcd213 a b = 1) (i k : Nat) :
    (dvdInd i a : Int) * (dvdInd k b : Int)
        * (f ((i + 1) * (k + 1)) * g ((a * b) / ((i + 1) * (k + 1))))
      = ((dvdInd i a : Int) * (f (i + 1) * g (a / (i + 1))))
        * ((dvdInd k b : Int) * (f (k + 1) * g (b / (k + 1)))) := by
  cases dvdInd_zero_or_one i a with
  | inl hi0 =>
    rw [hi0, castZero_mul]
    show (0 : Int) * (f ((i + 1) * (k + 1)) * g ((a * b) / ((i + 1) * (k + 1))))
       = (((0 : Nat) : Int) * (f (i + 1) * g (a / (i + 1))))
         * ((dvdInd k b : Int) * (f (k + 1) * g (b / (k + 1))))
    rw [castZero_mul, E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_mul]
  | inr hi1 =>
    cases dvdInd_zero_or_one k b with
    | inl hk0 =>
      rw [hk0]
      show (dvdInd i a : Int) * ((0 : Int))
            * (f ((i + 1) * (k + 1)) * g ((a * b) / ((i + 1) * (k + 1))))
         = ((dvdInd i a : Int) * (f (i + 1) * g (a / (i + 1))))
           * (((0 : Int)) * (f (k + 1) * g (b / (k + 1))))
      generalize (dvdInd i a : Int) = D
      generalize f (i + 1) * g (a / (i + 1)) = M1
      generalize f ((i + 1) * (k + 1)) * g ((a * b) / ((i + 1) * (k + 1))) = MP
      generalize f (k + 1) * g (b / (k + 1)) = M2
      rw [E213.Meta.Int213.PolyIntM.mul_zeroZ, E213.Meta.Int213.zero_mul,
          E213.Meta.Int213.zero_mul, E213.Meta.Int213.PolyIntM.mul_zeroZ]
    | inr hk1 =>
      have hia : (i + 1) ∣ a := (dvdInd_eq_one_iff i a).mp hi1
      have hkb : (k + 1) ∣ b := (dvdInd_eq_one_iff k b).mp hk1
      have hcop : gcd213 (i + 1) (k + 1) = 1 := coprime_of_divisors hab hia hkb
      have hfm : f ((i + 1) * (k + 1)) = f (i + 1) * f (k + 1) := hf _ _ hcop
      -- cofactor split + cofactor coprimality + hg
      have hcofeq : (a * b) / ((i + 1) * (k + 1)) = (a / (i + 1)) * (b / (k + 1)) :=
        cofactor_split hia hkb (Nat.succ_pos i) (Nat.succ_pos k)
      have hcofcop : gcd213 (a / (i + 1)) (b / (k + 1)) = 1 :=
        cofactor_coprime hab hia hkb
      have hgm : g ((a * b) / ((i + 1) * (k + 1)))
          = g (a / (i + 1)) * g (b / (k + 1)) := by
        rw [hcofeq]; exact hg _ _ hcofcop
      rw [hfm, hgm]
      generalize (dvdInd i a : Int) = D1
      generalize (dvdInd k b : Int) = D2
      generalize f (i + 1) = F1
      generalize f (k + 1) = F2
      generalize g (a / (i + 1)) = G1
      generalize g (b / (k + 1)) = G2
      -- D1·D2·((F1·F2)·(G1·G2)) = (D1·(F1·G1))·(D2·(F2·G2))
      ring_intZ

/-! ## §4 — ★★★ Convolution of two multiplicatives is multiplicative -/

/-- ★★★ **Dirichlet convolution preserves multiplicativity**: if `f,g` are
    multiplicative on coprime pairs then so is `f∗g`:
    `gcd(a,b)=1 → 0<a → 0<b → dconv f g (a·b) = dconv f g a · dconv f g b`. -/
theorem dconv_mul (f g : Nat → Int)
    (hf : ∀ a b, gcd213 a b = 1 → f (a * b) = f a * f b)
    (hg : ∀ a b, gcd213 a b = 1 → g (a * b) = g a * g b)
    {a b : Nat} (hab : gcd213 a b = 1) (ha : 0 < a) (hb : 0 < b) :
    dconv f g (a * b) = dconv f g a * dconv f g b := by
  -- dconv f g (a·b) = divisorSumZ (a·b) (fun d => f d · g((a·b)/d))
  show divisorSumZ (a * b) (fun d => f d * g ((a * b) / d))
      = dconv f g a * dconv f g b
  rw [divisorSumZ_product_reindex a b hab ha hb (fun d => f d * g ((a * b) / d))]
  -- factor each grid cell
  have hcells : sumZ a (fun i => sumZ b (fun k =>
        (dvdInd i a : Int) * (dvdInd k b : Int)
          * (f ((i + 1) * (k + 1)) * g ((a * b) / ((i + 1) * (k + 1))))))
      = sumZ a (fun i => sumZ b (fun k =>
        ((dvdInd i a : Int) * (f (i + 1) * g (a / (i + 1))))
          * ((dvdInd k b : Int) * (f (k + 1) * g (b / (k + 1)))))) :=
    sumZ_congr a _ _ (fun i _ =>
      sumZ_congr b _ _ (fun k _ => cell_factor f g hf hg hab i k))
  rw [hcells]
  -- factor out the i-part of each inner sum
  have hfactor : sumZ a (fun i => sumZ b (fun k =>
        ((dvdInd i a : Int) * (f (i + 1) * g (a / (i + 1))))
          * ((dvdInd k b : Int) * (f (k + 1) * g (b / (k + 1))))))
      = sumZ a (fun i => ((dvdInd i a : Int) * (f (i + 1) * g (a / (i + 1))))
          * sumZ b (fun k => (dvdInd k b : Int) * (f (k + 1) * g (b / (k + 1))))) :=
    sumZ_congr a _ _ (fun i _ =>
      inner_factor ((dvdInd i a : Int) * (f (i + 1) * g (a / (i + 1)))) b
        (fun k => (dvdInd k b : Int) * (f (k + 1) * g (b / (k + 1)))))
  rw [hfactor]
  -- pull the constant b-sum out of the a-sum
  rw [sumZ_mul_right
        (sumZ b (fun k => (dvdInd k b : Int) * (f (k + 1) * g (b / (k + 1))))) a
        (fun i => (dvdInd i a : Int) * (f (i + 1) * g (a / (i + 1))))]
  -- both factors are now `dconv f g a` / `dconv f g b` once we recognise the floors.
  show (sumZ a (fun i => (dvdInd i a : Int) * (f (i + 1) * g (a / (i + 1)))))
      * (sumZ b (fun k => (dvdInd k b : Int) * (f (k + 1) * g (b / (k + 1)))))
    = dconv f g a * dconv f g b
  rfl

end E213.Lib.Math.NumberTheory.DirichletMultiplicative
