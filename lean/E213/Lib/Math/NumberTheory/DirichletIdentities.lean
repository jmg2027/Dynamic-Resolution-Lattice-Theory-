import E213.Lib.Math.NumberTheory.DirichletConvolution
import E213.Lib.Math.NumberTheory.MobiusBridge
import E213.Lib.Math.NumberTheory.GaussTotient
import E213.Lib.Math.NumberTheory.SumOfDivisors
import E213.Lib.Math.NumberTheory.GeneralizedDivisorSum

/-!
# Named Dirichlet-convolution identities (∅-axiom)

Restatement-bridges tying the session's μ/φ/σ framework to `dconv`:
  * `eps` — the Dirichlet identity element.
  * `mu_conv_one`   : `μ ∗ 1 = ε`.
  * `dconv_one_eps` / `dconv_eps_one` : `ε` is the two-sided identity.
  * `phi_conv_one`  : `φ ∗ 1 = id`.
  * `sigma_eq_id_conv_one` : `σ = id ∗ 1`.
-/

namespace E213.Lib.Math.NumberTheory.DirichletIdentities

open E213.Lib.Math.NumberTheory.DirichletConvolution (dconv dconv_one_right)
open E213.Lib.Math.NumberTheory.MobiusFunction (mu sumZ divisorSumZ mobiusSum)
open E213.Lib.Math.NumberTheory.MobiusPrimeCase (sumZ_congr)
open E213.Lib.Math.NumberTheory.EulerTotient (dvdInd totient divisorSum gaussSum)
open E213.Lib.Math.NumberTheory.GaussTotient
  (eqInd eqInd_self eqInd_ne mul_div_of_dvd gauss_totient)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum (sum_eqIndZ_weight_eq castOne_mul castZero_mul)
open E213.Lib.Math.NumberTheory.MobiusInversion (div_eq_one_iff_eq)
open E213.Meta.Nat.NatDiv213 (mul_witness_iff_mod_eq_zero)

/-! ## §1 — The Dirichlet identity element ε -/

/-- The Dirichlet identity element `ε(n) = [n = 1]` (the unit of `dconv`),
    propext-free via `Bool.toNat`. -/
def eps (n : Nat) : Int := ((n == 1).toNat : Int)

/-- `ε 1 = 1`. -/
theorem eps_one : eps 1 = 1 := rfl

/-- `n ≠ 1 → ε n = 0`. -/
theorem eps_ne_one {n : Nat} (h : n ≠ 1) : eps n = 0 := by
  show ((n == 1).toNat : Int) = 0
  rw [E213.Meta.Nat.Beq213.nat_beq_op_eq_false_of_ne h]; rfl

/-! ## §2 — `μ ∗ 1 = ε` -/

/-- ★★★ **`μ ∗ 1 = ε`**: the corpus Möbius divisor-sum, restated as a Dirichlet
    convolution.  `dconv mu (fun _=>1) n = Σ_{d∣n} μ(d) = [n=1] = ε n`. -/
theorem mu_conv_one (n : Nat) (hn : 0 < n) :
    dconv mu (fun _ => (1 : Int)) n = eps n := by
  rw [dconv_one_right mu n]
  show mobiusSum n = ((n == 1).toNat : Int)
  exact E213.Lib.Math.NumberTheory.MobiusBridge.mu_divisor_sum n hn

/-! ## §3 — ε is the two-sided identity for `dconv` -/

/-- ★★ **`f ∗ ε = f`**: ε is a right identity.  Only the divisor `d = n` survives
    (`ε(n/n) = ε 1 = 1`; `ε(n/d) = 0` otherwise). -/
theorem dconv_one_eps (f : Nat → Int) (n : Nat) (hn : 0 < n) :
    dconv f eps n = f n := by
  show sumZ n (fun j => (dvdInd j n : Int) * (f (j + 1) * eps (n / (j + 1)))) = f n
  -- survivor index is j = n - 1
  have hsurv_lt : n - 1 < n := Nat.sub_lt hn Nat.one_pos
  have hsurv1 : n - 1 + 1 = n :=
    E213.Tactic.NatHelper.sub_one_add_one (Nat.ne_of_gt hn)
  have hpt : ∀ j, j < n →
      (dvdInd j n : Int) * (f (j + 1) * eps (n / (j + 1)))
        = (eqInd (n - 1) j : Int) * f n := by
    intro j _
    cases Nat.decEq (j + 1) n with
    | isTrue hjn =>
      -- j + 1 = n: divisor d = n, eps(n/n) = 1, term = f n; survivor index
      have hdvd : (j + 1) ∣ n := ⟨1, by rw [Nat.mul_one, hjn]⟩
      have hd1 : dvdInd j n = 1 := by
        show (n % (j + 1) == 0).toNat = 1
        have hmod : n % (j + 1) = 0 := by
          obtain ⟨c, hc⟩ := hdvd
          rw [hc]; exact E213.Meta.Nat.NatDiv213.mul_mod_self_pure (j + 1) c
        rw [hmod]; rfl
      have hcof : (j + 1) * (n / (j + 1)) = n := mul_div_of_dvd hdvd
      have hnd1 : n / (j + 1) = 1 := (div_eq_one_iff_eq hn hdvd).mpr hjn
      have hjeq : n - 1 = j := by
        have : j + 1 - 1 = n - 1 := by rw [hjn]
        rw [E213.Tactic.NatHelper.add_sub_cancel_right j 1] at this
        exact this.symm
      rw [hd1, hnd1, hjeq, eqInd_self]
      show (1 : Int) * (f (j + 1) * eps 1) = (1 : Int) * f n
      rw [eps_one, hjn, E213.Meta.Int213.mul_one,
          E213.Meta.Int213.PolyIntM.one_mulZ]
    | isFalse hjn =>
      -- j + 1 ≠ n: term is zero, and survivor indicator is zero
      have hjne : n - 1 ≠ j := by
        intro he
        apply hjn
        rw [← he, hsurv1]
      rw [eqInd_ne hjne, castZero_mul]
      cases Nat.decEq (n % (j + 1)) 0 with
      | isFalse hnd0 =>
        have hd0 : dvdInd j n = 0 := by
          show (n % (j + 1) == 0).toNat = 0
          rw [E213.Meta.Nat.Beq213.nat_beq_op_eq_false_of_ne hnd0]; rfl
        rw [hd0, castZero_mul]
      | isTrue hmod =>
        have hdvd : (j + 1) ∣ n := by
          obtain ⟨x, hx⟩ := (mul_witness_iff_mod_eq_zero (j + 1) n).mpr hmod
          exact ⟨x, hx.symm⟩
        have hnd1 : n / (j + 1) ≠ 1 := fun he => hjn ((div_eq_one_iff_eq hn hdvd).mp he)
        rw [eps_ne_one hnd1, E213.Meta.Int213.PolyIntM.mul_zeroZ,
            E213.Meta.Int213.PolyIntM.mul_zeroZ]
  rw [sumZ_congr n _ _ hpt]
  exact sum_eqIndZ_weight_eq n (n - 1) (f n) hsurv_lt

/-- ★★ **`ε ∗ f = f`**: ε is a left identity (from `dconv_one_eps` via comm). -/
theorem dconv_eps_one (f : Nat → Int) (n : Nat) (hn : 0 < n) :
    dconv eps f n = f n := by
  rw [E213.Lib.Math.NumberTheory.DirichletConvolution.dirichlet_comm eps f n hn]
  exact dconv_one_eps f n hn

/-! ## §3.5 — Casting a Nat `sumTo` to the Int `sumZ` -/

/-- Push the `Int.ofNat` cast through the Nat range-sum `sumTo`:
    `(sumTo n F : Int) = sumZ n (fun j => (F j : Int))`. -/
theorem castSumTo (n : Nat) (F : Nat → Nat) :
    ((E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum.sumTo n F : Nat) : Int)
      = sumZ n (fun j => (F j : Int)) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show ((E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum.sumTo m F + F m : Nat) : Int)
        = sumZ m (fun j => (F j : Int)) + (F m : Int)
    rw [Int.ofNat_add, ih]

/-! ## §4 — `φ ∗ 1 = id` -/

/-- ★★ **`φ ∗ 1 = id`** (Gauss): `dconv (fun d => φ(d)) (fun _=>1) n = n`. -/
theorem phi_conv_one (n : Nat) (hn : 0 < n) :
    dconv (fun d => (totient d : Int)) (fun _ => (1 : Int)) n = (n : Int) := by
  rw [dconv_one_right (fun d => (totient d : Int)) n]
  -- divisorSumZ n (fun d => totient d) = (divisorSum n totient : Int) = (gaussSum n : Int)
  have hbridge : divisorSumZ n (fun d => (totient d : Int)) = (gaussSum n : Int) := by
    show sumZ n (fun j => (dvdInd j n : Int) * (totient (j + 1) : Int)) = (gaussSum n : Int)
    show sumZ n (fun j => (dvdInd j n : Int) * (totient (j + 1) : Int))
        = (divisorSum n totient : Int)
    show sumZ n (fun j => (dvdInd j n : Int) * (totient (j + 1) : Int))
        = (E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum.sumTo n
            (fun j => dvdInd j n * totient (j + 1)) : Int)
    -- push the cast through the Nat sumTo
    rw [castSumTo n (fun j => dvdInd j n * totient (j + 1))]
    exact sumZ_congr n _ _ (fun j _ => by
      rw [Int.ofNat_mul])
  rw [hbridge, gauss_totient n hn]

/-! ## §5 — `σ = id ∗ 1` -/

/-- ★ **`σ = id ∗ 1`**: `dconv (fun d => d) (fun _=>1) n = σ(n) = Σ_{d∣n} d`. -/
theorem sigma_eq_id_conv_one (n : Nat) (_hn : 0 < n) :
    dconv (fun d => (d : Int)) (fun _ => (1 : Int)) n
      = (E213.Lib.Math.NumberTheory.SumOfDivisors.sigma n : Int) := by
  rw [dconv_one_right (fun d => (d : Int)) n]
  show sumZ n (fun j => (dvdInd j n : Int) * ((j + 1 : Nat) : Int))
      = (E213.Lib.Math.NumberTheory.SumOfDivisors.sigma n : Int)
  show sumZ n (fun j => (dvdInd j n : Int) * ((j + 1 : Nat) : Int))
      = (E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum.sumTo n
          (fun j => dvdInd j n * (j + 1)) : Int)
  rw [castSumTo n (fun j => dvdInd j n * (j + 1))]
  exact sumZ_congr n _ _ (fun j _ => by
    rw [Int.ofNat_mul])


/-! ## §6 — `τ = 1 ∗ 1` -/

/-- ★ **`τ = 1 ∗ 1`**: the number-of-divisors function is the Dirichlet square of the
    constant `1`: `dconv (fun _=>1) (fun _=>1) n = τ(n) = Σ_{d∣n} 1`.  Mirrors `σ = id ∗ 1`. -/
theorem tau_eq_one_conv_one (n : Nat) (_hn : 0 < n) :
    dconv (fun _ => (1 : Int)) (fun _ => (1 : Int)) n
      = (E213.Lib.Math.NumberTheory.SumOfDivisors.tau n : Int) := by
  rw [dconv_one_right (fun _ => (1 : Int)) n]
  show sumZ n (fun j => (dvdInd j n : Int) * (1 : Int))
      = (E213.Lib.Math.NumberTheory.SumOfDivisors.tau n : Int)
  show sumZ n (fun j => (dvdInd j n : Int) * (1 : Int))
      = (E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum.sumTo n
          (fun j => dvdInd j n * 1) : Int)
  rw [castSumTo n (fun j => dvdInd j n * 1)]
  exact sumZ_congr n _ _ (fun j _ => by
    rw [Nat.mul_one]; exact E213.Meta.Int213.mul_one _)


/-! ## §7 — `φ = μ ∗ id` (the Möbius dual of `φ ∗ 1 = id`) -/

/-- ★★ **`φ = μ ∗ id`** (Gauss/Möbius dual): the Euler totient is the Dirichlet convolution
    of `μ` with the identity, `dconv μ (fun d => d) n = φ(n)`.  The Möbius inverse of the
    existing `phi_conv_one` (`φ ∗ 1 = id`), via `mobius_inversion`. -/
theorem phi_eq_mu_conv_id (n : Nat) (hn : 0 < n) :
    dconv mu (fun d => (d : Int)) n = (totient n : Int) := by
  have hg : ∀ m : Nat, 0 < m →
      ((m : Int)) = divisorSumZ m (fun d => (totient d : Int)) :=
    fun m hm => ((dconv_one_right (fun d => (totient d : Int)) m).symm.trans
      (phi_conv_one m hm)).symm
  have hinv := E213.Lib.Math.NumberTheory.MobiusInversion.mobius_inversion
    (fun d => (totient d : Int)) (fun d : Nat => (d : Int)) n hn hg
  have hinv' : (totient n : Int)
      = divisorSumZ n (fun d => E213.Lib.Math.NumberTheory.MobiusMultiplicative.muStruct d
          * ((n / d : Nat) : Int)) := hinv
  show divisorSumZ n (fun d => mu d * ((n / d : Nat) : Int)) = (totient n : Int)
  rw [hinv']
  show sumZ n (fun j => (dvdInd j n : Int) * (mu (j + 1) * ((n / (j + 1) : Nat) : Int)))
      = sumZ n (fun j => (dvdInd j n : Int)
          * (E213.Lib.Math.NumberTheory.MobiusMultiplicative.muStruct (j + 1)
              * ((n / (j + 1) : Nat) : Int)))
  exact sumZ_congr n _ _ (fun j _ => by
    rw [E213.Lib.Math.NumberTheory.MobiusBridge.muStruct_eq_mu (j + 1) (Nat.succ_pos j)])


/-! ## §8 — Dirichlet congruence helpers and the Jordan totient `J_k` -/

/-- `dconv` respects pointwise equality of the first argument (funext-free). -/
theorem dconv_congr_left (F1 F2 g : Nat → Int) (h : ∀ m, F1 m = F2 m) (n : Nat) :
    dconv F1 g n = dconv F2 g n := by
  show sumZ n (fun j => (dvdInd j n : Int) * (F1 (j + 1) * g (n / (j + 1))))
      = sumZ n (fun j => (dvdInd j n : Int) * (F2 (j + 1) * g (n / (j + 1))))
  exact sumZ_congr n _ _ (fun j _ => by rw [h (j + 1)])

/-- `dconv` respects pointwise equality of the second argument (funext-free). -/
theorem dconv_congr_right (f g1 g2 : Nat → Int) (h : ∀ m, g1 m = g2 m) (n : Nat) :
    dconv f g1 n = dconv f g2 n := by
  show sumZ n (fun j => (dvdInd j n : Int) * (f (j + 1) * g1 (n / (j + 1))))
      = sumZ n (fun j => (dvdInd j n : Int) * (f (j + 1) * g2 (n / (j + 1))))
  exact sumZ_congr n _ _ (fun j _ => by rw [h (n / (j + 1))])

/-- **Jordan totient** `J_k(n) = Σ_{d∣n} μ(d)·(n/d)^k = (μ ∗ id^k)(n)`. -/
def jordanK (k n : Nat) : Int := dconv mu (fun d => ((d ^ k : Nat) : Int)) n

/-- ★★★ **`J_k ∗ 1 = id^k`**: the Jordan totient's defining divisor-sum,
    `Σ_{d∣n} J_k(d) = n^k`.  Via the ring laws `(μ ∗ id^k) ∗ 1 = id^k ∗ (μ ∗ 1) = id^k ∗ ε
    = id^k` (commute, associate, `μ∗1=ε`, `ε` unit). -/
theorem jordan_conv_one (k n : Nat) (hn : 0 < n) :
    dconv (jordanK k) (fun _ => (1 : Int)) n = ((n ^ k : Nat) : Int) := by
  have comm_all : ∀ m, dconv mu (fun d => ((d ^ k : Nat) : Int)) m
      = dconv (fun d => ((d ^ k : Nat) : Int)) mu m := by
    intro m
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0; rfl
    · exact E213.Lib.Math.NumberTheory.DirichletConvolution.dirichlet_comm
        mu (fun d => ((d ^ k : Nat) : Int)) m hm
  have mu_one_all : ∀ m, dconv mu (fun _ => (1 : Int)) m = eps m := by
    intro m
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0; rfl
    · exact mu_conv_one m hm
  show dconv (dconv mu (fun d => ((d ^ k : Nat) : Int))) (fun _ => (1 : Int)) n
      = ((n ^ k : Nat) : Int)
  rw [dconv_congr_left (dconv mu (fun d => ((d ^ k : Nat) : Int)))
        (dconv (fun d => ((d ^ k : Nat) : Int)) mu) (fun _ => (1 : Int)) comm_all n,
      E213.Lib.Math.NumberTheory.DirichletConvolution.dirichlet_assoc
        (fun d => ((d ^ k : Nat) : Int)) mu (fun _ => (1 : Int)) n hn,
      dconv_congr_right (fun d => ((d ^ k : Nat) : Int)) (dconv mu (fun _ => (1 : Int))) eps
        mu_one_all n,
      dconv_one_eps (fun d => ((d ^ k : Nat) : Int)) n hn]

/-- ★ **`J_1 = φ`**: the Jordan totient at `k=1` is Euler's totient (via `φ = μ ∗ id`). -/
theorem jordan_one_eq_totient (n : Nat) (hn : 0 < n) :
    jordanK 1 n = (totient n : Int) := by
  show dconv mu (fun d => ((d ^ 1 : Nat) : Int)) n = (totient n : Int)
  rw [dconv_congr_right mu (fun d => ((d ^ 1 : Nat) : Int)) (fun d => (d : Int))
        (fun m => by show ((m ^ 1 : Nat) : Int) = (m : Int); rw [Nat.pow_one]) n]
  exact phi_eq_mu_conv_id n hn


/-! ## §9 — `σ_k = id^k ∗ 1` (the divisor-power sum in the Dirichlet ring) -/

/-- ★ **`σ_k = id^k ∗ 1`**: the `k`-th divisor-power sum is `id^k` convolved with `1`:
    `dconv (fun d => d^k) (fun _=>1) n = σ_k(n) = Σ_{d∣n} d^k`.  Links the existing `sigmaK`
    to the Dirichlet ring; the Möbius dual of the Jordan totient (`J_k = μ ∗ id^k`,
    `σ_k = id^k ∗ 1`).  Generalizes `σ = id ∗ 1` (`k=1`) and `τ = 1 ∗ 1` (`k=0`). -/
theorem sigmaK_eq_idk_conv_one (k n : Nat) (_hn : 0 < n) :
    dconv (fun d => ((d ^ k : Nat) : Int)) (fun _ => (1 : Int)) n
      = (E213.Lib.Math.NumberTheory.GeneralizedDivisorSum.sigmaK k n : Int) := by
  rw [dconv_one_right (fun d => ((d ^ k : Nat) : Int)) n]
  show sumZ n (fun j => (dvdInd j n : Int) * (((j + 1) ^ k : Nat) : Int))
      = (E213.Lib.Math.NumberTheory.GeneralizedDivisorSum.sigmaK k n : Int)
  show sumZ n (fun j => (dvdInd j n : Int) * (((j + 1) ^ k : Nat) : Int))
      = (E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum.sumTo n
          (fun j => dvdInd j n * (j + 1) ^ k) : Int)
  rw [castSumTo n (fun j => dvdInd j n * (j + 1) ^ k)]
  exact sumZ_congr n _ _ (fun j _ => by rw [Int.ofNat_mul])


/-- ★ **`J_0 = ε`**: the Jordan totient at `k=0` is the Dirichlet unit (`id^0 = 1`, and
    `μ ∗ 1 = ε`).  The base of the Jordan family, complementing `σ_0 = τ`. -/
theorem jordan_zero_eq_eps (n : Nat) (hn : 0 < n) : jordanK 0 n = eps n := by
  show dconv mu (fun d => ((d ^ 0 : Nat) : Int)) n = eps n
  rw [dconv_congr_right mu (fun d => ((d ^ 0 : Nat) : Int)) (fun _ => ((1 : Nat) : Int))
        (fun m => by show ((m ^ 0 : Nat) : Int) = ((1 : Nat) : Int); rw [Nat.pow_zero]) n]
  exact mu_conv_one n hn

end E213.Lib.Math.NumberTheory.DirichletIdentities
