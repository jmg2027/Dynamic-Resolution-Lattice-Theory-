import E213.Lib.Math.NumberTheory.MobiusFunction
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Meta.Nat.Beq213
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Core

/-!
# Möbius function on primes — structural evaluation + `muAux` toolkit (∅-axiom)

General (all-prime, not table) structural evaluations of the corpus trial-division
`mu` (`MobiusFunction.lean`), plus a reusable `muAux` branch toolkit:

  * ★★ `mu_prime`       — `Prime213 p → mu p = −1`        (every prime).
  * ★★ `mu_prime_sq`    — `Prime213 p → mu (p·p) = 0`     (every prime).
  * ★★ `mobiusSum_prime`— `Prime213 p → mobiusSum p = 0`  (every prime) —
        i.e. `Σ_{d∣p} μ(d) = 0`, the **n = prime case** of the general Möbius
        divisor-sum identity.
  * `muAux_{succ,zero,at_one,sq,strip,advance}` — branch equations; ★ `muAux_skip`
    scans past a whole run of non-divisors (consumes `gap` fuel, `d → d+gap`).
  * `sumZ_{succ,congr,const_zero,split_first}` — an Int divisor-sum toolkit.

These establish the corpus `mu`'s scan is correctly evaluated structurally in the
closable cases.  The **general** theorem `∀ n ≥ 1, Σ_{d∣n} μ(d) = [n=1]` remains
open — it needs a `muAux`-correctness invariant (scan interleaving / scan-start
independence) bridging trial-division `mu` to a structural `vp`/`Prime213`
valuation.  (Full obstruction analysis since closed in the Möbius-framework
programme.)
-/

namespace E213.Lib.Math.NumberTheory.MobiusPrimeCase

open E213.Lib.Math.NumberTheory.MobiusFunction (mu muAux sumZ divisorSumZ mobiusSum)
open E213.Meta.Nat.Beq213 (nat_beq_op_eq_false_of_ne)

/-! ## `muAux` branch equations -/

/-- The defining equation of `muAux` at `fuel+1`, exposed (`rfl`). -/
theorem muAux_succ (fuel m d : Nat) (sign : Int) :
    muAux (fuel + 1) m d sign =
      cond (m == 1) sign
        (cond (m % d == 0)
          (cond ((m / d) % d == 0) 0 (muAux fuel (m / d) (d + 1) (- sign)))
          (muAux fuel m (d + 1) sign)) := rfl

theorem muAux_zero (m d : Nat) (sign : Int) : muAux 0 m d sign = sign := rfl

/-- `m = 1` ⇒ return sign. -/
theorem muAux_at_one (fuel d : Nat) (sign : Int) : muAux (fuel + 1) 1 d sign = sign := by
  rw [muAux_succ]; show cond (1 == 1) sign _ = sign
  rw [show ((1:Nat) == 1) = true from rfl]; rfl

/-- Branch: `m ≠ 1`, `d ∣ m`, `d² ∣ m` ⇒ return 0. -/
theorem muAux_sq (fuel m d : Nat) (sign : Int)
    (h1 : ¬ m = 1) (h2 : m % d = 0) (h3 : (m / d) % d = 0) :
    muAux (fuel + 1) m d sign = 0 := by
  rw [muAux_succ]
  rw [nat_beq_op_eq_false_of_ne h1]
  show cond (m % d == 0) _ _ = 0
  rw [show (m % d == 0) = true from by rw [h2]; rfl]
  show cond ((m / d) % d == 0) 0 _ = 0
  rw [show ((m / d) % d == 0) = true from by rw [h3]; rfl]; rfl

/-- Branch: `m ≠ 1`, `d ∣ m`, `d² ∤ m` ⇒ strip `d`, flip sign, recurse. -/
theorem muAux_strip (fuel m d : Nat) (sign : Int)
    (h1 : ¬ m = 1) (h2 : m % d = 0) (h3 : ¬ (m / d) % d = 0) :
    muAux (fuel + 1) m d sign = muAux fuel (m / d) (d + 1) (- sign) := by
  rw [muAux_succ, nat_beq_op_eq_false_of_ne h1]
  show cond (m % d == 0) _ _ = _
  rw [show (m % d == 0) = true from by rw [h2]; rfl]
  show cond ((m / d) % d == 0) 0 _ = _
  rw [nat_beq_op_eq_false_of_ne h3]; rfl

/-- Branch: `m ≠ 1`, `d ∤ m` ⇒ advance `d`. -/
theorem muAux_advance (fuel m d : Nat) (sign : Int)
    (h1 : ¬ m = 1) (h2 : ¬ m % d = 0) :
    muAux (fuel + 1) m d sign = muAux fuel m (d + 1) sign := by
  rw [muAux_succ, nat_beq_op_eq_false_of_ne h1]
  show cond (m % d == 0) _ _ = _
  rw [nat_beq_op_eq_false_of_ne h2]; rfl

/-- ★ **Scan-advance over a gap**: if `m ≠ 1` and `m % (d+j) ≠ 0` for all `j < gap`,
    then `gap` units of fuel are consumed advancing `d → d+gap`. -/
theorem muAux_skip (m : Nat) (sign : Int) (h1 : ¬ m = 1) :
    ∀ (gap rest d : Nat),
      (∀ j, j < gap → ¬ m % (d + j) = 0) →
      muAux (gap + rest) m d sign = muAux rest m (d + gap) sign
  | 0, rest, d, _ => by rw [Nat.zero_add, Nat.add_zero]
  | gap + 1, rest, d, hnd => by
    have h0 : ¬ m % d = 0 := by
      have := hnd 0 (Nat.succ_pos gap); rwa [Nat.add_zero] at this
    rw [show gap + 1 + rest = (gap + rest) + 1 from by
      rw [Nat.add_right_comm gap 1 rest]]
    rw [muAux_advance (gap + rest) m d sign h1 h0]
    have hnd' : ∀ j, j < gap → ¬ m % ((d + 1) + j) = 0 := by
      intro j hj
      have := hnd (j + 1) (Nat.succ_lt_succ hj)
      rwa [show d + (j + 1) = (d + 1) + j from by
        rw [Nat.add_assoc, Nat.add_comm 1 j, ← Nat.add_assoc]] at this
    rw [muAux_skip m sign h1 gap rest (d + 1) hnd']
    have he : (d + 1) + gap = d + (gap + 1) := by
      rw [Nat.add_assoc d 1 gap, Nat.add_comm 1 gap]
    rw [he]

/-! ## `mu` of a general prime is `−1` -/

open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero mod_self)

/-- For a prime `p` and `2 ≤ j < p`, `p % j ≠ 0` (a proper divisor would be `1` or `p`). -/
theorem prime_not_mod_zero {p j : Nat} (hp : Prime213 p) (hj2 : 2 ≤ j) (hjp : j < p) :
    ¬ p % j = 0 := by
  intro hmod
  have hjd : j ∣ p := dvd_of_mod_eq_zero hmod
  rcases hp.2 j hjd with h1 | hpe
  · exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hj2))
  · exact absurd hpe (Nat.ne_of_lt hjp)

/-- `p / p = 1` for `0 < p`. -/
theorem div_self_pos {p : Nat} (hp : 0 < p) : p / p = 1 := by
  have : 1 * p / p = 1 := E213.Meta.Nat.NatDiv213.mul_div_self_pure 1 p hp
  rwa [Nat.one_mul] at this

/-- `1 % p = 1` for `2 ≤ p`, hence `≠ 0`. -/
theorem one_mod_ne_zero {p : Nat} (hp : 2 ≤ p) : ¬ (1 : Nat) % p = 0 := by
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide) hp)]; exact (by decide)

/-- ★★ **`mu` of a general prime is `−1`** (structural, all primes, not a table).
    The scan from `d=2` advances past every `j ∈ [2,p)` (none divides `p`), finds
    `p`, sees `p² ∤ p` (cofactor `1`), strips and flips to `−1`, then `m=1` returns. -/
theorem mu_prime {p : Nat} (hp : Prime213 p) : mu p = -1 := by
  have hp2 : 2 ≤ p := hp.1
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := match p, hp2 with
    | k + 2, _ => ⟨k, rfl⟩
  show muAux (n + 2) (n + 2) 2 1 = -1
  have hskip : muAux (n + 2) (n + 2) 2 1 = muAux 2 (n + 2) (2 + n) 1 := by
    have hne : ¬ (n + 2) = 1 := fun h => Nat.noConfusion (Nat.succ.inj h)
    have hnd : ∀ j, j < n → ¬ (n + 2) % (2 + j) = 0 := by
      intro j hj
      refine prime_not_mod_zero hp (Nat.le_add_right 2 j) ?_
      rw [Nat.add_comm 2 j]
      exact Nat.add_lt_add_right hj 2
    calc muAux (n + 2) (n + 2) 2 1
        = muAux (n + 2) (n + 2) 2 1 := rfl
      _ = muAux 2 (n + 2) (2 + n) 1 := by
          have := muAux_skip (n + 2) 1 hne n 2 2 hnd
          rwa [show n + 2 = n + 2 from rfl] at this
  rw [hskip]
  have hpeq : (2 + n) = n + 2 := Nat.add_comm 2 n
  rw [hpeq]
  have hne : ¬ (n + 2) = 1 := fun h => Nat.noConfusion (Nat.succ.inj h)
  have hmod : (n + 2) % (n + 2) = 0 := mod_self (n + 2)
  have hdiv : (n + 2) / (n + 2) = 1 := div_self_pos (Nat.succ_pos (n + 1))
  have hcof : ¬ ((n + 2) / (n + 2)) % (n + 2) = 0 := by
    rw [hdiv]; exact one_mod_ne_zero hp2
  rw [show (2 : Nat) = 1 + 1 from rfl, muAux_strip 1 (n + 2) (n + 2) 1 hne hmod hcof]
  rw [hdiv]
  show muAux (0 + 1) 1 (n + 2 + 1) (-1) = -1
  rw [muAux_at_one]

/-! ## A minimal `sumZ` toolkit + `mobiusSum p = 0` for general primes -/

open E213.Lib.Math.NumberTheory.MobiusFunction (sumZ divisorSumZ)
open E213.Lib.Math.NumberTheory.EulerTotient (dvdInd)
open E213.Meta.Int213 (zero_mul zero_add add_neg_cancel)

theorem sumZ_succ (n : Nat) (f : Nat → Int) : sumZ (n + 1) f = sumZ n f + f n := rfl

/-- Congruence for `sumZ` on `[0,n)`. -/
theorem sumZ_congr (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k = g k) :
    sumZ n f = sumZ n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
        h m (Nat.lt_succ_self m)]

/-- If every term vanishes, `sumZ` is `0`. -/
theorem sumZ_const_zero (n : Nat) : sumZ n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [sumZ_succ, ih]; rfl

/-- Split the first term: `sumZ (n+1) f = f 0 + sumZ n (fun j => f (j+1))`. -/
theorem sumZ_split_first (n : Nat) (f : Nat → Int) :
    sumZ (n + 1) f = f 0 + sumZ n (fun j => f (j + 1)) := by
  induction n with
  | zero =>
    show sumZ 0 f + f 0 = f 0 + sumZ 0 (fun j => f (j + 1))
    show (0 : Int) + f 0 = f 0 + 0
    ring_intZ
  | succ m ih =>
    rw [sumZ_succ (m + 1) f, ih]
    show f 0 + sumZ m (fun j => f (j + 1)) + f (m + 1)
       = f 0 + (sumZ m (fun j => f (j + 1)) + f (m + 1))
    ring_intZ

/-- `n % (j+1) ≠ 0 → dvdInd j n = 0`. -/
theorem dvdInd_zero_of_not_mod {j n : Nat} (h : ¬ n % (j + 1) = 0) : dvdInd j n = 0 := by
  show (n % (j + 1) == 0).toNat = 0
  rw [nat_beq_op_eq_false_of_ne h]; rfl

/-- ★★ **`mobiusSum p = 0` for every prime `p`** (general, not a table).
    The only divisors of `p` are `1` and `p`; their `mu`-values `1` and `−1`
    cancel, and every intermediate divisor index contributes `0`. -/
theorem mobiusSum_prime {p : Nat} (hp : Prime213 p) :
    mobiusSum p = 0 := by
  have hp2 : 2 ≤ p := hp.1
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := match p, hp2 with
    | k + 2, _ => ⟨k, rfl⟩
  show sumZ (n + 2) (fun j => (dvdInd j (n + 2) : Int) * mu (j + 1)) = 0
  rw [sumZ_succ (n + 1) (fun j => (dvdInd j (n + 2) : Int) * mu (j + 1))]
  have hlast : ((dvdInd (n + 1) (n + 2) : Int) * mu (n + 1 + 1)) = -1 := by
    have hdv : dvdInd (n + 1) (n + 2) = 1 := by
      show ((n + 2) % (n + 2) == 0).toNat = 1
      rw [show (n + 2) % (n + 2) = 0 from mod_self (n + 2)]; rfl
    rw [hdv]
    show (1 : Int) * mu (n + 2) = -1
    rw [mu_prime hp]; ring_intZ
  rw [hlast]
  rw [sumZ_split_first n (fun j => (dvdInd j (n + 2) : Int) * mu (j + 1))]
  have hhead : ((dvdInd 0 (n + 2) : Int) * mu (0 + 1)) = 1 := by
    have hd0 : dvdInd 0 (n + 2) = 1 := by
      show ((n + 2) % 1 == 0).toNat = 1
      rw [show (n + 2) % 1 = 0 from Nat.mod_one (n + 2)]; rfl
    rw [hd0]; show (1 : Int) * mu 1 = 1; rw [show mu 1 = 1 from rfl]; ring_intZ
  rw [hhead]
  have hmid : sumZ n (fun j => (dvdInd (j + 1) (n + 2) : Int) * mu (j + 1 + 1))
            = sumZ n (fun _ => (0 : Int)) := by
    refine sumZ_congr n _ _ (fun j hj => ?_)
    have hnd : ¬ (n + 2) % (j + 2) = 0 :=
      prime_not_mod_zero hp (Nat.le_add_left 2 j)
        (Nat.succ_lt_succ (Nat.succ_lt_succ hj))
    have hdz : dvdInd (j + 1) (n + 2) = 0 := dvdInd_zero_of_not_mod hnd
    show (dvdInd (j + 1) (n + 2) : Int) * mu (j + 1 + 1) = 0
    rw [hdz]; show (0 : Int) * mu (j + 1 + 1) = 0
    exact zero_mul (mu (j + 1 + 1))
  rw [hmid, sumZ_const_zero]
  show (0 : Int) + (1 + 0) + (-1) = 0
  show (0 : Int) + 1 + (-1) = 0
  rw [zero_add (1 : Int)]
  exact add_neg_cancel (1 : Int)

/-! ## `mu (p²) = 0` for general primes (the squared-factor branch) -/

open E213.Meta.Nat.Gcd213 (coprime_dvd_of_dvd_mul gcd213_dvd_left gcd213_dvd_right)
open E213.Tactic.NatHelper (gcd213)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Meta.Nat.NatDiv213 (mul_mod_self_pure mul_div_cancel_left_pure)

/-- A divisor `j` of `p²` with `2 ≤ j < p` is impossible (divisors of `p²` are
    `1, p, p²`). -/
theorem prime_sq_not_mod_zero {p j : Nat} (hp : Prime213 p) (hj2 : 2 ≤ j) (hjp : j < p) :
    ¬ (p * p) % j = 0 := by
  intro hmod
  have hjpp : j ∣ (p * p) := dvd_of_mod_eq_zero hmod
  cases hjp_mod : Nat.decEq (j % p) 0 with
  | isTrue hpj0 =>
    have hpj : p ∣ j := dvd_of_mod_eq_zero hpj0
    exact absurd (le_of_dvd_pos p j (Nat.lt_of_lt_of_le (by decide) hj2) hpj)
      (Nat.not_le.mpr hjp)
  | isFalse hpj0 =>
    have hpj : ¬ p ∣ j := fun hd =>
      hpj0 (E213.Meta.Nat.Valuation.mod_zero_of_dvd
        (Nat.lt_of_lt_of_le (by decide) hp.1) hd)
    have hcop : gcd213 j p = 1 := by
      rcases hp.2 (gcd213 j p) (gcd213_dvd_right j p) with h1 | hpe
      · exact h1
      · exact absurd (hpe ▸ gcd213_dvd_left j p) hpj
    have hjp_dvd : j ∣ p := coprime_dvd_of_dvd_mul hcop hjpp
    rcases hp.2 j hjp_dvd with h1 | hpe
    · exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hj2))
    · exact absurd hpe (Nat.ne_of_lt hjp)

/-- ★★ **`mu (p²) = 0` for every prime `p`** (general, not a table).
    The scan reaches the smallest factor `p` (nothing in `[2,p)` divides `p²`),
    sees `p ∣ (p²/p) = p` (squared factor), and returns `0`. -/
theorem mu_prime_sq {p : Nat} (hp : Prime213 p) : mu (p * p) = 0 := by
  have hp2 : 2 ≤ p := hp.1
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  obtain ⟨n, hn⟩ : ∃ n, p = n + 2 := match p, hp2 with
    | k + 2, _ => ⟨k, rfl⟩
  have hpp2 : 2 ≤ p * p := Nat.le_trans hp2 (Nat.le_mul_of_pos_left p hp0)
  obtain ⟨M, hM⟩ : ∃ M, p * p = M + 2 := match p * p, hpp2 with
    | k + 2, _ => ⟨k, rfl⟩
  have hmu : mu (p * p) = muAux (M + 2) (M + 2) 2 1 := by
    rw [hM]; rfl
  rw [hmu]
  have hne : ¬ (M + 2) = 1 := fun h => Nat.noConfusion (Nat.succ.inj h)
  have hn2_le : n + 2 ≤ M + 2 := by
    have h1 : p ≤ p * p := Nat.le_mul_of_pos_left p hp0
    rw [hM] at h1; rw [hn] at h1; exact h1
  have hnle : n ≤ M + 2 :=
    Nat.le_trans (Nat.le_succ_of_le (Nat.le_succ n)) hn2_le
  have hnd : ∀ j, j < n → ¬ (M + 2) % (2 + j) = 0 := by
    intro j hj
    rw [← hM]
    refine prime_sq_not_mod_zero hp (Nat.le_add_right 2 j) ?_
    rw [hn, Nat.add_comm 2 j]
    exact Nat.add_lt_add_right hj 2
  have hsplit : muAux (M + 2) (M + 2) 2 1
              = muAux ((M + 2) - n) (M + 2) (2 + n) 1 := by
    have hfuel : n + ((M + 2) - n) = M + 2 := E213.Tactic.NatHelper.add_sub_of_le hnle
    calc muAux (M + 2) (M + 2) 2 1
        = muAux (n + ((M + 2) - n)) (M + 2) 2 1 := by rw [hfuel]
      _ = muAux ((M + 2) - n) (M + 2) (2 + n) 1 :=
          muAux_skip (M + 2) 1 hne n ((M + 2) - n) 2 hnd
  rw [hsplit]
  have hdp : (2 + n) = p := by rw [hn, Nat.add_comm 2 n]
  rw [hdp]
  obtain ⟨r, hr⟩ : ∃ r, (M + 2) - n = r + 1 := by
    have hfuel : n + ((M + 2) - n) = M + 2 := E213.Tactic.NatHelper.add_sub_of_le hnle
    have hn1 : n + 1 ≤ n + ((M + 2) - n) := by
      rw [hfuel]
      exact Nat.le_trans (Nat.succ_le_succ (Nat.le_succ n)) hn2_le
    have hpos : 1 ≤ (M + 2) - n := E213.Tactic.NatHelper.le_of_add_le_add_left hn1
    exact match (M + 2) - n, hpos with | k + 1, _ => ⟨k, rfl⟩
  rw [hr]
  have hmod1 : (M + 2) % p = 0 := by rw [← hM]; exact mul_mod_self_pure p p
  have hdiv1 : (M + 2) / p = p := by rw [← hM]; exact mul_div_cancel_left_pure p p hp0
  have hmod2 : ((M + 2) / p) % p = 0 := by rw [hdiv1]; exact mod_self p
  exact muAux_sq r (M + 2) p 1 hne hmod1 hmod2

end E213.Lib.Math.NumberTheory.MobiusPrimeCase
