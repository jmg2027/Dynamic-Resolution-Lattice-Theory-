import E213.Lib.Math.NumberTheory.MobiusMultiplicative
import E213.Lib.Math.NumberTheory.MobiusPrimeCase
import E213.Lib.Math.NumberTheory.MobiusDivisorSum
import E213.Lib.Math.NumberTheory.MobiusFunction
import E213.Lib.Math.NumberTheory.MobiusInversion
import E213.Meta.Nat.VpSeparation
import E213.Meta.Nat.VpMul
import E213.Meta.Nat.Valuation
import E213.Lib.Math.NumberTheory.PrimeValuation

/-!
# The `muStruct = mu` bridge + corpus-`mu` Möbius framework (∅-axiom)

★★★ `muStruct_eq_mu : ∀ n, 0 < n → muStruct n = mu n` — the corpus trial-division
`mu` agrees with the structural `muStruct` everywhere.  Closes the last item of the Möbius-framework programme, transporting the WHOLE
Möbius framework from `muStruct` to the corpus `mu`.

The scan-correctness obstruction (muAux strips the smallest prime and recurses from
`d+1`; `muStruct` reads valuations independently) is cracked by the reusable
★★★ `muAux_eq_prodFrom` invariant: tying the window length to the fuel
(`m < d + fuel`, `NSF d m` = no prime factor `< d`) lets a single induction on `fuel`
handle all three muAux branches uniformly (advance / strip / square), with
`prodFrom_strip_eq` realigning the stripped `m/d`-window to the `m`-window.
Specializing `d=2, fuel=m` collapses to `mu m = prodFrom 2 m m = muStruct m`.

Corpus-`mu` corollaries (the framework, now on the actual `mu`):
  * ★★★ `mu_divisor_sum` — `∀n>0, Σ_{d∣n} mu d = [n=1]` (general — generalizes the
    iter-103 `decide` table n=1..24 to ALL n).
  * ★★★ `mu_mul` — `gcd(a,b)=1 → mu(a·b) = mu a · mu b` (multiplicative).
  * `mu_prime_pow` — `mu(pⁱ) = mFactor i`.
  * ★★★ `mu_mobius_inversion` — `f n = Σ_{d∣n} mu d · Σ_{e∣(n/d)} f e`.
All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.MobiusBridge

open E213.Lib.Math.NumberTheory.MobiusFunction (mu muAux)
open E213.Lib.Math.NumberTheory.MobiusMultiplicative
  (muStruct mFactor guarded prodFrom prodFrom_zero prodFrom_succ
   guarded_prime guarded_nonprime primB prime_of_primB guarded_one_of_gt
   mFactor_zero mFactor_one mFactor_succ_succ prodFrom2_stable muStruct_mul muStruct_one)
open E213.Lib.Math.NumberTheory.MobiusPrimeCase
  (muAux_succ muAux_zero muAux_at_one muAux_sq muAux_strip muAux_advance muAux_skip)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.Valuation (vp mod_zero_of_dvd)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Meta.Nat.VpSeparation (exists_prime_factor)
open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd dvd_iff_one_le_vp vp_div_prime vp_div_prime_other)

/-! ## muStruct strip recurrence (T2) -/

/-- `muStruct p^k * m = mFactor k * muStruct m` for prime `p`, `gcd(p^k,m)=1`. -/
theorem muStruct_strip {p k m : Nat} (hp : Prime213 p)
    (hm : 0 < m) (hcop : E213.Tactic.NatHelper.gcd213 (p ^ k) m = 1) :
    muStruct (p ^ k * m) = mFactor k * muStruct m := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hpk : 0 < p ^ k := Nat.pos_pow_of_pos k hp0
  rw [muStruct_mul hpk hm hcop,
      E213.Lib.Math.NumberTheory.MobiusDivisorSum.muStruct_prime_pow hp k]

/-! ## prodFrom head-peel + window lemmas (for the muAux scan invariant) -/

/-- Peel the *first* candidate off a `prodFrom` window:
    `prodFrom d m (len+1) = guarded d m * prodFrom (d+1) m len`.
    (`prodFrom` is defined peeling from the tail; this is the head version.) -/
theorem prodFrom_head (d m : Nat) :
    ∀ len, prodFrom d m (len + 1) = guarded d m * prodFrom (d + 1) m len
  | 0 => by
    show prodFrom d m 1 = guarded d m * prodFrom (d + 1) m 0
    rw [show prodFrom d m 1 = prodFrom d m 0 * guarded (d + 0) m from prodFrom_succ d m 0]
    rw [prodFrom_zero, Nat.add_zero, E213.Meta.Int213.PolyIntM.one_mulZ]
    rw [show prodFrom (d + 1) m 0 = 1 from prodFrom_zero (d + 1) m,
        E213.Meta.Int213.mul_one]
  | len + 1 => by
    rw [show prodFrom d m (len + 1 + 1) = prodFrom d m (len + 1) * guarded (d + (len + 1)) m
          from prodFrom_succ d m (len + 1)]
    rw [prodFrom_head d m len]
    rw [show prodFrom (d + 1) m (len + 1) = prodFrom (d + 1) m len * guarded ((d + 1) + len) m
          from prodFrom_succ (d + 1) m len]
    have he : d + (len + 1) = (d + 1) + len := by
      rw [Nat.add_assoc, Nat.add_comm 1 len, ← Nat.add_assoc]
    rw [he]
    generalize guarded d m = G
    generalize prodFrom (d + 1) m len = P
    generalize guarded ((d + 1) + len) m = H
    rw [E213.Meta.Int213.mul_assoc G P H]

/-- A window all of whose candidates contribute `guarded = 1` has product `1`. -/
theorem prodFrom_window_one (d m : Nat) :
    ∀ len, (∀ j, j < len → guarded (d + j) m = 1) → prodFrom d m len = 1
  | 0, _ => prodFrom_zero d m
  | len + 1, hone => by
    rw [prodFrom_succ, hone len (Nat.lt_succ_self len), E213.Meta.Int213.mul_one]
    exact prodFrom_window_one d m len (fun j hj => hone j (Nat.lt_succ_of_lt hj))

/-! ## strip invariance: `guarded q m = guarded q (m/d)` for `q ≠ d` -/

/-- Stripping a prime `d ∣ m` leaves the guarded factor at any candidate `q ≠ d`
    unchanged: `guarded q m = guarded q (m / d)`. -/
theorem guarded_strip_eq {d q m : Nat} (hd : Prime213 d) (hm : 0 < m) (hdm : d ∣ m)
    (hqd : q ≠ d) : guarded q m = guarded q (m / d) := by
  cases hqB : primB q with
  | false => rw [guarded_nonprime hqB, guarded_nonprime hqB]
  | true =>
    have hqpr : Prime213 q := prime_of_primB hqB
    rw [guarded_prime hqB, guarded_prime hqB,
        vp_div_prime_other (E213.Lib.Math.NumberTheory.MobiusMultiplicative.isPrime_of_prime hd)
          (E213.Lib.Math.NumberTheory.MobiusMultiplicative.isPrime_of_prime hqpr) hqd hm hdm]

/-- The whole window from `d+1` is strip-invariant: every candidate exceeds `d`,
    hence `≠ d`, so `prodFrom (d+1) m len = prodFrom (d+1) (m/d) len`. -/
theorem prodFrom_strip_eq {d m : Nat} (hd : Prime213 d) (hm : 0 < m) (hdm : d ∣ m) :
    ∀ len, prodFrom (d + 1) m len = prodFrom (d + 1) (m / d) len
  | 0 => by rw [prodFrom_zero, prodFrom_zero]
  | len + 1 => by
    rw [prodFrom_succ, prodFrom_succ, prodFrom_strip_eq hd hm hdm len]
    have hqd : (d + 1) + len ≠ d := by
      have heq : (d + 1) + len = d + (len + 1) := by
        rw [Nat.add_assoc d 1 len, Nat.add_comm 1 len]
      rw [heq]
      intro he
      have h2 : d + (len + 1) = d + 0 := by rw [Nat.add_zero]; exact he
      exact Nat.noConfusion (E213.Tactic.NatHelper.add_left_cancel h2)
    rw [guarded_strip_eq hd hm hdm hqd]

/-! ## guarded / mFactor value bridges for the scan -/

/-- A candidate `q` not dividing `m > 0` contributes `guarded q m = 1`
    (prime ⇒ `vp = 0 ⇒ mFactor 0 = 1`; composite ⇒ `guarded = 1` definitionally). -/
theorem guarded_one_of_not_dvd {q m : Nat} (hm : 0 < m) (hnd : ¬ q ∣ m) :
    guarded q m = 1 := by
  cases hqB : primB q with
  | false => exact guarded_nonprime hqB
  | true =>
    have hqpr : Prime213 q := prime_of_primB hqB
    rw [guarded_prime hqB,
        vp_eq_zero_of_not_dvd
          (E213.Lib.Math.NumberTheory.MobiusMultiplicative.isPrime_of_prime hqpr) hm hnd,
        mFactor_zero]

/-- `mFactor k = 0` when `2 ≤ k`. -/
theorem mFactor_two_le_zero {k : Nat} (hk : 2 ≤ k) : mFactor k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := match k, hk with
    | j + 2, _ => ⟨j, rfl⟩
  exact mFactor_succ_succ j

/-- No-small-factor predicate: no prime `< d` divides `m`. -/
def NSF (d m : Nat) : Prop := ∀ q, Prime213 q → q < d → ¬ q ∣ m

/-- Under NSF, a candidate `d ∣ m` (with `m > 0`, `2 ≤ d`) must be prime:
    a composite `d` would have a prime factor `< d` dividing `m`. -/
theorem prime_of_nsf_dvd {d m : Nat} (h2 : 2 ≤ d) (hdm : d ∣ m) (hnsf : NSF d m) :
    Prime213 d := by
  obtain ⟨r, hr, hrd⟩ := exists_prime_factor d d (Nat.le_refl d) h2
  have hrpr : Prime213 r := hr
  have hr_le : r ≤ d := E213.Tactic.Pow213.le_of_dvd_pos r d (Nat.lt_of_lt_of_le (by decide) h2) hrd
  cases Nat.lt_or_ge r d with
  | inl hrlt =>
    exact absurd (E213.Meta.Nat.Valuation.dtrans hrd hdm) (hnsf r hrpr hrlt)
  | inr hge =>
    have hre : r = d := Nat.le_antisymm hr_le hge
    rw [hre] at hrpr; exact hrpr

/-- `q ∣ 1 → q = 1`. -/
theorem eq_one_of_dvd_one {q : Nat} (h : q ∣ 1) : q = 1 :=
  Nat.le_antisymm (E213.Tactic.Pow213.le_of_dvd_pos q 1 (by decide) h)
    (match q, h with
      | 0, ⟨c, hc⟩ => absurd hc (by rw [Nat.zero_mul]; exact (by decide))
      | _ + 1, _ => Nat.succ_le_succ (Nat.zero_le _))

/-- `prodFrom d 1 len = 1` for `2 ≤ d` (no candidate `≥ d` divides `1`). -/
theorem prodFrom_one_eq_one {d : Nat} (h2 : 2 ≤ d) (len : Nat) :
    prodFrom d 1 len = 1 := by
  refine prodFrom_window_one d 1 len (fun j _ => ?_)
  refine guarded_one_of_not_dvd (by decide) (fun hd => ?_)
  have : d + j = 1 := eq_one_of_dvd_one hd
  have hdle : d ≤ 1 := Nat.le_trans (Nat.le_add_right d j) (Nat.le_of_eq this)
  exact absurd (Nat.le_trans h2 hdle) (by decide)

/-! ## ★★★ The scan-tail-product invariant (T2.5 core) -/

open E213.Meta.Int213 (mul_assoc mul_neg neg_mul mul_one)
open E213.Meta.Int213.PolyIntM (one_mulZ)

/-- ★★★ **Scan-tail-product invariant**: with sufficient fuel/window
    (`m < d + fuel`), `2 ≤ d`, `0 < m`, and `m` having no prime factor `< d`
    (`NSF d m`), the corpus `muAux` scan computes exactly the signed structural
    tail product:
    `muAux fuel m d sign = sign * prodFrom d m fuel`. -/
theorem muAux_eq_prodFrom :
    ∀ (fuel m d : Nat) (sign : Int),
      0 < m → 2 ≤ d → NSF d m → m < d + fuel →
      muAux fuel m d sign = sign * prodFrom d m fuel
  | 0, m, d, sign, hm, h2, hnsf, hlt => by
    -- m < d + 0 = d, NSF ⇒ m = 1
    rw [Nat.add_zero] at hlt
    have hm1 : m = 1 := by
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · exact Nat.le_antisymm (Nat.le_of_lt_succ hm2) hm
      · exfalso
        obtain ⟨p, hp, hpm⟩ := exists_prime_factor m m (Nat.le_refl m) hm2
        have hple : p ≤ m := E213.Tactic.Pow213.le_of_dvd_pos p m hm hpm
        exact hnsf p hp (Nat.lt_of_le_of_lt hple hlt) hpm
    subst hm1
    rw [muAux_zero, prodFrom_zero, mul_one]
  | fuel + 1, m, d, sign, hm, h2, hnsf, hlt => by
    cases Nat.decEq m 1 with
    | isTrue hm1 =>
      subst hm1
      rw [muAux_at_one, prodFrom_one_eq_one h2 (fuel + 1), mul_one]
    | isFalse hm1 =>
      -- m ≥ 2
      cases hdvd : Nat.decEq (m % d) 0 with
      | isFalse hnd0 =>
        -- d ∤ m : advance
        have hnd : ¬ d ∣ m := fun hd =>
          hnd0 (mod_zero_of_dvd (Nat.lt_of_lt_of_le (by decide) h2) hd)
        rw [muAux_advance fuel m d sign hm1 hnd0]
        have hnsf' : NSF (d + 1) m := by
          intro q hq hqd hqm
          rcases Nat.lt_or_ge q d with hqlt | hqge
          · exact hnsf q hq hqlt hqm
          · have hqe : q = d := Nat.le_antisymm (Nat.le_of_lt_succ hqd) hqge
            rw [hqe] at hqm; exact hnd hqm
        have hlt' : m < (d + 1) + fuel := by
          have : d + (fuel + 1) = (d + 1) + fuel := by
            rw [Nat.add_assoc, Nat.add_comm 1 fuel, ← Nat.add_assoc]
          rwa [← this]
        rw [muAux_eq_prodFrom fuel m (d + 1) sign hm h2.step hnsf' hlt']
        rw [prodFrom_head d m fuel, guarded_one_of_not_dvd hm hnd, one_mulZ]
      | isTrue hd0 =>
        -- d ∣ m, hence d prime
        have hdm : d ∣ m := dvd_of_mod_eq_zero hd0
        have hdpr : Prime213 d := prime_of_nsf_dvd h2 hdm hnsf
        have hd0' : 0 < d := Nat.lt_of_lt_of_le (by decide) h2
        cases hsq : Nat.decEq ((m / d) % d) 0 with
        | isTrue hsq0 =>
          -- d² ∣ m : muAux = 0, and guarded d m = mFactor (vp d m) = 0
          rw [muAux_sq fuel m d sign hm1 hd0 hsq0]
          rw [prodFrom_head d m fuel]
          have hddvd : d ∣ (m / d) := dvd_of_mod_eq_zero hsq0
          have hvp_md : 1 ≤ vp d (m / d) :=
            (dvd_iff_one_le_vp
              (E213.Lib.Math.NumberTheory.MobiusMultiplicative.isPrime_of_prime hdpr)
              (by
                rcases Nat.eq_zero_or_pos (m / d) with h0 | hpos
                · exfalso
                  have : d ∣ 0 := h0 ▸ hddvd
                  -- m/d = 0 impossible since d ∣ m, m > 0
                  have hrecon : d * (m / d) = m :=
                    E213.Lib.Math.NumberTheory.GaussTotient.mul_div_of_dvd hdm
                  rw [h0, Nat.mul_zero] at hrecon
                  rw [← hrecon] at hm; exact absurd hm (Nat.lt_irrefl 0)
                · exact hpos)).mp hddvd
          have hvp2 : 2 ≤ vp d m := by
            have he : vp d (m / d) + 1 = vp d m :=
              vp_div_prime
                (E213.Lib.Math.NumberTheory.MobiusMultiplicative.isPrime_of_prime hdpr)
                hm hdm
            rw [← he]; exact Nat.succ_le_succ hvp_md
          rw [guarded_prime
                (E213.Lib.Math.NumberTheory.MobiusDivisorSum.primB_of_prime hdpr),
              mFactor_two_le_zero hvp2]
          rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.PolyIntM.mul_zeroZ]
        | isFalse hsqn =>
          -- d² ∤ m : strip, vp d m = 1
          rw [muAux_strip fuel m d sign hm1 hd0 hsqn]
          have hmd_pos : 0 < m / d := by
            rcases Nat.eq_zero_or_pos (m / d) with h0 | hpos
            · exfalso
              have hrecon : d * (m / d) = m :=
                E213.Lib.Math.NumberTheory.GaussTotient.mul_div_of_dvd hdm
              rw [h0, Nat.mul_zero] at hrecon
              rw [← hrecon] at hm; exact absurd hm (Nat.lt_irrefl 0)
            · exact hpos
          have hddmd : ¬ d ∣ (m / d) := fun hd =>
            hsqn (mod_zero_of_dvd hd0' hd)
          -- NSF (d+1) (m/d)
          have hmd_dvd_m : (m / d) ∣ m :=
            ⟨d, ((Nat.mul_comm (m / d) d).trans
                  (E213.Lib.Math.NumberTheory.GaussTotient.mul_div_of_dvd hdm)).symm⟩
          have hnsf' : NSF (d + 1) (m / d) := by
            intro q hq hqd hqmd
            have hqm : q ∣ m := E213.Meta.Nat.Valuation.dtrans hqmd hmd_dvd_m
            rcases Nat.lt_or_ge q d with hqlt | hqge
            · exact hnsf q hq hqlt hqm
            · have hqe : q = d := Nat.le_antisymm (Nat.le_of_lt_succ hqd) hqge
              rw [hqe] at hqmd; exact hddmd hqmd
          have hmd_lt : m / d < (d + 1) + fuel := by
            have hmd_le : m / d ≤ m :=
              E213.Lib.Math.NumberTheory.DivisorMultiplicative.le_of_dvd_pos' hm hmd_dvd_m
            have heq : d + (fuel + 1) = (d + 1) + fuel := by
              rw [Nat.add_assoc, Nat.add_comm 1 fuel, ← Nat.add_assoc]
            rw [heq] at hlt
            exact Nat.lt_of_le_of_lt hmd_le hlt
          rw [muAux_eq_prodFrom fuel (m / d) (d + 1) (- sign) hmd_pos h2.step hnsf' hmd_lt]
          rw [← prodFrom_strip_eq hdpr hm hdm fuel]
          rw [prodFrom_head d m fuel]
          -- guarded d m = mFactor 1 = -1
          have hvp1 : vp d m = 1 := by
            have he : vp d (m / d) + 1 = vp d m :=
              vp_div_prime
                (E213.Lib.Math.NumberTheory.MobiusMultiplicative.isPrime_of_prime hdpr)
                hm hdm
            have hvp0 : vp d (m / d) = 0 :=
              vp_eq_zero_of_not_dvd
                (E213.Lib.Math.NumberTheory.MobiusMultiplicative.isPrime_of_prime hdpr)
                hmd_pos hddmd
            rw [← he, hvp0]
          rw [guarded_prime
                (E213.Lib.Math.NumberTheory.MobiusDivisorSum.primB_of_prime hdpr),
              hvp1, mFactor_one]
          -- (-sign) * P = sign * ((-1) * P)
          generalize prodFrom (d + 1) m fuel = P
          show (- sign) * P = sign * ((-1 : Int) * P)
          rw [neg_mul sign P]
          rw [show ((-1 : Int) * P) = - P from by rw [neg_mul, one_mulZ]]
          rw [mul_neg sign P]

/-! ## ★★★ The bridge `muStruct n = mu n` (T3) -/

/-- `NSF 2 m` holds for every `m`: there is no prime `< 2`. -/
theorem nsf_two (m : Nat) : NSF 2 m := by
  intro q hq hq2 _
  exact absurd (Nat.lt_of_lt_of_le hq2 hq.1) (Nat.lt_irrefl q)

/-- ★★★ **The bridge**: the corpus trial-division `mu` agrees with the structural
    `muStruct` on every positive `n`. -/
theorem muStruct_eq_mu : ∀ n, 0 < n → muStruct n = mu n
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | 1, _ => by rw [muStruct_one]; rfl
  | n + 2, _ => by
    -- mu (n+2) = muAux (n+2) (n+2) 2 1 ; muStruct (n+2) = prodFrom 2 (n+2) (n+2)
    show muStruct (n + 2) = muAux (n + 2) (n + 2) 2 1
    have hkey : muAux (n + 2) (n + 2) 2 1
        = (1 : Int) * prodFrom 2 (n + 2) (n + 2) :=
      muAux_eq_prodFrom (n + 2) (n + 2) 2 1
        (Nat.succ_pos (n + 1)) (by decide) (nsf_two (n + 2))
        (by rw [Nat.add_comm 2 (n + 2)]; exact Nat.lt_add_of_pos_right (by decide))
    rw [hkey, E213.Meta.Int213.PolyIntM.one_mulZ]
    rfl

/-! ## Transfer: the whole `muStruct` framework lands on the corpus `mu` -/

/-- ★★★ **Corpus `mu` is multiplicative for coprimes** (transferred from
    `muStruct_mul` via the bridge). -/
theorem mu_mul {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (hcop : E213.Tactic.NatHelper.gcd213 a b = 1) :
    mu (a * b) = mu a * mu b := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  rw [← muStruct_eq_mu (a * b) hab, ← muStruct_eq_mu a ha, ← muStruct_eq_mu b hb]
  exact muStruct_mul ha hb hcop

/-- ★★★ **Corpus `mu` on a prime power** `mu (pⁱ) = mFactor i` (transferred from
    `muStruct_prime_pow`). -/
theorem mu_prime_pow {p : Nat} (hp : Prime213 p) (i : Nat) :
    mu (p ^ i) = mFactor i := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hpi : 0 < p ^ i := Nat.pos_pow_of_pos i hp0
  rw [← muStruct_eq_mu (p ^ i) hpi]
  exact E213.Lib.Math.NumberTheory.MobiusDivisorSum.muStruct_prime_pow hp i

/-- ★★★ **Corpus `mu` divisor-sum** `∀n>0, Σ_{d∣n} mu d = [n=1]` (general —
    generalizes the iter-103 table n=1..24 to all `n`), transferred from
    `muStruct_divisor_sum` via the bridge. -/
theorem mu_divisor_sum (n : Nat) (hn : 0 < n) :
    E213.Lib.Math.NumberTheory.MobiusFunction.mobiusSum n = ((n == 1).toNat : Int) := by
  show E213.Lib.Math.NumberTheory.MobiusFunction.divisorSumZ n mu = ((n == 1).toNat : Int)
  have hcong : E213.Lib.Math.NumberTheory.MobiusFunction.divisorSumZ n mu
             = E213.Lib.Math.NumberTheory.MobiusFunction.divisorSumZ n muStruct := by
    show E213.Lib.Math.NumberTheory.MobiusFunction.sumZ n
          (fun j => (E213.Lib.Math.NumberTheory.EulerTotient.dvdInd j n : Int) * mu (j + 1))
       = E213.Lib.Math.NumberTheory.MobiusFunction.sumZ n
          (fun j => (E213.Lib.Math.NumberTheory.EulerTotient.dvdInd j n : Int) * muStruct (j + 1))
    exact E213.Lib.Math.NumberTheory.MobiusPrimeCase.sumZ_congr n _ _
      (fun k _ => by rw [muStruct_eq_mu (k + 1) (Nat.succ_pos k)])
  rw [hcong]
  exact E213.Lib.Math.NumberTheory.MobiusDivisorSum.muStruct_divisor_sum n hn

/-- ★★★ **Corpus `mu` Möbius inversion** `f n = Σ_{d∣n} mu d · Σ_{e∣(n/d)} f e`,
    transferred from `mobius_inversion_g` via the bridge. -/
theorem mu_mobius_inversion (f : Nat → Int) (n : Nat) (hn : 0 < n) :
    f n = E213.Lib.Math.NumberTheory.MobiusFunction.divisorSumZ n
            (fun d => mu d * E213.Lib.Math.NumberTheory.MobiusFunction.divisorSumZ (n / d) f) := by
  rw [E213.Lib.Math.NumberTheory.MobiusInversion.mobius_inversion_g f n hn]
  show E213.Lib.Math.NumberTheory.MobiusFunction.sumZ n
        (fun j => (E213.Lib.Math.NumberTheory.EulerTotient.dvdInd j n : Int)
          * (muStruct (j + 1)
              * E213.Lib.Math.NumberTheory.MobiusFunction.divisorSumZ (n / (j + 1)) f))
     = E213.Lib.Math.NumberTheory.MobiusFunction.sumZ n
        (fun j => (E213.Lib.Math.NumberTheory.EulerTotient.dvdInd j n : Int)
          * (mu (j + 1)
              * E213.Lib.Math.NumberTheory.MobiusFunction.divisorSumZ (n / (j + 1)) f))
  exact E213.Lib.Math.NumberTheory.MobiusPrimeCase.sumZ_congr n _ _
    (fun k _ => by rw [muStruct_eq_mu (k + 1) (Nat.succ_pos k)])

end E213.Lib.Math.NumberTheory.MobiusBridge
