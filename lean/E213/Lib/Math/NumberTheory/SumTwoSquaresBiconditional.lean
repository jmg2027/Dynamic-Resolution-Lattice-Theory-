import E213.Lib.Math.NumberTheory.SumTwoSquaresOddPower
import E213.Lib.Math.NumberTheory.SumTwoSquares
import E213.Lib.Math.NumberTheory.TwoSquareTheorem
import E213.Lib.Math.NumberTheory.PrimeFactorization
import E213.Meta.Nat.VpMul
import E213.Meta.Nat.VpSeparation
import E213.Meta.Nat.NatRing213
import E213.Meta.Nat.AddMod213

/-!
# Two-square characterization — the biconditional capstone (∅-axiom) — scratch

The "only if" (`even_vp_three_mod4`) lives in `SumTwoSquaresOddPower`.  This file
proves the **"if"** at the `Nat` level and bundles the biconditional:

  `0 < n → (isSumTwoSqNat n ↔ ∀ q ≡ 3 mod 4 prime, ∃ k, vp q n = 2*k)`.

The "if" is a clean strong induction pulling out `minFac n`: a `q ≡ 3 (mod 4)`
prime factor has even valuation (hypothesis), so `p² ∣ n` and `n/p²` recurses;
any other prime factor is itself a sum of two squares (`2 = 1²+1²`, or
`two_square` for `p ≡ 1 mod 4`) so `n/p` recurses and `isSumTwoSqNat_mul` finishes.
-/

namespace E213.Lib.Math.NumberTheory.SumTwoSquaresBiconditional

open E213.Lib.Math.NumberTheory.SumTwoSquaresOddPower (isSumTwoSqNat even_vp_three_mod4)
open E213.Lib.Math.NumberTheory.SumTwoSquares (isSumTwoSq isSumTwoSq_mul)
open E213.Lib.Math.NumberTheory.TwoSquareTheorem (two_square natAbs_sq_sum)
open E213.Meta.Nat.Valuation (vp mod_zero_of_dvd)
open E213.Meta.Nat.VpMul (IsPrime213 vp_mul vp_self_pow)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd vp_div_prime vp_div_prime_other)
open E213.Lib.Math.NumberTheory.PrimeFactorization (minFac minFac_prime minFac_div)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero mod_mod_of_dvd)
open E213.Meta.Nat.NatRing213 (nat_mul_assoc)

/-! ## §1 — `Nat`-level multiplicative closure (Brahmagupta via the `Int` corpus) -/

/-- `isSumTwoSqNat m → isSumTwoSq ↑m` (lift a `Nat` representation to `Int`). -/
theorem isSumTwoSq_of_nat {m : Nat} (hm : isSumTwoSqNat m) : isSumTwoSq (m : Int) := by
  obtain ⟨a, b, hab⟩ := hm
  refine ⟨(a : Int), (b : Int), ?_⟩
  have he : ((m : Nat) : Int) = (((a * a + b * b : Nat)) : Int) := by rw [hab]
  rw [he]
  show ((a * a : Nat) : Int) + ((b * b : Nat) : Int) = (a : Int) * (a : Int) + (b : Int) * (b : Int)
  rfl

/-- ★★ **`Nat` sum-of-two-squares closure.**  If `m` and `n` are each a sum of two
    `Nat` squares, so is `m·n`.  Bridge: lift to `Int`, apply Brahmagupta
    (`isSumTwoSq_mul`), descend via `natAbs` (`natAbs_sq_sum`). -/
theorem isSumTwoSqNat_mul {m n : Nat}
    (hm : isSumTwoSqNat m) (hn : isSumTwoSqNat n) : isSumTwoSqNat (m * n) := by
  have hM := isSumTwoSq_of_nat hm
  have hN := isSumTwoSq_of_nat hn
  -- ↑m · ↑n = ↑(m*n) is a sum of two Int squares
  obtain ⟨A, B, hAB⟩ := isSumTwoSq_mul hM hN
  -- m*n = (↑(m*n)).natAbs = (A²+B²).natAbs = |A|² + |B|²
  refine ⟨A.natAbs, B.natAbs, ?_⟩
  have hcast : ((m * n : Nat) : Int) = (m : Int) * (n : Int) := by
    show ((m * n : Nat) : Int) = (m : Int) * (n : Int)
    rfl
  have hmn : ((m * n : Nat) : Int) = A * A + B * B := by rw [hcast]; exact hAB
  have habs : (m * n : Nat) = (A * A + B * B).natAbs := by
    rw [← hmn]; exact (Int.natAbs_ofNat (m * n)).symm
  rw [habs, natAbs_sq_sum]

/-! ## §2 — base building blocks: `1`, `2`, `k²`, and primes -/

/-- `1 = 1² + 0²`. -/
theorem isSumTwoSqNat_one : isSumTwoSqNat 1 := ⟨1, 0, by decide⟩

/-- `2 = 1² + 1²`. -/
theorem isSumTwoSqNat_two : isSumTwoSqNat 2 := ⟨1, 1, by decide⟩

/-- Every square `k²` is a sum of two squares (`k² + 0²`). -/
theorem isSumTwoSqNat_sq (k : Nat) : isSumTwoSqNat (k * k) :=
  ⟨k, 0, by rw [Nat.mul_zero, Nat.add_zero]⟩

/-- A prime `p ≢ 3 (mod 4)` is a sum of two squares: `p = 2` gives `1²+1²`;
    `p ≡ 1 (mod 4)` is `two_square`.  (Primes are odd except `2`; `p % 4 ∈ {1,3}`
    for odd `p`, so `p % 4 ≠ 3 ⟹ p = 2 ∨ p % 4 = 1`.) -/
theorem isSumTwoSqNat_prime_ne_three {p : Nat} (hp : IsPrime213 p)
    (hmod : p % 4 ≠ 3) : isSumTwoSqNat p := by
  -- p ≥ 2.  Decide p = 2 vs p ≥ 3.
  have hp2 : 2 ≤ p := hp.two_le
  rcases Nat.lt_or_ge p 3 with hlt | hge
  · -- p = 2
    have hpe : p = 2 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hp2
    rw [hpe]; exact isSumTwoSqNat_two
  · -- p ≥ 3 prime ⟹ p odd ⟹ p % 4 = 1 or 3; hmod kills 3.
    -- p % 4 ∈ {0,1,2,3}.  p % 4 = 0 ⟹ 4 ∣ p ⟹ 2 ∣ p contra prime>2.
    --                    p % 4 = 2 ⟹ 2 ∣ p contra.
    -- So p % 4 = 1 (since ≠ 3).  Then two_square.
    have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hge
    -- divisor dichotomy from IsPrime213
    have hdich : ∀ d, d ∣ p → d = 1 ∨ d = p := hp.2
    -- 2 ∤ p : else 2 = 1 ∨ 2 = p, but p ≥ 3
    have h2nd : ¬ (2 : Nat) ∣ p := by
      intro hd
      rcases hdich 2 hd with h1 | h2
      · exact absurd h1 (by decide)
      · rw [← h2] at hge; exact absurd hge (by decide)
    -- p % 2 = 1
    have hpodd : p % 2 = 1 := by
      have hdec : p % 2 = 0 ∨ p % 2 = 1 := by
        rcases Nat.lt_or_ge (p % 2) 1 with h | h
        · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.zero_le _))
        · exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ (Nat.mod_lt p (by decide))) h)
      rcases hdec with h0 | h1
      · exact absurd (dvd_of_mod_eq_zero h0) h2nd
      · exact h1
    -- p % 4 = 1 : p % 4 ∈ {1,3} from p odd; ≠ 3 ⟹ = 1.
    -- p % 4 determines p % 2 = (p % 4) % 2.  If p%4 ∈ {0,2} then p%2=0 contra.
    have hp4 : p % 4 = 1 := by
      have h2d4 : (2 : Nat) ∣ 4 := ⟨2, by decide⟩
      have hmod2_of4 : (p % 4) % 2 = p % 2 := mod_mod_of_dvd p h2d4
      rw [hpodd] at hmod2_of4
      -- enumerate r = p % 4 < 4, with (r % 2 = 1) and (r ≠ 3) ⟹ r = 1
      have hlt4 : p % 4 < 4 := Nat.mod_lt p (by decide)
      -- mechanical decidable enumeration on r
      revert hmod2_of4 hmod
      generalize hr : p % 4 = r
      have hlt4' : r < 4 := hr ▸ hlt4
      intro hrne hrmod
      -- hrmod : r % 2 = 1 ;  hrne : r ≠ 3.
      -- r ∈ {0,1,2,3}; r%2=1 rules out 0,2; hrne rules out 3.
      rcases Nat.lt_or_ge r 1 with h0 | h1
      · have hr0 : r = 0 := Nat.le_antisymm (Nat.le_of_lt_succ h0) (Nat.zero_le _)
        subst hr0; exact absurd hrmod (by decide)
      rcases Nat.lt_or_ge r 2 with h1' | h2
      · exact Nat.le_antisymm (Nat.le_of_lt_succ h1') h1
      rcases Nat.lt_or_ge r 3 with h2' | h3
      · have hr2 : r = 2 := Nat.le_antisymm (Nat.le_of_lt_succ h2') h2
        subst hr2; exact absurd hrmod (by decide)
      · have hr3 : r = 3 := Nat.le_antisymm (Nat.le_of_lt_succ hlt4') h3
        exact absurd hr3 hrne
    exact two_square p hp1 hdich hp4

/-! ## §3 — the prize: the "if" direction (constructive prime-power assembly) -/

/-- `minFac n` as an `IsPrime213` (same conjunction as `Prime213`). -/
theorem minFac_isPrime {n : Nat} (hn : 2 ≤ n) : IsPrime213 (minFac n) :=
  let h : Prime213 (minFac n) := minFac_prime hn
  ⟨h.1, h.2⟩

/-- ★★★★★ **The "if" direction.**  If every prime `q ≡ 3 (mod 4)` has even
    `q`-adic valuation in `n > 0`, then `n` is a sum of two squares.  Strong
    induction pulling out `p = minFac n`:
    * `p ≡ 3 (mod 4)`: hypothesis gives `vp p n = 2k`, so `p² ∣ n`; `n' = n/p²`
      satisfies the hypothesis (valuations at `p` drop by 2, others unchanged),
      `isSumTwoSqNat n'` by IH, and `n = p²·n' = (p·a)²+(p·b)²`.
    * `p ≢ 3 (mod 4)`: `p` is itself a sum of two squares
      (`isSumTwoSqNat_prime_ne_three`); `n' = n/p` satisfies the hypothesis
      (only `q ≡ 3 mod 4` matters, all those valuations unchanged); IH +
      `isSumTwoSqNat_mul` on `n = p·n'`. -/
theorem isSumTwoSqNat_of_even_vp (n : Nat) (hn : 0 < n)
    (hyp : ∀ q, IsPrime213 q → q % 4 = 3 → ∃ k, vp q n = 2 * k) :
    isSumTwoSqNat n :=
  Nat.strongRecOn n
    (motive := fun n => 0 < n →
      (∀ q, IsPrime213 q → q % 4 = 3 → ∃ k, vp q n = 2 * k) → isSumTwoSqNat n)
    (fun n ih hn hyp => by
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · -- n = 1
        have hn1 : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hn
        rw [hn1]; exact isSumTwoSqNat_one
      · -- n ≥ 2 : pull out p = minFac n
        -- derive all minFac facts, then generalise `minFac n` to `p`
        have hp0 : IsPrime213 (minFac n) := minFac_isPrime hge
        obtain ⟨hpn_mul0, hqlt0⟩ := minFac_div hge        -- p * (n/p) = n,  n/p < n
        -- abstract: ∀ p, prime, p*(n/p)=n, n/p<n  ⟹ goal
        have step : ∀ p : Nat, IsPrime213 p → p * (n / p) = n → n / p < n →
            isSumTwoSqNat n := by
          intro p hp hpn_mul hqlt
          have hp2 : 2 ≤ p := hp.two_le
          have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
          have hpn : p ∣ n := ⟨n / p, hpn_mul.symm⟩
          -- positivity of m = n/p (used in both branches' bookkeeping)
          have hmpos : 0 < n / p := by
            rcases Nat.eq_zero_or_pos (n / p) with h0 | hpos
            · exfalso; rw [h0, Nat.mul_zero] at hpn_mul
              rw [← hpn_mul] at hn; exact Nat.lt_irrefl 0 hn
            · exact hpos
          -- decide p % 4 = 3 vs not
          by_cases hp4 : p % 4 = 3
          · -- p ≡ 3 (mod 4): even valuation ⟹ p² ∣ n, descend by p²
            obtain ⟨k, hk⟩ := hyp p hp hp4                    -- vp p n = 2k
            -- name j = k - 1 once k ≥ 1, to avoid Nat-subtraction in ring_nat
            -- m = n/p ; vp p m + 1 = vp p n = 2k ⟹ vp p m = 2k-1 ≥ 1 ⟹ p ∣ m
            have hvpm1 : vp p (n / p) + 1 = vp p n := vp_div_prime hp hn hpn
            -- k ≥ 1: vp p n = 2k ≥ 1 because p ∣ n
            have hk1 : 1 ≤ k := by
              rcases Nat.eq_zero_or_pos k with h0 | hpos
              · exfalso
                rw [h0, Nat.mul_zero] at hk
                have hvz : ¬ p ∣ n := by
                  intro hd
                  have : 1 ≤ vp p n :=
                    (E213.Meta.Nat.VpSeparation.dvd_iff_one_le_vp hp hn).mp hd
                  rw [hk] at this; exact absurd this (by decide)
                exact hvz hpn
              · exact hpos
            -- vp p m = 2*(k-1) + 1 ≥ 1, so p ∣ m
            have hvpm_eq : vp p (n / p) = 2 * (k - 1) + 1 := by
              have hk' : (k - 1) + 1 = k := Nat.succ_pred_eq_of_pos hk1
              -- 2*k = 2*((k-1)+1) = (2*(k-1)+1)+1  (ring on atom (k-1)), then = via hk'
              have hring : 2 * ((k - 1) + 1) = (2 * (k - 1) + 1) + 1 := by ring_nat
              have h2k : 2 * k = (2 * (k - 1) + 1) + 1 :=
                (congrArg (fun t => 2 * t) hk').symm.trans hring
              have hh : vp p (n / p) + 1 = (2 * (k - 1) + 1) + 1 := by rw [hvpm1, hk, h2k]
              exact E213.Meta.Nat.NatRing213.nat_add_right_cancel hh
            have hpm : p ∣ (n / p) := by
              apply (E213.Meta.Nat.VpSeparation.dvd_iff_one_le_vp hp hmpos).mpr
              rw [hvpm_eq]; exact Nat.le_add_left 1 (2 * (k - 1))
            -- n' = m/p = c with m = p*c ; n = p*p*n'
            have hpm' := hpm
            obtain ⟨c, hc⟩ := hpm'                             -- n/p = p * c
            have hn'_c : (n / p) / p = c := by
              rw [hc]
              exact E213.Meta.Nat.NatDiv213.mul_div_cancel_left_pure p c hppos
            have hn'pos : 0 < (n / p) / p := by
              rw [hn'_c]
              rcases Nat.eq_zero_or_pos c with h0 | hpos
              · exfalso; rw [h0, Nat.mul_zero] at hc
                rw [hc] at hmpos; exact Nat.lt_irrefl 0 hmpos
              · exact hpos
            -- n = p*p*((n/p)/p)
            have hn_eq : n = p * p * ((n / p) / p) := by
              rw [hn'_c, ← hpn_mul, hc, nat_mul_assoc]
            -- (n/p)/p < n
            have hn'lt : (n / p) / p < n := by
              rw [hn'_c]
              have hcm : c < n / p := by
                rw [hc]
                have h1c : 1 * c < p * c := by
                  apply E213.Meta.Nat.NatRing213.nat_mul_lt_mul_right
                  · rcases Nat.eq_zero_or_pos c with h0 | hpos
                    · exfalso; rw [h0, Nat.mul_zero] at hc; rw [hc] at hmpos
                      exact Nat.lt_irrefl 0 hmpos
                    · exact hpos
                  · exact Nat.lt_of_lt_of_le (by decide) hp2
                rwa [Nat.one_mul] at h1c
              exact Nat.lt_trans hcm hqlt
            -- n' satisfies the hypothesis: split q = p vs q ≠ p
            have hyp' : ∀ q, IsPrime213 q → q % 4 = 3 → ∃ j, vp q ((n / p) / p) = 2 * j := by
              intro q hq hq4
              by_cases hqp : q = p
              · rw [hqp]
                refine ⟨k - 1, ?_⟩
                -- vp p ((n/p)/p) + 1 = vp p (n/p) = 2*(k-1)+1
                have h1 : vp p ((n / p) / p) + 1 = vp p (n / p) := vp_div_prime hp hmpos hpm
                rw [hvpm_eq] at h1
                exact E213.Meta.Nat.NatRing213.nat_add_right_cancel h1
              · obtain ⟨kq, hkq⟩ := hyp q hq hq4
                refine ⟨kq, ?_⟩
                have h1 : vp q ((n / p) / p) = vp q (n / p) :=
                  vp_div_prime_other hp hq hqp hmpos hpm
                have h2 : vp q (n / p) = vp q n := vp_div_prime_other hp hq hqp hn hpn
                rw [h1, h2]; exact hkq
            have hsq' : isSumTwoSqNat ((n / p) / p) := ih ((n / p) / p) hn'lt hn'pos hyp'
            obtain ⟨a, b, hab⟩ := hsq'
            -- n = p*p*n' = (p*a)² + (p*b)²
            refine ⟨p * a, p * b, ?_⟩
            rw [hn_eq, hab]; ring_nat
          · -- p ≢ 3 (mod 4): p is a sum of two squares; descend by p
            have hpsq : isSumTwoSqNat p := isSumTwoSqNat_prime_ne_three hp hp4
            -- n' = n/p satisfies the hypothesis : q≡3mod4 ⟹ q≠p, vp q n' = vp q n
            have hyp' : ∀ q, IsPrime213 q → q % 4 = 3 → ∃ j, vp q (n / p) = 2 * j := by
              intro q hq hq4
              have hqp : q ≠ p := by
                intro he; rw [he] at hq4; exact hp4 hq4
              obtain ⟨kq, hkq⟩ := hyp q hq hq4
              refine ⟨kq, ?_⟩
              have h1 : vp q (n / p) = vp q n := vp_div_prime_other hp hq hqp hn hpn
              rw [h1]; exact hkq
            have hsq' : isSumTwoSqNat (n / p) := ih (n / p) hqlt hmpos hyp'
            have hn_eq : n = p * (n / p) := hpn_mul.symm
            rw [hn_eq]; exact isSumTwoSqNat_mul hpsq hsq'
        exact step (minFac n) hp0 hpn_mul0 hqlt0)
    hn hyp

/-! ## §4 — the biconditional capstone -/

/-- ★★★★★ **Two-square characterization (biconditional).**  For `n > 0`:
    `n` is a sum of two squares **iff** every prime `q ≡ 3 (mod 4)` has even
    `q`-adic valuation in `n`.  "Only if" = `even_vp_three_mod4`; "if" =
    `isSumTwoSqNat_of_even_vp`. -/
theorem isSumTwoSqNat_iff_even_vp (n : Nat) (hn : 0 < n) :
    isSumTwoSqNat n ↔ (∀ q, IsPrime213 q → q % 4 = 3 → ∃ k, vp q n = 2 * k) :=
  ⟨fun hsq q hq hq4 => even_vp_three_mod4 hq hq4 n hn hsq,
   fun hyp => isSumTwoSqNat_of_even_vp n hn hyp⟩

/-! ## §5 — concrete smokes -/

/-- `45 = 3²·5` (vp₃ = 2, even): `45 = 6² + 3²` — sum of two squares. -/
theorem smoke_45 : isSumTwoSqNat 45 := ⟨6, 3, by decide⟩

/-- `45` as a sum of two squares **by the multiplicative closure** `9·5`
    (`9 = 3²+0²`, `5 = 2²+1²`), exercising `isSumTwoSqNat_mul`. -/
theorem smoke_5 : isSumTwoSqNat 5 := ⟨2, 1, by decide⟩

theorem smoke_45_via_mul : isSumTwoSqNat 45 :=
  isSumTwoSqNat_mul (isSumTwoSqNat_sq 3) smoke_5

/-- `21 = 3·7` (vp₃ = 1, odd): **not** a sum of two squares.  Via the "only if"
    side of the biconditional + the odd-valuation obstruction at `q = 3`. -/
theorem smoke_not_21 : ¬ isSumTwoSqNat 21 :=
  E213.Lib.Math.NumberTheory.SumTwoSquaresOddPower.not_isSumTwoSqNat_twentyone

/-- The biconditional's forward (only-if) reading at `n = 21` would force
    `vp 3 21` even; it is `1` (odd), confirming `21` is not a sum of two squares
    (contrapositive form, exercising `isSumTwoSqNat_iff_even_vp.mp`). -/
theorem smoke_21_iff_forces_even : ¬ isSumTwoSqNat 21 := by
  intro hsq
  have heven := (isSumTwoSqNat_iff_even_vp 21 (by decide)).mp hsq
  obtain ⟨k, hk⟩ :=
    heven 3 E213.Lib.Math.NumberTheory.SumTwoSquaresOddPower.isPrime3 (by decide)
  -- vp 3 21 = 1, so 1 = 2*k, impossible
  rw [E213.Lib.Math.NumberTheory.SumTwoSquaresOddPower.vp_3_21] at hk
  exact E213.Lib.Math.NumberTheory.SumTwoSquaresOddPower.one_not_two_mul ⟨k, hk⟩

end E213.Lib.Math.NumberTheory.SumTwoSquaresBiconditional
