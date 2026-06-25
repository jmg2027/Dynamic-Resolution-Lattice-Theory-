import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.Combinatorics.Vandermonde
import E213.Lib.Math.NumberTheory.ModArith.LucasTheorem
import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.NatRing213
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.Valuation
import E213.Meta.Tactic.NatHelper

/-!
# Lucas' theorem — the general digit-step (∅-axiom)

★★★ Closes the open follow-up of `NumberTheory/ModArith/LucasTheorem.lean` (which
had `freshman_binom` + the digit-step table, but not the general step): for a prime
`p` and digits `r,s < p`,

  ★★★ `lucas_step : choose (p·n + r) (p·k + s) ≡ choose n k · choose r s (mod p)`.

A fully **combinatorial Vandermonde-collapse** proof (the corpus `freshman_dream` is
numeric `(a+1)^p`, no polynomial coefficient extraction).  Key pieces:
  · `gen_freshman` — `p ∤ i → choose (p·n) i ≡ 0 (mod p)` (induction on n via the
    Vandermonde step `choose(pn+p)(i) ≡ choose(pn)(i) + choose(pn)(i−p)`).
  · `choose_pn_pk` — `choose (p·n) (p·k) ≡ choose n k (mod p)`.
  · `lucas_step` — Vandermonde-split `choose(pn+r)(pk+s) = Σ_j choose(pn)(j)·choose r(pk+s−j)`,
    the prefix vanishes mod p, the suffix collapses to the single `j=pk` survivor.
Reuses the iter-96 `Combinatorics/Vandermonde.vandermonde_sum`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.LucasStepGeneral

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_zero_succ choose_succ_succ choose_succ_mul
   choose_eq_zero_of_lt choose_self choose_symm_sum)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
  (sumTo sumTo_zero sumTo_succ sumTo_eq_zero_of_all_zero)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_add_func sumTo_congr sumTo_mul_left)
open E213.Lib.Math.Combinatorics.Vandermonde (vandermonde vandermonde_sum)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 prime_dvd_mul)
open E213.Lib.Math.NumberTheory.ModArith.LucasTheorem (prime_not_dvd_pos_lt freshman_binom)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero mod_self add_mod_gen mod_mod zero_mod)
open E213.Meta.Nat.Valuation (mod_zero_of_dvd)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (mul_assoc add_mul sub_add_cancel add_sub_of_le sub_pos_of_lt
  add_sub_add_left)
open E213.Meta.Nat.NatRing213 (nat_add_sub_self_right)
open E213.Meta.Nat.Gcd213 (dvd_add_213)
open E213.Meta.Nat.NatDiv213 (div_add_mod_pure)

/-- `(p * x) % p = 0`. -/
theorem mul_p_mod_eq_zero (p x : Nat) : (p * x) % p = 0 := by
  rw [mul_mod_left_pure p x p, mod_self, Nat.zero_mul, zero_mod]

/-- `p ∣ (p * x)`. -/
theorem dvd_mul_p (p x : Nat) : p ∣ (p * x) := ⟨x, rfl⟩

/-- `1 % p = 1` when `2 ≤ p`. -/
theorem one_mod_of_two_le {p : Nat} (hp : 2 ≤ p) : (1 : Nat) % p = 1 :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide) hp)

/-- `choose p m % p = 0` for every `m` with `m ≠ 0` and `m ≠ p` (`Prime213 p`).
    Three regimes: `0 < m < p` (freshman), `m = p` excluded, `p < m` (zero row). -/
theorem choose_p_mod_zero {p m : Nat} (hp : Prime213 p)
    (hm0 : m ≠ 0) (hmp : m ≠ p) : (choose p m) % p = 0 := by
  rcases Nat.lt_or_ge m p with hlt | hge
  · -- 0 < m < p
    exact freshman_binom hp (Nat.pos_of_ne_zero hm0) hlt
  · -- p ≤ m, and m ≠ p ⇒ p < m ⇒ choose p m = 0
    have hpm : p < m := Nat.lt_of_le_of_ne hge (fun h => hmp h.symm)
    rw [choose_eq_zero_of_lt p m hpm, zero_mod]

/-- `choose p 0 % p = 1` and `choose p p % p = 1` (the two survivors). -/
theorem choose_p_mod_zero_idx {p : Nat} (hp : Prime213 p) : (choose p 0) % p = 1 := by
  rw [choose_zero_right]; exact one_mod_of_two_le hp.1

theorem choose_p_mod_p_idx {p : Nat} (hp : Prime213 p) : (choose p p) % p = 1 := by
  rw [choose_self]; exact one_mod_of_two_le hp.1

/-! ## Mod-p collapse of the `choose p`-convolution

For fixed `i` and a function `g`, consider `Σ_{k=0}^{i} g k · choose p (i-k)`.
Mod p, `choose p (i-k)` is `≡ 1` exactly at `i-k ∈ {0, p}` and `≡ 0` otherwise.
We show this sum is `≡ g i + g (i-p)·[p ≤ i] (mod p)`.

Stated additively to avoid `if`: we prove the **head-collapse**
`sumTo (i+1) (fun k => g k * choose p (i-k)) % p = (g i + R) % p` where `R` is the
contribution from the `i-k = p` survivor.  We do `i < p` and `p ≤ i` separately. -/

/-- For `i < p`: every term with `k < i` has `0 < i - k < p` so `choose p (i-k) ≡ 0`;
    only the `k = i` term (`choose p 0 = 1`) survives.  Hence the convolution
    `≡ g i (mod p)`. -/
theorem conv_collapse_lt {p : Nat} (hp : Prime213 p) (g : Nat → Nat) :
    ∀ i, i < p → (sumTo (i + 1) (fun k => g k * choose p (i - k))) % p = (g i) % p := by
  intro i hip
  -- split off the last term k = i
  rw [sumTo_succ]
  -- sumTo i (...) + g i * choose p (i - i)
  rw [show i - i = 0 from by
        have h := nat_add_sub_self_right 0 i; rw [Nat.zero_add] at h; exact h,
      choose_zero_right, Nat.mul_one]
  -- the head sumTo i (...) vanishes mod p
  have hhead : (sumTo i (fun k => g k * choose p (i - k))) % p = 0 := by
    apply sumTo_eq_zero_of_all_zero p i (fun k => g k * choose p (i - k))
    intro k hk
    -- k < i ⇒ 0 < i - k ≤ i < p ⇒ choose p (i-k) ≡ 0
    have hik_pos : 0 < i - k := sub_pos_of_lt hk
    have hik_le : i - k ≤ i := Nat.le.intro (sub_add_cancel (Nat.le_of_lt hk))
    have hik_lt : i - k < p := Nat.lt_of_le_of_lt hik_le hip
    have hcz : (choose p (i - k)) % p = 0 :=
      freshman_binom hp hik_pos hik_lt
    rw [mul_mod_right_pure (g k) (choose p (i - k)) p, hcz, Nat.mul_zero, zero_mod]
  rw [add_mod_gen (sumTo i (fun k => g k * choose p (i - k))) (g i) p, hhead, Nat.zero_add, mod_mod]

/-- Range concatenation: `sumTo (a + b) f = sumTo a f + sumTo b (fun k => f (a + k))`. -/
theorem sumTo_split_at (a : Nat) (f : Nat → Nat) :
    ∀ b, sumTo (a + b) f = sumTo a f + sumTo b (fun k => f (a + k))
  | 0 => by rw [Nat.add_zero]; show sumTo a f = sumTo a f + 0; rw [Nat.add_zero]
  | b + 1 => by
    show sumTo (a + (b + 1)) f = sumTo a f + (sumTo b (fun k => f (a + k)) + f (a + b))
    rw [show a + (b + 1) = (a + b) + 1 from (Nat.add_assoc a b 1).symm, sumTo_succ,
        sumTo_split_at a f b, Nat.add_assoc]

/-- Σ reflection (peeled form): `sumTo (m+1) f = sumTo (m+1) (fun k => f (m - k))`. -/
theorem sumTo_reflect (f : Nat → Nat) :
    ∀ m, sumTo (m + 1) f = sumTo (m + 1) (fun k => f (m - k))
  | 0 => by show (0 : Nat) + f 0 = 0 + f (0 - 0); rfl
  | m + 1 => by
    rw [sumTo_succ]
    rw [sumTo_split_first (m + 1) (fun k => f ((m + 1) - k))]
    rw [Nat.sub_zero]
    have hc : sumTo (m + 1) (fun k => f ((m + 1) - (k + 1))) = sumTo (m + 1) f := by
      have hstep : sumTo (m + 1) (fun k => f ((m + 1) - (k + 1)))
                 = sumTo (m + 1) (fun k => f (m - k)) :=
        sumTo_congr (m + 1)
          (fun k => f ((m + 1) - (k + 1))) (fun k => f (m - k))
          (fun k _ => by
            show f ((m + 1) - (k + 1)) = f (m - k)
            rw [Nat.succ_sub_succ_eq_sub m k])
      rw [hstep, ← sumTo_reflect f m]
    rw [hc, Nat.add_comm (f (m + 1)) (sumTo (m + 1) f)]

/-- Reflection specialised to the `choose p`-convolution:
    `Σ_{k=0}^{i} g k · choose p (i-k) = Σ_{j=0}^{i} g (i-j) · choose p j`. -/
theorem conv_reflect (p : Nat) (g : Nat → Nat) (i : Nat) :
    sumTo (i + 1) (fun k => g k * choose p (i - k))
       = sumTo (i + 1) (fun j => g (i - j) * choose p j) := by
  rw [sumTo_reflect (fun k => g k * choose p (i - k)) i]
  exact sumTo_congr (i + 1)
    (fun k => g (i - k) * choose p (i - (i - k)))
    (fun j => g (i - j) * choose p j)
    (fun k hk => by
      have hki : k ≤ i := Nat.le_of_lt_succ hk
      show g (i - k) * choose p (i - (i - k)) = g (i - k) * choose p k
      rw [show i - (i - k) = k from E213.Tactic.NatHelper.sub_sub_self hki])

/-- Head block: `Σ_{j=0}^{p-1} h j · choose p j ≡ h 0 (mod p)` (`Prime213 p`). -/
theorem head_block {p : Nat} (hp : Prime213 p) (h : Nat → Nat) :
    (sumTo p (fun j => h j * choose p j)) % p = (h 0) % p := by
  obtain ⟨p', rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by
    rw [sub_add_cancel (Nat.le_trans (by decide) hp.1)]⟩
  rw [sumTo_split_first p' (fun j => h j * choose (p' + 1) j)]
  rw [show choose (p' + 1) 0 = 1 from choose_zero_right (p' + 1), Nat.mul_one]
  have htail : (sumTo p' (fun j => h (j + 1) * choose (p' + 1) (j + 1))) % (p' + 1) = 0 := by
    apply sumTo_eq_zero_of_all_zero (p' + 1) p' (fun j => h (j + 1) * choose (p' + 1) (j + 1))
    intro j hj
    have hcz : (choose (p' + 1) (j + 1)) % (p' + 1) = 0 :=
      freshman_binom hp (Nat.succ_pos j) (Nat.succ_lt_succ hj)
    rw [mul_mod_right_pure (h (j + 1)) (choose (p' + 1) (j + 1)) (p' + 1),
        hcz, Nat.mul_zero, zero_mod]
  rw [add_mod_gen (h 0) (sumTo p' (fun j => h (j + 1) * choose (p' + 1) (j + 1))) (p' + 1),
      htail, Nat.add_zero, mod_mod]

/-- Tail block: `Σ_{t=0}^{m} h (p+t) · choose p (p+t) ≡ h p (mod p)` (`Prime213 p`).
    `t=0` gives `choose p p = 1`; `t ≥ 1` gives `choose p (p+t) = 0` (row past the
    diagonal, exactly zero). -/
theorem tail_block {p : Nat} (hp : Prime213 p) (h : Nat → Nat) (m : Nat) :
    (sumTo (m + 1) (fun t => h (p + t) * choose p (p + t))) % p = (h p) % p := by
  rw [sumTo_split_first m (fun t => h (p + t) * choose p (p + t))]
  -- = h (p+0)*choose p (p+0) + sumTo m (fun t => h (p+(t+1))*choose p (p+(t+1)))
  rw [show p + 0 = p from Nat.add_zero p, show choose p p = 1 from choose_self p, Nat.mul_one]
  have htail : (sumTo m (fun t => h (p + (t + 1)) * choose p (p + (t + 1)))) = 0 := by
    have hz : sumTo m (fun t => h (p + (t + 1)) * choose p (p + (t + 1)))
            = sumTo m (fun _ => 0) := by
      apply sumTo_congr m (fun t => h (p + (t + 1)) * choose p (p + (t + 1))) (fun _ => 0)
      intro t _
      show h (p + (t + 1)) * choose p (p + (t + 1)) = 0
      rw [show choose p (p + (t + 1)) = 0 from
            choose_eq_zero_of_lt p (p + (t + 1)) (by
              rw [show p + (t + 1) = (p + t) + 1 from (Nat.add_assoc p t 1).symm]
              exact Nat.lt_succ_of_le (Nat.le_add_right p t)),
          Nat.mul_zero]
    rw [hz, E213.Lib.Math.Combinatorics.Vandermonde.sumTo_const_zero m]
  rw [add_mod_gen (h p) (sumTo m (fun t => h (p + (t + 1)) * choose p (p + (t + 1)))) p,
      htail, zero_mod, Nat.add_zero, mod_mod]

/-- Two-survivor collapse (reflected, `p ≤ i`):
    `Σ_{j=0}^{i} g (i-j) · choose p j ≡ g i + g (i-p) (mod p)`. -/
theorem conv_collapse_ge {p : Nat} (hp : Prime213 p) (g : Nat → Nat) (i : Nat)
    (hpi : p ≤ i) :
    (sumTo (i + 1) (fun j => g (i - j) * choose p j)) % p
      = (g i + g (i - p)) % p := by
  -- i + 1 = p + (i + 1 - p), and i + 1 - p = (i - p) + 1
  have hsplit : i + 1 = p + ((i - p) + 1) := by
    rw [show p + ((i - p) + 1) = (p + (i - p)) + 1 from (Nat.add_assoc p (i - p) 1).symm,
        add_sub_of_le hpi]
  rw [hsplit, sumTo_split_at p (fun j => g (i - j) * choose p j) ((i - p) + 1)]
  -- block1 = sumTo p (fun j => g (i-j) * choose p j); block2 = sumTo ((i-p)+1) (fun t => g (i-(p+t)) * choose p (p+t))
  have hblock1 : (sumTo p (fun j => g (i - j) * choose p j)) % p = (g i) % p := by
    have := head_block hp (fun j => g (i - j))
    rw [show i - 0 = i from Nat.sub_zero i] at this
    exact this
  have hblock2 : (sumTo ((i - p) + 1) (fun t => g (i - (p + t)) * choose p (p + t))) % p
               = (g (i - p)) % p := tail_block hp (fun j => g (i - j)) (i - p)
  -- combine
  rw [add_mod_gen (sumTo p (fun j => g (i - j) * choose p j))
        (sumTo ((i - p) + 1) (fun t => g (i - (p + t)) * choose p (p + t))) p,
      hblock1, hblock2, ← add_mod_gen (g i) (g (i - p)) p]

/-- One-survivor collapse (reflected, `i < p`): every `j` with `0 < j ≤ i < p` gives
    `choose p j ≡ 0`; only `j = 0` survives.  `≡ g i (mod p)`. -/
theorem conv_collapse_refl_lt {p : Nat} (hp : Prime213 p) (g : Nat → Nat) (i : Nat)
    (hip : i < p) :
    (sumTo (i + 1) (fun j => g (i - j) * choose p j)) % p = (g i) % p := by
  rw [sumTo_split_first i (fun j => g (i - j) * choose p j)]
  -- = g (i-0)*choose p 0 + sumTo i (fun j => g (i-(j+1))*choose p (j+1))
  rw [show i - 0 = i from Nat.sub_zero i,
      show choose p 0 = 1 from choose_zero_right p, Nat.mul_one]
  have htail : (sumTo i (fun j => g (i - (j + 1)) * choose p (j + 1))) % p = 0 := by
    apply sumTo_eq_zero_of_all_zero p i (fun j => g (i - (j + 1)) * choose p (j + 1))
    intro j hj
    have hjp : j + 1 < p := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hj) hip
    have hcz : (choose p (j + 1)) % p = 0 := freshman_binom hp (Nat.succ_pos j) hjp
    rw [mul_mod_right_pure (g (i - (j + 1))) (choose p (j + 1)) p, hcz, Nat.mul_zero, zero_mod]
  rw [add_mod_gen (g i) (sumTo i (fun j => g (i - (j + 1)) * choose p (j + 1))) p,
      htail, Nat.add_zero, mod_mod]

/-- Step recurrence (`i < p`): `choose (p*n + p) i ≡ choose (p*n) i (mod p)`. -/
theorem step_lt {p : Nat} (hp : Prime213 p) (n i : Nat) (hip : i < p) :
    (choose (p * n + p) i) % p = (choose (p * n) i) % p := by
  rw [← vandermonde_sum (p * n) p i, conv_reflect p (fun k => choose (p * n) k) i]
  exact conv_collapse_refl_lt hp (fun k => choose (p * n) k) i hip

/-- Step recurrence (`p ≤ i`): `choose (p*n + p) i ≡ choose (p*n) i + choose (p*n) (i-p) (mod p)`. -/
theorem step_ge {p : Nat} (hp : Prime213 p) (n i : Nat) (hpi : p ≤ i) :
    (choose (p * n + p) i) % p = (choose (p * n) i + choose (p * n) (i - p)) % p := by
  rw [← vandermonde_sum (p * n) p i, conv_reflect p (fun k => choose (p * n) k) i]
  exact conv_collapse_ge hp (fun k => choose (p * n) k) i hpi

/-- `p ∤ i → p ∤ (i - p)` (for `p ≤ i`): if `p ∣ i-p` then `p ∣ (i-p)+p = i`. -/
theorem not_dvd_sub_of_not_dvd {p i : Nat} (hpi : p ≤ i) (h : ¬ p ∣ i) : ¬ p ∣ (i - p) := by
  intro hd
  exact h (by
    have : p ∣ (i - p) + p := dvd_add_213 p (i - p) p hd ⟨1, (Nat.mul_one p).symm⟩
    rw [sub_add_cancel hpi] at this
    exact this)

/-- `p * (n + 1) = p * n + p` (pure). -/
theorem mul_succ_pure (p n : Nat) : p * (n + 1) = p * n + p := by
  rw [Nat.mul_add, Nat.mul_one]

/-- ★★ **Generalized freshman's binom** — the heart of Lucas:
    `p ∤ i → choose (p * n) i ≡ 0 (mod p)` (`Prime213 p`).  Induction on `n` via the
    Vandermonde step recurrence (`step_lt` / `step_ge`). -/
theorem gen_freshman {p : Nat} (hp : Prime213 p) :
    ∀ (n i : Nat), ¬ p ∣ i → (choose (p * n) i) % p = 0
  | 0, i, hpi => by
    -- p ∤ i ⇒ i ≠ 0 ⇒ choose 0 i = 0
    have hi0 : i ≠ 0 := fun h => hpi (h ▸ ⟨0, (Nat.mul_zero p).symm⟩)
    rw [show p * 0 = 0 from Nat.mul_zero p]
    obtain ⟨i', rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by
      rw [sub_add_cancel (Nat.pos_of_ne_zero hi0)]⟩
    rw [show choose 0 (i' + 1) = 0 from rfl, zero_mod]
  | n + 1, i, hpi => by
    rw [mul_succ_pure p n]
    rcases Nat.lt_or_ge i p with hlt | hge
    · rw [step_lt hp n i hlt]
      exact gen_freshman hp n i hpi
    · rw [step_ge hp n i hge,
          add_mod_gen (choose (p * n) i) (choose (p * n) (i - p)) p,
          gen_freshman hp n i hpi,
          gen_freshman hp n (i - p) (not_dvd_sub_of_not_dvd hge hpi),
          Nat.add_zero, zero_mod]

/-- `choose 0 (p*k) % p`: `1` if `k=0`, else `0` (`0 < p`). -/
theorem choose_zero_pk {p : Nat} (hp0 : 0 < p) (k : Nat) :
    (choose 0 (p * k)) % p = (choose 0 k) % p := by
  cases k with
  | zero => rw [show p * 0 = 0 from Nat.mul_zero p]
  | succ k' =>
    have hpos : 0 < p * (k' + 1) := Nat.mul_pos hp0 (Nat.succ_pos k')
    obtain ⟨m, hm⟩ : ∃ m, p * (k' + 1) = m + 1 := ⟨p * (k' + 1) - 1, by
      rw [sub_add_cancel hpos]⟩
    rw [hm, show choose 0 (m + 1) = 0 from rfl, show choose 0 (k' + 1) = 0 from rfl]

/-- ★★ **Multiple-of-p reduction**: `choose (p*n) (p*k) ≡ choose n k (mod p)`.
    Induction on `n`; the `p ≤ p*k` (k ≥ 1) step uses `step_ge` + `gen`-IH twice +
    Pascal; `k = 0` is the diagonal-top `1 ≡ 1`. -/
theorem choose_pn_pk {p : Nat} (hp : Prime213 p) :
    ∀ (n k : Nat), (choose (p * n) (p * k)) % p = (choose n k) % p
  | 0, k => by
    rw [show p * 0 = 0 from Nat.mul_zero p]
    exact choose_zero_pk (Nat.lt_of_lt_of_le (by decide) hp.1) k
  | n + 1, k => by
    rw [mul_succ_pure p n]
    cases k with
    | zero =>
      -- choose (p*n+p) 0 = 1 = choose (n+1) 0
      rw [show p * 0 = 0 from Nat.mul_zero p,
          show choose (p * n + p) 0 = 1 from choose_zero_right _,
          show choose (n + 1) 0 = 1 from choose_zero_right _]
    | succ k' =>
      -- p*(k'+1) = p*k' + p ≥ p
      have hpk : p ≤ p * (k' + 1) := by
        rw [mul_succ_pure p k']; exact Nat.le_add_left p (p * k')
      rw [step_ge hp n (p * (k' + 1)) hpk]
      -- ≡ choose(p*n)(p*(k'+1)) + choose(p*n)(p*(k'+1) - p)
      have hsub : p * (k' + 1) - p = p * k' := by
        rw [mul_succ_pure p k']
        exact E213.Tactic.NatHelper.add_sub_cancel_right (p * k') p
      rw [hsub]
      rw [add_mod_gen (choose (p * n) (p * (k' + 1))) (choose (p * n) (p * k')) p,
          choose_pn_pk hp n (k' + 1), choose_pn_pk hp n k',
          ← add_mod_gen (choose n (k' + 1)) (choose n k') p]
      -- RHS: choose (n+1) (k'+1) = choose n k' + choose n (k'+1)
      rw [show choose (n + 1) (k' + 1) = choose n k' + choose n (k' + 1) from
            choose_succ_succ n k', Nat.add_comm (choose n k') (choose n (k' + 1))]

/-! ## Final assembly: the general Lucas digit-step

Vandermonde-split `choose (p*n + r) (p*k + s)` over the top `(p*n) + r`, bottom
`p*k + s`.  Mod p only the `j = p*k` term survives:
  · `p ∤ j` ⇒ `choose (p*n) j ≡ 0` (`gen_freshman`);
  · `p ∣ j`, `j < p*k` ⇒ `choose r (p*k+s − j) = 0` (argument `> r`);
  · `j = p*k` ⇒ `choose (p*n) (p*k) · choose r s ≡ choose n k · choose r s`. -/

/-- Prefix terms (`j < p*k`) of the Lucas convolution vanish mod p. -/
theorem lucas_prefix_zero {p : Nat} (hp : Prime213 p) (n k r s : Nat)
    (hr : r < p) (j : Nat) (hj : j < p * k) :
    (choose (p * n) j * choose r (p * k + s - j)) % p = 0 := by
  by_cases hpj : j % p = 0
  · -- p ∣ j ⇒ choose r (p*k+s-j) = 0 since p*k+s-j > r
    have hdvd : p ∣ j := dvd_of_mod_eq_zero hpj
    obtain ⟨t, rfl⟩ := hdvd
    -- p*t < p*k ⇒ t < k ⇒ t+1 ≤ k ⇒ p*t + p ≤ p*k
    have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
    have htk : t < k := by
      rcases Nat.lt_or_ge t k with h | h
      · exact h
      · exact absurd hj (Nat.not_lt_of_ge (Nat.mul_le_mul_left p h))
    have hstep : p * t + p ≤ p * k := by
      rw [← mul_succ_pure p t]
      exact Nat.mul_le_mul_left p (Nat.succ_le_of_lt htk)
    -- p*k + s - p*t ≥ p + s ≥ p > r
    have hge : p ≤ p * k + s - p * t := by
      have h1 : p * t + p ≤ p * k + s :=
        Nat.le_trans hstep (Nat.le_add_right (p * k) s)
      have h2 : p * t + p - p * t ≤ p * k + s - p * t :=
        Nat.sub_le_sub_right h1 (p * t)
      rw [Nat.add_comm (p * t) p,
          E213.Tactic.NatHelper.add_sub_cancel_right p (p * t)] at h2
      exact h2
    have hrlt : r < p * k + s - p * t := Nat.lt_of_lt_of_le hr hge
    rw [show choose r (p * k + s - p * t) = 0 from choose_eq_zero_of_lt r _ hrlt,
        Nat.mul_zero, zero_mod]
  · -- p ∤ j ⇒ choose (p*n) j ≡ 0
    have hcz : (choose (p * n) j) % p = 0 :=
      gen_freshman hp n j (fun hd => hpj (mod_zero_of_dvd
        (Nat.lt_of_lt_of_le (by decide) hp.1) hd))
    rw [mul_mod_left_pure (choose (p * n) j) (choose r (p * k + s - j)) p, hcz,
        Nat.zero_mul, zero_mod]

/-- `(p*k + t) % p = t % p`: the multiple `p*k` drops out. -/
theorem add_mul_mod_self (p k t : Nat) : (p * k + t) % p = t % p := by
  rw [add_mod_gen (p * k) t p, mul_p_mod_eq_zero p k, Nat.zero_add, mod_mod]

/-- Suffix block of the Lucas convolution: only `t=0` survives mod p.
    `Σ_{t=0}^{s} choose (p*n) (p*k+t) · choose r (s-t) ≡ choose (p*n) (p*k) · choose r s (mod p)`. -/
theorem lucas_suffix {p : Nat} (hp : Prime213 p) (n k r s : Nat) (hs : s < p) :
    (sumTo (s + 1) (fun t => choose (p * n) (p * k + t) * choose r (s - t))) % p
      = (choose (p * n) (p * k) * choose r s) % p := by
  rw [sumTo_split_first s (fun t => choose (p * n) (p * k + t) * choose r (s - t))]
  -- = (choose (p*n) (p*k+0) * choose r (s-0)) + sumTo s (fun t => ... (t+1))
  rw [show p * k + 0 = p * k from Nat.add_zero (p * k), Nat.sub_zero]
  have htail : (sumTo s (fun t => choose (p * n) (p * k + (t + 1)) * choose r (s - (t + 1)))) % p = 0 := by
    apply sumTo_eq_zero_of_all_zero p s (fun t => choose (p * n) (p * k + (t + 1)) * choose r (s - (t + 1)))
    intro t ht
    -- 0 < t+1 ≤ s < p ⇒ p ∤ (p*k + (t+1)) ⇒ first factor ≡ 0
    have htp : t + 1 < p := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt ht) hs
    have hmod : (p * k + (t + 1)) % p = t + 1 := by
      rw [add_mul_mod_self p k (t + 1), Nat.mod_eq_of_lt htp]
    have hndvd : ¬ p ∣ (p * k + (t + 1)) := by
      intro hd
      have : (p * k + (t + 1)) % p = 0 :=
        mod_zero_of_dvd (Nat.lt_of_lt_of_le (by decide) hp.1) hd
      rw [hmod] at this
      exact Nat.noConfusion this
    have hcz : (choose (p * n) (p * k + (t + 1))) % p = 0 := gen_freshman hp n _ hndvd
    rw [mul_mod_left_pure (choose (p * n) (p * k + (t + 1))) (choose r (s - (t + 1))) p,
        hcz, Nat.zero_mul, zero_mod]
  rw [add_mod_gen (choose (p * n) (p * k) * choose r s)
        (sumTo s (fun t => choose (p * n) (p * k + (t + 1)) * choose r (s - (t + 1)))) p,
      htail, Nat.add_zero, mod_mod]

/-- ★★★ **General Lucas digit-step** (`Prime213 p`, `r < p`, `s < p`):
    `choose (p*n + r) (p*k + s) ≡ choose n k · choose r s (mod p)`.

    Vandermonde-split over the top `(p*n) + r`; the prefix `j < p*k` vanishes
    (`lucas_prefix_zero`), the suffix collapses to the single `j = p*k` survivor
    (`lucas_suffix`), and `choose (p*n) (p*k) ≡ choose n k` (`choose_pn_pk`). -/
theorem lucas_step {p : Nat} (hp : Prime213 p) (n k r s : Nat)
    (hr : r < p) (hs : s < p) :
    (choose (p * n + r) (p * k + s)) % p = (choose n k * choose r s) % p := by
  -- Vandermonde: choose (p*n + r) (p*k+s) = Σ_{j} choose (p*n) j · choose r (p*k+s-j)
  rw [← vandermonde_sum (p * n) r (p * k + s)]
  -- split at p*k : sumTo (p*k+s+1) = sumTo (p*k) + sumTo (s+1) (shifted)
  rw [show p * k + s + 1 = p * k + (s + 1) from (Nat.add_assoc (p * k) s 1).symm,
      sumTo_split_at (p * k) (fun j => choose (p * n) j * choose r (p * k + s - j)) (s + 1)]
  -- prefix vanishes mod p
  have hprefix : (sumTo (p * k) (fun j => choose (p * n) j * choose r (p * k + s - j))) % p = 0 := by
    apply sumTo_eq_zero_of_all_zero p (p * k)
      (fun j => choose (p * n) j * choose r (p * k + s - j))
    intro j hj
    exact lucas_prefix_zero hp n k r s hr j hj
  -- suffix term: rewrite p*k+s-(p*k+t) = s-t, then lucas_suffix
  have hsuffix : (sumTo (s + 1)
        (fun t => choose (p * n) (p * k + t) * choose r (p * k + s - (p * k + t)))) % p
      = (choose n k * choose r s) % p := by
    have hcongr : sumTo (s + 1)
          (fun t => choose (p * n) (p * k + t) * choose r (p * k + s - (p * k + t)))
        = sumTo (s + 1)
          (fun t => choose (p * n) (p * k + t) * choose r (s - t)) := by
      apply sumTo_congr (s + 1)
        (fun t => choose (p * n) (p * k + t) * choose r (p * k + s - (p * k + t)))
        (fun t => choose (p * n) (p * k + t) * choose r (s - t))
      intro t _
      show choose (p * n) (p * k + t) * choose r (p * k + s - (p * k + t))
         = choose (p * n) (p * k + t) * choose r (s - t)
      rw [add_sub_add_left (p * k) s t]
    rw [hcongr, lucas_suffix hp n k r s hs, mul_mod_left_pure (choose (p * n) (p * k)) (choose r s) p,
        choose_pn_pk hp n k, ← mul_mod_left_pure (choose n k) (choose r s) p]
  rw [add_mod_gen (sumTo (p * k) (fun j => choose (p * n) j * choose r (p * k + s - j)))
        (sumTo (s + 1) (fun t => choose (p * n) (p * k + t) * choose r (p * k + s - (p * k + t)))) p,
      hprefix, Nat.zero_add, mod_mod, hsuffix]

/-- ★★★ **Lucas' theorem, recursive (division) form** — for arbitrary `m, n` (no pre-split into
    digits): `choose m n ≡ choose (m / p) (n / p) · choose (m % p) (n % p)  (mod p)`.  The digit-step
    `lucas_step` applied to the base-`p` decomposition `m = p·(m/p) + m%p`, `n = p·(n/p) + n%p`
    (`div_add_mod_pure`); the low digits `m % p`, `n % p` are `< p` (`Nat.mod_lt`).  Iterating this
    down the quotients gives the full digit-product `choose m n ≡ ∏ᵢ choose mᵢ nᵢ`.  ∅-axiom. -/
theorem lucas_div {p : Nat} (hp : Prime213 p) (m n : Nat) :
    (choose m n) % p = (choose (m / p) (n / p) * choose (m % p) (n % p)) % p := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have key := lucas_step hp (m / p) (n / p) (m % p) (n % p) (Nat.mod_lt m hp0) (Nat.mod_lt n hp0)
  rwa [div_add_mod_pure m p, div_add_mod_pure n p] at key

/-! ## Smoke tests against the concrete `LucasTheorem.lucasStep` table -/

open E213.Lib.Math.NumberTheory.ModArith.LucasTheorem (prime5 prime7)

/-- p=5, n=2,k=1,r=3,s=2: choose 13 7 ≡ choose 2 1 · choose 3 2 (mod 5), via `lucas_step`. -/
theorem lucas_step_5_smoke :
    (choose (5 * 2 + 3) (5 * 1 + 2)) % 5 = (choose 2 1 * choose 3 2) % 5 :=
  lucas_step prime5 2 1 3 2 (by decide) (by decide)

/-- p=7, n=2,k=1,r=4,s=3: choose 18 10 ≡ choose 2 1 · choose 4 3 (mod 7), via `lucas_step`. -/
theorem lucas_step_7_smoke :
    (choose (7 * 2 + 4) (7 * 1 + 3)) % 7 = (choose 2 1 * choose 4 3) % 7 :=
  lucas_step prime7 2 1 4 3 (by decide) (by decide)

end E213.Lib.Math.Combinatorics.LucasStepGeneral
