import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.Beq213
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.NumberTheory.FactorialLcmIdentity
import E213.Lib.Math.Combinatorics.SumReshape
import E213.Lib.Math.NumberTheory.EulerTotient

/-!
# General Gauss totient divisor-sum `∀ n ≥ 1, Σ_{d∣n} φ(d) = n` (∅-axiom)

★★★ The full general theorem `gauss_totient (n) (hn : 0 < n) : gaussSum n = n`,
i.e. `divisorSum n totient = n` — for ALL n ≥ 1, not just a table.  Closes the
frontier `research-notes/frontiers/gauss_totient_general.md`.  All declarations
PURE.

## Architecture (the standard partition-by-gcd proof, made ∅-axiom)

  1. `count_partition_by_key` — **reusable disjoint-cover cardinality**:
       `Σ_{k<n} 1 = Σ_{v<B} count{k<n : key k = v}` (any `key` with `key k < B`).
       Built from `sumTo_fubini` + `sum_eqInd_eq_one`.  Broadly useful (σ, τ,
       μ-inversion, any multiplicative-function identity).
  2. `gcd_class_count` — **gcd-class count = totient** (bridge, divisor case):
       for `e,d ≥ 1`, `Σ_{k<e·d} [gcd213 (k+1) (e·d) = e] = totient d`.  Via
       `sumTo_reshape` into `d` blocks of size `e`; in each block only the
       multiple-of-`e` position survives, where `gcd213 (e(i+1)) (ed) = e·gcd(i+1,d)`
       (`gcd213_mul_left`) collapses to `[gcd(i+1,d)=1] = coprimeInd i d`.
  3. Partition by `key k = n / gcd213 (k+1) n` (range `[0,n+1)`):
       `class_count_div`/`_nondiv`/`_zero` evaluate each class to `totient d`
       (d∣n) / 0, giving `class_eq_divterm`: `C(j+1) = dvdInd j n · totient(j+1)`
       — exactly the `divisorSum` term.
  4. `gauss_totient` — assemble: split off the `d=0` class, term-match the rest.

The `n/gcd` key (vs. keying by `gcd` directly) lands the partition sum on the
`divisorSum` index order with **no separate divisor-reflection reindex**.

Two propext leaks were eliminated en route: `Nat.sub_add_cancel` (avoided via
`e = m+1` form so `e−1 = m` is definitional) and classical `by_cases` on `∣`
(replaced by a decidable `Nat.decEq (n % (j+1)) 0` split).
-/

namespace E213.Lib.Math.NumberTheory.GaussTotient

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr sumTo_add_func)
open E213.Lib.Math.NumberTheory.FactorialLcmIdentity
  (sumTo_const_one sumTo_const_zero sumTo_fubini)
open E213.Lib.Math.Combinatorics.SumReshape (sumTo_reshape)
open E213.Meta.Nat.Beq213 (nat_beq_op_eq_false_of_ne nat_beq_refl')

/-! ## Single-value indicator collapse -/

/-- `eqInd c v = [c = v]` (`Bool.toNat` of `c == v`), propext-free. -/
def eqInd (c v : Nat) : Nat := (c == v).toNat

/-- `[c = c] = 1`. -/
theorem eqInd_self (c : Nat) : eqInd c c = 1 := by
  show (c == c).toNat = 1
  rw [show (c == c) = true from decide_eq_true rfl]; rfl

/-- `c ≠ v → [c = v] = 0`. -/
theorem eqInd_ne {c v : Nat} (h : c ≠ v) : eqInd c v = 0 := by
  show (c == v).toNat = 0
  rw [nat_beq_op_eq_false_of_ne h]; rfl

/-- `Σ_{v<B} [c = v] = 1` when `c < B`: exactly one `v` in range hits `c`. -/
theorem sum_eqInd_eq_one : ∀ (B c : Nat), c < B →
    sumTo B (fun v => eqInd c v) = 1
  | 0, c, h => absurd h (Nat.not_lt_zero c)
  | B + 1, c, h => by
    show sumTo B (fun v => eqInd c v) + eqInd c B = 1
    by_cases hcB : c < B
    · rw [sum_eqInd_eq_one B c hcB, eqInd_ne (Nat.ne_of_lt hcB)]
    · have hceqB : c = B :=
        Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.le_of_not_lt hcB)
      have hzero : sumTo B (fun v => eqInd c v) = 0 := by
        rw [sumTo_congr B (fun v => eqInd c v) (fun _ => 0) (fun v hv => ?_)]
        · exact sumTo_const_zero B
        · refine eqInd_ne (fun he : c = v => ?_)
          exact absurd (hceqB ▸ he : B = v) (Nat.ne_of_gt hv)
      rw [hzero, hceqB, eqInd_self, Nat.zero_add]

/-! ## Partition-by-key (the reusable counting tool) -/

/-- ★ **Partition-by-key** (reusable):
    `Σ_{k<n} 1 = Σ_{v<B} count{k<n : key k = v}`, provided `key k < B` for all
    `k < n` — the disjoint-cover cardinality identity. -/
theorem count_partition_by_key (key : Nat → Nat) (n B : Nat)
    (hb : ∀ k, k < n → key k < B) :
    sumTo n (fun _ => 1)
      = sumTo B (fun v => sumTo n (fun k => eqInd (key k) v)) := by
  rw [sumTo_fubini (fun v k => eqInd (key k) v) B n]
  exact (sumTo_congr n (fun _ => 1) (fun k => sumTo B (fun v => eqInd (key k) v))
    (fun k hk => (sum_eqInd_eq_one B (key k) (hb k hk)).symm))

/-- `n = Σ_{v<B} count{k<n : key k = v}` (count form). -/
theorem count_partition_by_key' (key : Nat → Nat) (n B : Nat)
    (hb : ∀ k, k < n → key k < B) :
    n = sumTo B (fun v => sumTo n (fun k => eqInd (key k) v)) :=
  (sumTo_const_one n).symm.trans (count_partition_by_key key n B hb)

/-! ## Divisibility / mod plumbing for the gcd-class bridge -/

open E213.Meta.Nat.NatDiv213 (mul_mod_self_pure add_mod_right_pos mul_div_cancel_left_pure)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_mul_left)
open E213.Tactic.NatHelper (gcd213)

/-- `e ∣ x → x % e = 0`. -/
theorem dvd_mod_zero {e x : Nat} (h : e ∣ x) : x % e = 0 := by
  obtain ⟨c, hc⟩ := h
  rw [hc]; exact mul_mod_self_pure e c

/-- `(s + e * i) % e = s % e`: dropping whole multiples of `e`. -/
theorem add_mul_mod_left_pure (e : Nat) (he : 0 < e) :
    ∀ (s i : Nat), (s + e * i) % e = s % e
  | s, 0 => by rw [Nat.mul_zero, Nat.add_zero]
  | s, i + 1 => by
    rw [Nat.mul_succ, ← Nat.add_assoc, add_mod_right_pos he, add_mul_mod_left_pure e he s i]

/-- For `1 ≤ s` and `s < e`, `e ∤ (e * i + s)`. -/
theorem not_dvd_block (e i s : Nat) (he : 0 < e) (hs1 : 0 < s) (hse : s < e) :
    ¬ e ∣ (e * i + s) := by
  intro hd
  have hmod0 : (e * i + s) % e = 0 := dvd_mod_zero hd
  have hcomm : e * i + s = s + e * i := Nat.add_comm _ _
  rw [hcomm, add_mul_mod_left_pure e he s i, Nat.mod_eq_of_lt hse] at hmod0
  exact absurd hmod0 (Nat.ne_of_gt hs1)

/-- In a size-`e` block at offset `i`, a non-final position `r < e−1` contributes
    `0` to the gcd-class count for value `e` (`e ∤ j`, so `gcd j (e·d) ≠ e`). -/
theorem block_mid_zero (e d i r : Nat) (he : 0 < e) (hr : r + 1 < e) :
    eqInd (gcd213 (e * i + r + 1) (e * d)) e = 0 := by
  refine eqInd_ne (fun heq => ?_)
  have hdvd : gcd213 (e * i + (r + 1)) (e * d) ∣ (e * i + (r + 1)) :=
    gcd213_dvd_left _ _
  have hj : e * i + r + 1 = e * i + (r + 1) := Nat.add_assoc _ r 1
  rw [hj] at heq
  obtain ⟨w, hw⟩ := hdvd
  have he_dvd : e ∣ (e * i + (r + 1)) := ⟨w, by rw [hw, heq]⟩
  exact not_dvd_block e i (r + 1) he (Nat.succ_pos r) hr he_dvd

/-- The final position of a block (`e = m+1`) contributes `coprimeInd i d`:
    `j = e·(i+1)`, `gcd(e(i+1)) (ed) = e·gcd(i+1) d`, and `[e·g = e] = [g = 1]`. -/
theorem block_last (m d i : Nat) :
    eqInd (gcd213 ((m + 1) * i + m + 1) ((m + 1) * d)) (m + 1)
      = E213.Lib.Math.NumberTheory.EulerTotient.coprimeInd i d := by
  have he : 0 < m + 1 := Nat.succ_pos m
  have hj : (m + 1) * i + m + 1 = (m + 1) * (i + 1) := by
    rw [Nat.add_assoc, Nat.mul_succ]
  rw [hj, gcd213_mul_left (m + 1) (i + 1) d]
  show eqInd ((m + 1) * gcd213 (i + 1) d) (m + 1)
      = (gcd213 (i + 1) d == 1).toNat
  by_cases hg : gcd213 (i + 1) d = 1
  · rw [hg, Nat.mul_one, eqInd_self]
    rw [show (1 == 1) = true from decide_eq_true rfl]; rfl
  · rw [eqInd_ne (fun he2 : (m + 1) * gcd213 (i + 1) d = m + 1 => ?_),
        nat_beq_op_eq_false_of_ne hg]
    · rfl
    · have : (m + 1) * gcd213 (i + 1) d = (m + 1) * 1 := by rw [Nat.mul_one]; exact he2
      exact hg (Nat.eq_of_mul_eq_mul_left he this)

/-- **Block sum** (`e = m+1`): a full size-`e` block contributes `coprimeInd i d`. -/
theorem block_sum_succ (m d i : Nat) :
    sumTo (m + 1) (fun r => eqInd (gcd213 ((m + 1) * i + r + 1) ((m + 1) * d)) (m + 1))
      = E213.Lib.Math.NumberTheory.EulerTotient.coprimeInd i d := by
  have he : 0 < m + 1 := Nat.succ_pos m
  rw [sumTo_succ]
  have hhead :
      sumTo m (fun r => eqInd (gcd213 ((m + 1) * i + r + 1) ((m + 1) * d)) (m + 1)) = 0 := by
    rw [sumTo_congr m
      (fun r => eqInd (gcd213 ((m + 1) * i + r + 1) ((m + 1) * d)) (m + 1)) (fun _ => 0)
      (fun r hr => ?_)]
    · exact sumTo_const_zero m
    · exact block_mid_zero (m + 1) d i r he (Nat.succ_lt_succ hr)
  rw [hhead, Nat.zero_add]
  exact block_last m d i

/-- **Block sum** (general `e ≥ 1`). -/
theorem block_sum (e d i : Nat) (he : 0 < e) :
    sumTo e (fun r => eqInd (gcd213 (e * i + r + 1) (e * d)) e)
      = E213.Lib.Math.NumberTheory.EulerTotient.coprimeInd i d := by
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := match e, he with
    | m + 1, _ => ⟨m, rfl⟩
  exact block_sum_succ m d i

/-- ★★ **gcd-class count = totient** (the bridge, divisor case):
    for `e,d ≥ 1` with `n = e·d`, `count{k<n : gcd213 (k+1) n = e} = totient d`. -/
theorem gcd_class_count (e d : Nat) (he : 0 < e) :
    sumTo (e * d) (fun k => eqInd (gcd213 (k + 1) (e * d)) e)
      = E213.Lib.Math.NumberTheory.EulerTotient.totient d := by
  have hblock : ∀ i,
      sumTo e (fun r => eqInd (gcd213 (i * e + r + 1) (e * d)) e)
        = E213.Lib.Math.NumberTheory.EulerTotient.coprimeInd i d := by
    intro i
    have hcg : sumTo e (fun r => eqInd (gcd213 (i * e + r + 1) (e * d)) e)
             = sumTo e (fun r => eqInd (gcd213 (e * i + r + 1) (e * d)) e) :=
      sumTo_congr e _ _ (fun r _ => by rw [Nat.mul_comm i e])
    exact hcg.trans (block_sum e d i he)
  calc sumTo (e * d) (fun k => eqInd (gcd213 (k + 1) (e * d)) e)
      = sumTo (d * e) (fun k => eqInd (gcd213 (k + 1) (e * d)) e) :=
        congrArg (fun N => sumTo N (fun k => eqInd (gcd213 (k + 1) (e * d)) e))
          (Nat.mul_comm e d)
    _ = sumTo d (fun i => sumTo e (fun r => eqInd (gcd213 (i * e + r + 1) (e * d)) e)) :=
        sumTo_reshape (fun k => eqInd (gcd213 (k + 1) (e * d)) e) e d
    _ = sumTo d (fun i => E213.Lib.Math.NumberTheory.EulerTotient.coprimeInd i d) :=
        sumTo_congr d _ _ (fun i _ => hblock i)
    _ = E213.Lib.Math.NumberTheory.EulerTotient.totient d := rfl

/-! ## Assembly: the gcd-class partition keyed by `n / gcd` -/

open E213.Meta.Nat.NatDiv213 (div_add_mod_pure)
open E213.Meta.Nat.Gcd213 (gcd213_dvd_left gcd213_dvd_right)
open E213.Lib.Math.NumberTheory.EulerTotient (totient coprimeInd divisorSum dvdInd gaussSum)

/-- `g ∣ n → g * (n / g) = n` (the divisor cofactor). -/
theorem mul_div_of_dvd {g n : Nat} (h : g ∣ n) : g * (n / g) = n := by
  have hmod : g * (n / g) + n % g = n := div_add_mod_pure n g
  rw [dvd_mod_zero h, Nat.add_zero] at hmod
  exact hmod

/-- `gcd213 (k+1) n` is positive (it divides `k+1 ≥ 1`). -/
theorem gcd_succ_pos (k n : Nat) : 0 < gcd213 (k + 1) n := by
  rcases Nat.eq_zero_or_pos (gcd213 (k + 1) n) with h0 | hpos
  · exfalso
    obtain ⟨c, hc⟩ := gcd213_dvd_left (k + 1) n
    rw [h0, Nat.zero_mul] at hc
    exact Nat.noConfusion hc
  · exact hpos

/-- **Key reciprocity**: for `g ∣ n`, `n = e·d`, `0 < e`, `0 < d`, `[n/g = d] = [g = e]`. -/
theorem key_convert {g n e d : Nat} (hgdvd : g ∣ n) (hn_ed : n = e * d)
    (hepos : 0 < e) (hd : 0 < d) :
    eqInd (n / g) d = eqInd g e := by
  have hgcof : g * (n / g) = n := mul_div_of_dvd hgdvd
  by_cases hcase : g = e
  · subst hcase
    have hngd : n / g = d := by
      have hstep : g * (n / g) = g * d := hgcof.trans hn_ed
      exact Nat.eq_of_mul_eq_mul_left hepos hstep
    rw [hngd, eqInd_self, eqInd_self]
  · have hne : n / g ≠ d := by
      intro hng
      apply hcase
      have h1 : g * d = n := by rw [← hng]; exact hgcof
      have h2 : g * d = e * d := h1.trans hn_ed
      exact Nat.eq_of_mul_eq_mul_right hd h2
    rw [eqInd_ne hne, eqInd_ne hcase]

/-- **The `n/gcd` key class-count, divisor case** (`d ∣ n`, `0 < n`, `0 < d`):
    `count{k<n : n / gcd213 (k+1) n = d} = totient d`. -/
theorem class_count_div (n d : Nat) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) :
    sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) d) = totient d := by
  obtain ⟨e, he_eq⟩ := hdvd
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · exfalso; rw [h0, Nat.mul_zero] at he_eq
      exact Nat.lt_irrefl 0 (he_eq ▸ hn)
    · exact hpos
  have hn_ed : n = e * d := by rw [he_eq]; exact Nat.mul_comm d e
  have hpt : ∀ k, eqInd (n / gcd213 (k + 1) n) d = eqInd (gcd213 (k + 1) n) e :=
    fun k => key_convert (gcd213_dvd_right (k + 1) n) hn_ed hepos hd
  have hsum : sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) d)
            = sumTo n (fun k => eqInd (gcd213 (k + 1) n) e) :=
    sumTo_congr n _ _ (fun k _ => hpt k)
  rw [hsum, hn_ed]
  exact gcd_class_count e d hepos

/-- **The `n/gcd` key class-count, non-divisor case** (`¬ d ∣ n`): count = 0. -/
theorem class_count_nondiv (n d : Nat) (hnd : ¬ d ∣ n) :
    sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) d) = 0 := by
  rw [sumTo_congr n (fun k => eqInd (n / gcd213 (k + 1) n) d) (fun _ => 0)
    (fun k _ => ?_)]
  · exact sumTo_const_zero n
  · refine eqInd_ne (fun hng => ?_)
    have hgdvd : gcd213 (k + 1) n ∣ n := gcd213_dvd_right (k + 1) n
    have hgcof : gcd213 (k + 1) n * (n / gcd213 (k + 1) n) = n := mul_div_of_dvd hgdvd
    have hgd : gcd213 (k + 1) n * d = n := by rw [← hng]; exact hgcof
    exact hnd ⟨gcd213 (k + 1) n, by rw [Nat.mul_comm]; exact hgd.symm⟩

/-- `n / gcd213 (k+1) n = 0` is impossible for `0 < n` (cofactor ≥ 1). -/
theorem class_count_zero (n : Nat) (hn : 0 < n) :
    sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) 0) = 0 := by
  rw [sumTo_congr n (fun k => eqInd (n / gcd213 (k + 1) n) 0) (fun _ => 0)
    (fun k _ => ?_)]
  · exact sumTo_const_zero n
  · refine eqInd_ne (fun hng => ?_)
    have hgcof : gcd213 (k + 1) n * (n / gcd213 (k + 1) n) = n :=
      mul_div_of_dvd (gcd213_dvd_right (k + 1) n)
    rw [hng, Nat.mul_zero] at hgcof
    exact Nat.lt_irrefl 0 (hgcof ▸ hn)

/-! ## ★★★ The general Gauss totient divisor-sum theorem -/

open E213.Meta.Nat.NatDiv213 (div_le_self_pos)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_split_first)

/-- Termwise: for `j < n` (divisor `d = j+1`),
    `count{k<n : n/gcd(k+1,n) = j+1} = dvdInd j n * totient (j+1)`. -/
theorem class_eq_divterm (n j : Nat) (hn : 0 < n) :
    sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) (j + 1))
      = dvdInd j n * totient (j + 1) := by
  cases hm : Nat.decEq (n % (j + 1)) 0 with
  | isTrue hmod =>
    have hdvd : (j + 1) ∣ n := by
      obtain ⟨x, hx⟩ :=
        (E213.Meta.Nat.NatDiv213.mul_witness_iff_mod_eq_zero (j + 1) n).mpr hmod
      exact ⟨x, hx.symm⟩
    have hC : sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) (j + 1)) = totient (j + 1) :=
      class_count_div n (j + 1) hn (Nat.succ_pos j) hdvd
    have hdi : dvdInd j n = 1 := by
      show (n % (j + 1) == 0).toNat = 1
      rw [hmod, show ((0 : Nat) == 0) = true from decide_eq_true rfl]; rfl
    rw [hC, hdi, Nat.one_mul]
  | isFalse hmod =>
    have hdvd : ¬ (j + 1) ∣ n := by
      intro hd
      obtain ⟨c, hc⟩ := hd
      exact hmod (dvd_mod_zero ⟨c, hc⟩)
    have hC : sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) (j + 1)) = 0 :=
      class_count_nondiv n (j + 1) hdvd
    have hdi : dvdInd j n = 0 := by
      show (n % (j + 1) == 0).toNat = 0
      rw [nat_beq_op_eq_false_of_ne hmod]; rfl
    rw [hC, hdi, Nat.zero_mul]

/-- ★★★ **General Gauss totient divisor-sum**: `Σ_{d∣n} φ(d) = n` for all `n ≥ 1`
    (`gaussSum n = divisorSum n totient = n`). -/
theorem gauss_totient (n : Nat) (hn : 0 < n) : gaussSum n = n := by
  have hkey : ∀ k, k < n → n / gcd213 (k + 1) n < n + 1 := by
    intro k _
    exact Nat.lt_succ_of_le (div_le_self_pos n (gcd213 (k + 1) n) (gcd_succ_pos k n))
  have hpart :
      n = sumTo (n + 1) (fun d => sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) d)) :=
    count_partition_by_key' (fun k => n / gcd213 (k + 1) n) n (n + 1) hkey
  rw [sumTo_split_first n
      (fun d => sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) d))] at hpart
  rw [class_count_zero n hn, Nat.zero_add] at hpart
  have hds : sumTo n (fun j => sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) (j + 1)))
           = divisorSum n totient := by
    show sumTo n (fun j => sumTo n (fun k => eqInd (n / gcd213 (k + 1) n) (j + 1)))
       = sumTo n (fun j => dvdInd j n * totient (j + 1))
    exact sumTo_congr n _ _ (fun j _ => class_eq_divterm n j hn)
  show divisorSum n totient = n
  rw [hds] at hpart
  exact hpart.symm

/-- Sanity: the former table cases now follow from the general theorem. -/
theorem gauss_totient_general_smoke :
    gaussSum 6 = 6 ∧ gaussSum 12 = 12 ∧ gaussSum 24 = 24 :=
  ⟨gauss_totient 6 (by decide), gauss_totient 12 (by decide),
   gauss_totient 24 (by decide)⟩

end E213.Lib.Math.NumberTheory.GaussTotient
