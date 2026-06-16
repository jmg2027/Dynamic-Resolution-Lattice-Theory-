import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.AddMod213
import E213.Lib.Math.NumberTheory.EulerTotient
import E213.Lib.Math.NumberTheory.GaussTotient
import E213.Lib.Math.NumberTheory.TauParity
import E213.Lib.Math.Combinatorics.LucasStepGeneral

/-!
# Euler totient pairing identities via the totative involution `k ↔ n−k` (∅-axiom)

`totient_even` (φ(n) even for n ≥ 3) + `sum_totatives` (2·Σ totatives = n·φ).
-/

namespace E213.Lib.Math.NumberTheory.TotientPairing

open E213.Tactic.NatHelper (gcd213 sub_add_cancel sub_sub_self)
open E213.Meta.Nat.Gcd213 (gcd213_comm gcd213_sub_left gcd213_self)

/-! ## §1 — gcd reflection: `gcd213 (n − j) n = gcd213 j n` for `j ≤ n`. -/

/-- **gcd reflection**: `gcd213 (n − j) n = gcd213 j n` for `j ≤ n`.
    Both sides reduce to `gcd213 (n − j) j` via `gcd213_comm` + `gcd213_sub_left`. -/
theorem gcd_reflect (n j : Nat) (h : j ≤ n) : gcd213 (n - j) n = gcd213 j n := by
  -- LHS: gcd213 (n-j) n = gcd213 n (n-j) = gcd213 (n-(n-j)) (n-j) = gcd213 j (n-j)
  have hnj_le : n - j ≤ n := Nat.sub_le n j
  have hL : gcd213 (n - j) n = gcd213 j (n - j) := by
    rw [gcd213_comm (n - j) n, gcd213_sub_left n (n - j) hnj_le, sub_sub_self h]
  -- RHS: gcd213 j n = gcd213 n j = gcd213 (n-j) j = gcd213 j (n-j)
  have hR : gcd213 j n = gcd213 j (n - j) := by
    rw [gcd213_comm j n, gcd213_sub_left n j h, gcd213_comm (n - j) j]
  rw [hL, hR]

/-! ## §2 — the symmetric totative-pairing weight -/

open E213.Lib.Math.NumberTheory.EulerTotient (totient coprimeInd)
open E213.Lib.Math.NumberTheory.GaussTotient (eqInd eqInd_self eqInd_ne sum_eqInd_eq_one)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr)
open E213.Lib.Math.NumberTheory.FactorialLcmIdentity (sumTo_const_zero)
open E213.Lib.Math.NumberTheory.DivisorProductReindex (sum_eqInd_weight_eq)
open E213.Lib.Math.NumberTheory.TauParity (doubleSum diagSum doubleSum_parity)

/-- The symmetric totative-pairing weight: `[a,b are totative-indices summing to n]`.
    `W n a b = cop a · cop b · [ (a+1)+(b+1) = n ]`. -/
def pairW (n a b : Nat) : Nat :=
  coprimeInd a n * (coprimeInd b n * eqInd ((a + 1) + (b + 1)) n)

/-- `pairW` is symmetric in `a, b` (commutativity of `+` and `*`). -/
theorem pairW_symm (n a b : Nat) : pairW n a b = pairW n b a := by
  show coprimeInd a n * (coprimeInd b n * eqInd ((a + 1) + (b + 1)) n)
     = coprimeInd b n * (coprimeInd a n * eqInd ((b + 1) + (a + 1)) n)
  rw [Nat.add_comm (b + 1) (a + 1)]
  -- mul rearrange (PURE; core `Nat.mul_assoc` leaks propext, use `PureNat.mul_assoc`)
  rw [← E213.Meta.Nat.PureNat.mul_assoc (coprimeInd a n) (coprimeInd b n)
        (eqInd ((a + 1) + (b + 1)) n),
      ← E213.Meta.Nat.PureNat.mul_assoc (coprimeInd b n) (coprimeInd a n)
        (eqInd ((a + 1) + (b + 1)) n),
      Nat.mul_comm (coprimeInd a n) (coprimeInd b n)]

/-! ## §3 — coprimeInd value facts -/

open E213.Meta.Nat.Beq213 (nat_beq_op_eq_false_of_ne)

/-- `coprimeInd a n = 1` when `gcd213 (a+1) n = 1`. -/
theorem coprimeInd_one_of {a n : Nat} (h : gcd213 (a + 1) n = 1) :
    coprimeInd a n = 1 := by
  show (gcd213 (a + 1) n == 1).toNat = 1
  rw [h, show ((1 : Nat) == 1) = true from decide_eq_true rfl]; rfl

/-- `coprimeInd a n = 0` when `gcd213 (a+1) n ≠ 1`. -/
theorem coprimeInd_zero_of {a n : Nat} (h : gcd213 (a + 1) n ≠ 1) :
    coprimeInd a n = 0 := by
  show (gcd213 (a + 1) n == 1).toNat = 0
  rw [nat_beq_op_eq_false_of_ne h]; rfl

/-- `coprimeInd a n` is `0`, or it is `1` with `gcd213 (a+1) n = 1`. -/
theorem coprimeInd_cases (a n : Nat) :
    coprimeInd a n = 0 ∨ (coprimeInd a n = 1 ∧ gcd213 (a + 1) n = 1) := by
  cases Nat.decEq (gcd213 (a + 1) n) 1 with
  | isTrue h => exact Or.inr ⟨coprimeInd_one_of h, h⟩
  | isFalse h => exact Or.inl (coprimeInd_zero_of h)

/-- A totative-index `a < n` with `gcd213 (a+1) n = 1` and `2 ≤ n` has `a + 1 < n`:
    `a + 1 = n` would force `gcd = gcd n n = n ≥ 2 ≠ 1`. -/
theorem totative_lt {a n : Nat} (hn : 2 ≤ n) (han : a < n) (h : gcd213 (a + 1) n = 1) :
    a + 1 < n := by
  rcases Nat.lt_or_ge (a + 1) n with hlt | hge
  · exact hlt
  · exfalso
    have heq : a + 1 = n := Nat.le_antisymm han hge
    rw [heq, gcd213_self n] at h
    exact absurd (h ▸ hn) (by decide)

/-! ## §4 — inner-row collapse: `Σ_b pairW n a b = coprimeInd a n` -/

/-- **Inner-row collapse**: each `a`-row of the pairing grid sums to `coprimeInd a n`.
    For a totative-index `a` (`cop a = 1`) the unique partner `b₀ = n − (a+2)` satisfies
    `(a+1)+(b₀+1) = n` and (by `gcd_reflect`) `cop b₀ = 1`; all other `b` contribute `0`. -/
theorem inner_collapse (n a : Nat) (hn : 2 ≤ n) (han : a < n) :
    sumTo n (fun b => pairW n a b) = coprimeInd a n := by
  cases coprimeInd_cases a n with
  | inl h0 =>
    -- cop a = 0 → every term is 0
    rw [sumTo_congr n (fun b => pairW n a b) (fun _ => 0) (fun b _ => ?_)]
    · rw [sumTo_const_zero n]; exact h0.symm
    · show coprimeInd a n * (coprimeInd b n * eqInd ((a + 1) + (b + 1)) n) = 0
      rw [h0, Nat.zero_mul]
  | inr h1 =>
    obtain ⟨hcop1, hgcd⟩ := h1
    have ha2 : a + 2 ≤ n := totative_lt hn han hgcd
    -- partner index
    let b₀ := n - (a + 2)
    have hb₀sum : b₀ + (a + 2) = n := sub_add_cancel ha2
    have hb₀n : b₀ < n := by
      have h2 : 0 < a + 2 := Nat.succ_pos (a + 1)
      have hlt : b₀ < b₀ + (a + 2) := Nat.lt_add_of_pos_right h2
      rw [hb₀sum] at hlt; exact hlt
    -- (a+1)+(b₀+1) = n
    have hpair : (a + 1) + (b₀ + 1) = n := by
      calc (a + 1) + (b₀ + 1) = b₀ + (a + 2) := by
            rw [Nat.add_comm (a + 1) (b₀ + 1)]
            rw [Nat.add_assoc b₀ 1 (a + 1)]
            show b₀ + (1 + (a + 1)) = b₀ + (a + 2)
            rw [Nat.add_comm 1 (a + 1)]
        _ = n := hb₀sum
    -- b₀ + 1 = n - (a+1)
    have hb₀1 : b₀ + 1 = n - (a + 1) := by
      have ha1le : a + 1 ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ha2)
      -- n - (a+1) + (a+1) = n  and  b₀+1 + (a+1) = n
      have e1 : (b₀ + 1) + (a + 1) = n := by
        rw [Nat.add_comm (a + 1) (b₀ + 1)] at hpair; exact hpair
      have e2 : (n - (a + 1)) + (a + 1) = n := sub_add_cancel ha1le
      have e3 : (b₀ + 1) + (a + 1) = (n - (a + 1)) + (a + 1) := e1.trans e2.symm
      exact E213.Tactic.NatHelper.add_right_cancel e3
    -- cop b₀ = 1 via gcd_reflect
    have hcopb₀ : coprimeInd b₀ n = 1 := by
      apply coprimeInd_one_of
      rw [hb₀1]
      exact gcd_reflect n (a + 1)
        (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ha2)) |>.trans hgcd
    -- factor cop a = 1; pointwise: cop b * [a+b+2=n] = eqInd b₀ b * 1
    rw [hcop1, sumTo_congr n (fun b => pairW n a b)
        (fun b => eqInd b₀ b * 1) (fun b hb => ?_)]
    · exact sum_eqInd_weight_eq n b₀ 1 hb₀n
    · show coprimeInd a n * (coprimeInd b n * eqInd ((a + 1) + (b + 1)) n) = eqInd b₀ b * 1
      rw [hcop1, Nat.one_mul, Nat.mul_one]
      by_cases hbb : b = b₀
      · subst hbb
        rw [hpair, eqInd_self, hcopb₀, Nat.mul_one, eqInd_self]
      · -- b ≠ b₀ → (a+1)+(b+1) ≠ n  and  eqInd b₀ b = 0
        have hne : (a + 1) + (b + 1) ≠ n := by
          intro he
          -- (a+1)+(b+1) = n = (a+1)+(b₀+1) → b+1 = b₀+1 → b = b₀
          have heq : (a + 1) + (b + 1) = (a + 1) + (b₀ + 1) := he.trans hpair.symm
          have hbb1 : b + 1 = b₀ + 1 := E213.Meta.Nat.Gcd213.add_left_cancel_213 (a + 1) heq
          exact hbb (Nat.succ.inj hbb1)
        rw [eqInd_ne hne, Nat.mul_zero, eqInd_ne (fun he => hbb he.symm)]

/-! ## §5 — `totient n = doubleSum n (pairW n)`; the diagonal vanishes for n ≥ 3 -/

open E213.Meta.Nat.Gcd213 (gcd213_dvd_right)

/-- ★ **totient as the symmetric pairing double sum**: `totient n = doubleSum n (pairW n)`
    for `2 ≤ n` — each row collapses to `coprimeInd a n` (`inner_collapse`). -/
theorem totient_eq_doubleSum {n : Nat} (hn : 2 ≤ n) :
    totient n = doubleSum n (pairW n) := by
  show sumTo n (fun a => coprimeInd a n)
     = sumTo n (fun a => sumTo n (fun b => pairW n a b))
  exact (sumTo_congr n _ _ (fun a ha => (inner_collapse n a hn ha).symm))

/-- **The diagonal vanishes for `n ≥ 3`**: a self-paired totative index `a`
    (`2(a+1) = n`) forces `(a+1) ∣ n`, so `gcd213 (a+1) n = a+1 = 1`, i.e. `n = 2`. -/
theorem diag_zero {n : Nat} (hn : 3 ≤ n) :
    diagSum n (pairW n) = 0 := by
  show sumTo n (fun a => pairW n a a) = 0
  rw [sumTo_congr n (fun a => pairW n a a) (fun _ => 0) (fun a _ => ?_)]
  · exact sumTo_const_zero n
  · show coprimeInd a n * (coprimeInd a n * eqInd ((a + 1) + (a + 1)) n) = 0
    cases coprimeInd_cases a n with
    | inl h0 => rw [h0, Nat.zero_mul]
    | inr h1 =>
      obtain ⟨hcop1, hgcd⟩ := h1
      rw [hcop1, Nat.one_mul, Nat.one_mul]
      -- eqInd ((a+1)+(a+1)) n = 0 : else 2(a+1)=n ⟹ (a+1)∣n ⟹ gcd=a+1=1 ⟹ n=2 < 3
      refine eqInd_ne (fun he => ?_)
      -- (a+1) ∣ n
      have hdvd : (a + 1) ∣ n := ⟨2, by rw [Nat.mul_comm]; rw [← he, Nat.two_mul]⟩
      -- gcd213 (a+1) n = a+1
      have hgg : gcd213 (a + 1) n = a + 1 :=
        E213.Meta.Nat.Gcd213.dvd_antisymm_213 (gcd213 (a + 1) n) (a + 1)
          (E213.Meta.Nat.Gcd213.gcd213_dvd_left (a + 1) n)
          (E213.Meta.Nat.Gcd213.gcd213_greatest (a + 1) n (a + 1)
            ⟨1, (Nat.mul_one _).symm⟩ hdvd)
      have ha1 : a + 1 = 1 := by rw [hgg] at hgcd; exact hgcd
      -- then n = 2(a+1) = 2, contradicting 3 ≤ n
      have hn2 : n = 2 := by
        rw [← he, ha1]
      rw [hn2] at hn
      exact absurd hn (by decide)

/-! ## §6 — ★★★ `totient_even`: φ(n) is even for n ≥ 3 -/

/-- ★★★ **Euler totient parity**: `φ(n)` is **even** for `n ≥ 3`.

    Proof (totative involution `k ↔ n−k`): `totient n` equals the symmetric
    pairing double sum `Σ_{a,b<n} cop a · cop b · [(a+1)+(b+1)=n]`
    (`totient_eq_doubleSum`); the weight is symmetric in `a, b`, so by the symmetric
    double-sum parity (`doubleSum_parity`) `φ(n)` is congruent mod 2 to the diagonal
    `Σ_{a<n} cop a · [2(a+1)=n]`.  For `n ≥ 3` a self-paired totative `2(a+1)=n`
    forces `(a+1) ∣ n` hence `gcd(a+1,n)=a+1=1`, i.e. `n=2` — excluded.  So the
    diagonal vanishes and `φ(n)` is even. -/
theorem totient_even {n : Nat} (hn : 3 ≤ n) : totient n % 2 = 0 := by
  have h2 : 2 ≤ n := Nat.le_trans (by decide) hn
  rw [totient_eq_doubleSum h2]
  rw [doubleSum_parity (pairW n) (pairW_symm n) n]
  rw [diag_zero hn]

/-! ## §7 — smokes -/

/-- Smoke: φ is even on `3..12` (closed numerics, axiom-clean). -/
theorem totient_even_smoke :
    totient 3 % 2 = 0 ∧ totient 4 % 2 = 0 ∧ totient 5 % 2 = 0 ∧ totient 6 % 2 = 0 ∧
    totient 7 % 2 = 0 ∧ totient 8 % 2 = 0 ∧ totient 9 % 2 = 0 ∧ totient 10 % 2 = 0 ∧
    totient 11 % 2 = 0 ∧ totient 12 % 2 = 0 := by decide

/-! ## §8 — ★★ `sum_totatives`: `2·Σ totatives = n·φ(n)` -/

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_mul_left sumTo_add_func)
open E213.Lib.Math.Combinatorics.LucasStepGeneral (sumTo_reflect)
open E213.Meta.Nat.NatRing213 (nat_succ_sub)

/-- The totative sum `S = Σ_{k<n} cop k · (k+1)`. -/
def totativeSum (n : Nat) : Nat := sumTo n (fun k => coprimeInd k n * (k + 1))

/-- The last index `k = m` (totative `m+1 = n`) is never coprime to `n = m+1` (`2 ≤ n`). -/
theorem coprimeInd_last_zero {m : Nat} (hge : 2 ≤ m + 1) :
    coprimeInd m (m + 1) = 0 := by
  apply coprimeInd_zero_of
  rw [gcd213_self (m + 1)]
  intro he; exact absurd (he ▸ hge) (by decide)

/-- `totient (m+1) = sumTo m coprimeInd`: the last term vanishes (`2 ≤ m+1`). -/
theorem totient_drop_last {m : Nat} (hge : 2 ≤ m + 1) :
    totient (m + 1) = sumTo m (fun k => coprimeInd k (m + 1)) := by
  show sumTo (m + 1) (fun k => coprimeInd k (m + 1))
     = sumTo m (fun k => coprimeInd k (m + 1))
  rw [sumTo_succ, coprimeInd_last_zero hge, Nat.add_zero]

/-- `totativeSum (m+1) = sumTo m (fun k => cop k · (k+1))`: last term vanishes. -/
theorem totativeSum_drop_last {m : Nat} (hge : 2 ≤ m + 1) :
    totativeSum (m + 1) = sumTo m (fun k => coprimeInd k (m + 1) * (k + 1)) := by
  show sumTo (m + 1) (fun k => coprimeInd k (m + 1) * (k + 1))
     = sumTo m (fun k => coprimeInd k (m + 1) * (k + 1))
  rw [sumTo_succ, coprimeInd_last_zero hge, Nat.zero_mul, Nat.add_zero]

/-- ★★ **Sum of totatives** (doubled, division-free): for `2 ≤ n`,
    `2 · (Σ_{k<n} cop k · (k+1)) = n · φ(n)`.

    Pairing `j ↔ n−j` (`k ↔ n−2−k` on indices): each pair sums to `n`, there are
    `φ(n)/2` pairs.  The doubled sum reindexes (`sumTo_reflect` + `gcd_reflect`)
    to `Σ_k cop k · ((k+1)+(n−1−k)) = Σ_k cop k · n = n · φ(n)`. -/
theorem sum_totatives {n : Nat} (hn : 2 ≤ n) :
    2 * totativeSum n = n * totient n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (sub_add_cancel (Nat.le_trans (by decide) hn)).symm⟩
  have hm1 : 1 ≤ m := Nat.le_of_succ_le_succ hn
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (sub_add_cancel hm1).symm⟩
  -- now n = m' + 1 + 1
  have hge : 2 ≤ m' + 1 + 1 := hn
  -- drop last term in both S and φ
  have hS : totativeSum (m' + 1 + 1)
            = sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1) * (k + 1)) :=
    totativeSum_drop_last hge
  have hφ : totient (m' + 1 + 1)
            = sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1)) :=
    totient_drop_last hge
  -- reflect S over 0..m'
  have hrefl :
      sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1) * (k + 1))
        = sumTo (m' + 1)
            (fun k => coprimeInd (m' - k) (m' + 1 + 1) * ((m' - k) + 1)) :=
    sumTo_reflect (fun k => coprimeInd k (m' + 1 + 1) * (k + 1)) m'
  -- pointwise: reflected term = cop k · ((m'+1) - k)
  have hpt : ∀ k, k < m' + 1 →
      coprimeInd (m' - k) (m' + 1 + 1) * ((m' - k) + 1)
        = coprimeInd k (m' + 1 + 1) * ((m' + 1) - k) := by
    intro k hk
    have hkm' : k ≤ m' := Nat.le_of_lt_succ hk
    have hcop : coprimeInd (m' - k) (m' + 1 + 1) = coprimeInd k (m' + 1 + 1) := by
      have hidx : (m' - k) + 1 = (m' + 1 + 1) - (k + 1) := by
        rw [Nat.succ_sub_succ_eq_sub (m' + 1) k, nat_succ_sub hkm']
      show (gcd213 ((m' - k) + 1) (m' + 1 + 1) == 1).toNat
         = (gcd213 (k + 1) (m' + 1 + 1) == 1).toNat
      rw [hidx, gcd_reflect (m' + 1 + 1) (k + 1)
            (Nat.le_succ_of_le (Nat.succ_le_succ hkm'))]
    have hlen : (m' - k) + 1 = (m' + 1) - k := (nat_succ_sub hkm').symm
    rw [hcop, hlen]
  have hrefl2 :
      sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1) * (k + 1))
        = sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1) * ((m' + 1) - k)) :=
    hrefl.trans (sumTo_congr (m' + 1) _ _ hpt)
  -- 2·S = S + reflected S
  have h2S :
      2 * totativeSum (m' + 1 + 1)
        = sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1) * (k + 1))
          + sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1) * ((m' + 1) - k)) := by
    rw [hS, Nat.two_mul, hrefl2]
  -- combine termwise → Σ cop k · n
  have hcomb :
      sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1) * (k + 1))
        + sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1) * ((m' + 1) - k))
      = sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1) * (m' + 1 + 1)) := by
    rw [sumTo_add_func (m' + 1)
        (fun k => coprimeInd k (m' + 1 + 1) * (k + 1))
        (fun k => coprimeInd k (m' + 1 + 1) * ((m' + 1) - k))]
    refine sumTo_congr (m' + 1) _ _ (fun k hk => ?_)
    have hkm' : k ≤ m' := Nat.le_of_lt_succ hk
    show coprimeInd k (m' + 1 + 1) * (k + 1)
          + coprimeInd k (m' + 1 + 1) * ((m' + 1) - k)
       = coprimeInd k (m' + 1 + 1) * (m' + 1 + 1)
    rw [← Nat.mul_add]
    have hsum : (k + 1) + ((m' + 1) - k) = m' + 1 + 1 := by
      have e1 : k + ((m' + 1) - k) = m' + 1 :=
        (Nat.add_comm k ((m' + 1) - k)).trans (sub_add_cancel (Nat.le_succ_of_le hkm'))
      calc (k + 1) + ((m' + 1) - k)
          = (k + ((m' + 1) - k)) + 1 := by
            rw [Nat.add_right_comm k 1 ((m' + 1) - k)]
        _ = (m' + 1) + 1 := by rw [e1]
    rw [hsum]
  -- Σ cop k · n = n · Σ cop k = n · φ(n)
  have hfact :
      sumTo (m' + 1) (fun k => coprimeInd k (m' + 1 + 1) * (m' + 1 + 1))
        = (m' + 1 + 1) * totient (m' + 1 + 1) := by
    rw [hφ, sumTo_mul_left (m' + 1 + 1) (m' + 1) (fun k => coprimeInd k (m' + 1 + 1))]
    exact sumTo_congr (m' + 1) _ _
      (fun k _ => Nat.mul_comm (coprimeInd k (m' + 1 + 1)) (m' + 1 + 1))
  rw [h2S, hcomb, hfact]

/-- Smoke: `2·Σtotatives = n·φ(n)` on small `n` (closed numerics, axiom-clean).
    e.g. n=5: totatives 1+2+3+4=10, 2·10=20=5·4=5·φ(5). -/
theorem sum_totatives_smoke :
    2 * totativeSum 3 = 3 * totient 3 ∧
    2 * totativeSum 5 = 5 * totient 5 ∧
    2 * totativeSum 6 = 6 * totient 6 ∧
    2 * totativeSum 12 = 12 * totient 12 := by decide

end E213.Lib.Math.NumberTheory.TotientPairing
