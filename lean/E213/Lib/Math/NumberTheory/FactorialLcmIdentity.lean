import E213.Lib.Math.NumberTheory.Legendre
import E213.Lib.Math.NumberTheory.LcmGrowthChebyshev

/-!
# FactorialLcmIdentity — `vₚ(N!) = Σ_{i=1}^{N} vₚ(lcm(1..⌊N/i⌋))`

The structural bridge between the two homes of `e`: the **factorial**
(`e = Σ 1/k!`, `EulerCut`) and the **lcm** (`lcm(1..N) ~ eᴺ`, the `ψ`-form of
PNT).  The per-prime exponent identity

  `vₚ(N!) = Σ_{i=1}^{N} vₚ(lcm(1..⌊N/i⌋))`

is exactly Legendre's formula read as a **Fubini count** on the lattice
`{(i,j) : i ≥ 1, j ≥ 1, i·pʲ ≤ N}`: summing the lcm-exponents `⌊log_p⌊N/i⌋⌋`
over the divisor-scaled ranges (count by rows) equals `Σⱼ ⌊N/pʲ⌋` (count by
columns).  It is the integer backbone of `ln N! = Σ_{i} ψ(⌊N/i⌋)` — so the
constant `e` is not *approached* by bounds, it is **computed** from the shared
prime-power skeleton: the factorial *is* the product of lcm's over the
divisor-scaled ranges (`N! = Π_{i=1}^{N} lcm(1..⌊N/i⌋)`, the exponent form here).

Self-contained ∅-axiom: a finite `sumTo`-Fubini (`sumTo_fubini`) and the
column-count `Σ_i [c ≤ ⌊N/(i+1)⌋] = ⌊N/c⌋` (`count_div`), assembled against
`legendre` + `vp_lcmUpTo`.  No Mathlib, no `Classical`, no `propext`-tainted
core lemmas (`le_div_iff_mul_le`, `div_le_self_pos`, `le_of_dvd_pos` are the
pure replacements).
-/

namespace E213.Lib.Math.NumberTheory.FactorialLcmIdentity

open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.PureNat (lt_two_pow)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial)
open E213.Lib.Math.NumberTheory.Legendre (legendre)
open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev (lcmUpTo vp_lcmUpTo le_div_iff_mul_le)
open E213.Meta.Nat.NatDiv213 (div_le_self_pos)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ sumTo_zero)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_add_func sumTo_congr)

/-! ## Finite-sum infrastructure -/

/-- `Σ_{k<n} 0 = 0`. -/
theorem sumTo_const_zero : ∀ n, sumTo n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by rw [sumTo_succ, sumTo_const_zero n]

/-- `Σ_{k<n} 1 = n`. -/
theorem sumTo_const_one : ∀ n, sumTo n (fun _ => 1) = n
  | 0 => rfl
  | n + 1 => by rw [sumTo_succ, sumTo_const_one n]

/-- Extend a `sumTo` past its bound when the tail vanishes (`g e = 0` for `e ≥ a`):
    `Σ_{e<a} g = Σ_{e<b} g` for `a ≤ b`.  `g` is a genuine function variable so
    `g k` matches in the step (no beta friction). -/
theorem sumTo_extend_vanish {g : Nat → Nat} {a : Nat} (hvan : ∀ e, a ≤ e → g e = 0) :
    ∀ b, a ≤ b → sumTo a g = sumTo b g := by
  intro b
  induction b with
  | zero => intro hab; rw [Nat.le_antisymm hab (Nat.zero_le _)]
  | succ k ih =>
      intro hab
      rcases Nat.lt_or_ge a (k + 1) with hlt | hge
      · have hak : a ≤ k := Nat.le_of_lt_succ hlt
        rw [sumTo_succ, ← ih hak, hvan k hak, Nat.add_zero]
      · rw [Nat.le_antisymm hab hge]

/-- **Finite Fubini**: `Σ_{i<m} Σ_{j<n} f i j = Σ_{j<n} Σ_{i<m} f i j`.  By
    induction on `m` via `sumTo_add_func` (no `funext`; `sumTo_congr` closes the
    pointwise step). -/
theorem sumTo_fubini (f : Nat → Nat → Nat) : ∀ m n,
    sumTo m (fun i => sumTo n (fun j => f i j))
      = sumTo n (fun j => sumTo m (fun i => f i j))
  | 0, n => by
      rw [sumTo_congr n (fun j => sumTo 0 (fun i => f i j)) (fun _ => 0) (fun _ _ => rfl)]
      exact (sumTo_const_zero n).symm
  | m + 1, n => by
      show sumTo m (fun i => sumTo n (fun j => f i j)) + sumTo n (fun j => f m j)
        = sumTo n (fun j => sumTo (m + 1) (fun i => f i j))
      rw [sumTo_fubini f m n,
          sumTo_add_func n (fun j => sumTo m (fun i => f i j)) (fun j => f m j)]
      exact sumTo_congr n _ _ (fun _ _ => rfl)

/-- **Initial-segment count**: `Σ_{i<N} [i < t] = t` when `t ≤ N`.  Induction on
    `N`; at `N+1`, either `t ≤ N` (last term vanishes, IH) or `t = N+1` (every
    term is `1`, `sumTo_const_one`). -/
theorem count_lt_le : ∀ (N t : Nat), t ≤ N →
    sumTo N (fun i => if i < t then 1 else 0) = t
  | 0, t, ht => by exact (Nat.le_antisymm ht (Nat.zero_le t)).symm
  | N + 1, t, ht => by
      show sumTo N (fun i => if i < t then 1 else 0) + (if N < t then 1 else 0) = t
      rcases Nat.lt_or_ge N t with hNt | hNt
      · -- N < t ≤ N+1 ⟹ t = N+1; every term is 1
        have ht' : t = N + 1 := Nat.le_antisymm ht hNt
        have hall : sumTo N (fun i => if i < t then 1 else 0) = N := by
          rw [sumTo_congr N (fun i => if i < t then 1 else 0) (fun _ => 1)
                (fun i hi => if_pos (Nat.lt_trans hi hNt)), sumTo_const_one N]
        rw [if_pos hNt, hall, ht']
      · -- t ≤ N: last term vanishes
        have hneg : ¬ N < t := fun h => Nat.lt_irrefl N (Nat.lt_of_lt_of_le h hNt)
        rw [if_neg hneg, Nat.add_zero, count_lt_le N t hNt]

/-- **The column count**: `Σ_{i<N} [c ≤ ⌊N/(i+1)⌋] = ⌊N/c⌋` (`c ≥ 1`).  The
    division adjunction `le_div_iff_mul_le` turns `c ≤ ⌊N/(i+1)⌋` into
    `i < ⌊N/c⌋`, then `count_lt_le` (using `⌊N/c⌋ ≤ N`). -/
theorem count_div (N c : Nat) (hc : 1 ≤ c) :
    sumTo N (fun i => if c ≤ N / (i + 1) then 1 else 0) = N / c := by
  rw [← count_lt_le N (N / c) (div_le_self_pos N c hc)]
  refine sumTo_congr N _ _ (fun i _ => ?_)
  have hiff : (c ≤ N / (i + 1)) ↔ (i < N / c) := by
    constructor
    · intro h
      have h1 : (i + 1) * c ≤ N := (le_div_iff_mul_le (Nat.succ_pos i)).mp h
      exact (le_div_iff_mul_le hc).mpr (by rw [Nat.mul_comm]; exact h1)
    · intro h
      have h2 : c * (i + 1) ≤ N := (le_div_iff_mul_le hc).mp h
      exact (le_div_iff_mul_le (Nat.succ_pos i)).mpr (by rw [Nat.mul_comm]; exact h2)
  by_cases hcond : i < N / c
  · rw [if_pos (hiff.mpr hcond), if_pos hcond]
  · rw [if_neg (fun h => hcond (hiff.mp h)), if_neg hcond]

/-! ## The identity -/

/-- **`vₚ(N!) = Σ_{i=1}^{N} vₚ(lcm(1..⌊N/i⌋))`** (`p` prime).  Legendre
    (`vₚ(N!) = Σⱼ ⌊N/pʲ⌋`) and the lcm valuation (`vₚ(lcm(1..M)) = Σ_e [p^{e+1} ≤ M]`,
    `vp_lcmUpTo`) are the row/column counts of the lattice `{(i,e) : (i+1)·p^{e+1} ≤ N}`:
    extend each inner lcm-sum to the common bound `N` (its tail vanishes, `2^{e} > M`
    past `M`), swap (`sumTo_fubini`), and collapse the column with `count_div`.  The
    exponent form of `N! = Π_{i=1}^{N} lcm(1..⌊N/i⌋)` — the factorial and the lcm as
    two readouts of one prime-power skeleton. -/
theorem vp_factorial_eq_sum_vp_lcm {p : Nat} (hp : Prime213 p) (N : Nat) :
    vp p (factorial N) = sumTo N (fun i => vp p (lcmUpTo (N / (i + 1)))) := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  -- RHS: rewrite each lcm valuation and extend its bound to N
  have hRHS : sumTo N (fun i => vp p (lcmUpTo (N / (i + 1))))
      = sumTo N (fun i => sumTo N (fun e => if p ^ (e + 1) ≤ N / (i + 1) then 1 else 0)) := by
    refine sumTo_congr N _ _ (fun i _ => ?_)
    rw [vp_lcmUpTo hp (N / (i + 1))]
    -- extend Σ_{e < N/(i+1)} to Σ_{e < N} (tail vanishes past N/(i+1))
    have hvan : ∀ e, N / (i + 1) ≤ e →
        (if p ^ (e + 1) ≤ N / (i + 1) then 1 else 0) = 0 := by
      intro e he
      refine if_neg (fun hcon => ?_)
      have h1 : N / (i + 1) < 2 ^ e := Nat.lt_of_le_of_lt he (lt_two_pow e)
      have h2 : (2 : Nat) ^ e ≤ p ^ (e + 1) :=
        Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ e))
          (Nat.pow_le_pow_left hp.1 (e + 1))
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 hcon))
    exact sumTo_extend_vanish (g := fun e => if p ^ (e + 1) ≤ N / (i + 1) then 1 else 0)
      hvan N (div_le_self_pos N (i + 1) (Nat.succ_pos i))
  rw [legendre hp N, hRHS,
      sumTo_fubini (fun i e => if p ^ (e + 1) ≤ N / (i + 1) then 1 else 0) N N]
  refine sumTo_congr N _ _ (fun e _ => ?_)
  exact (count_div N (p ^ (e + 1)) (Nat.pos_pow_of_pos (e + 1) hp0)).symm

end E213.Lib.Math.NumberTheory.FactorialLcmIdentity
