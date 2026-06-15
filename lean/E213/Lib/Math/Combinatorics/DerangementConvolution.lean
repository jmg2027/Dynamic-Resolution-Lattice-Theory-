import E213.Lib.Math.Combinatorics.Derangements
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.NatRing213

/-!
# Derangement–permutation convolution `Σ C(n,k)·D(n−k) = n!` (∅-axiom)

The inclusion–exclusion identity that permutations partition by their fixed-point
set: choosing which `k` points are fixed (`C(n,k)`) times deranging the rest
(`D(n−k)`) sums to all permutations (`n!`).  The cross-cluster companion of the
Fibonacci–binomial and Vandermonde convolutions.

  ★ `derange_convolution : Σ_{k=0}^{n} C(n,k)·D(n−k) = n!`.

Route: reverse the index + binomial symmetry (`sumTo_reverse`, `choose_symm_sum`)
reduce the goal to the symmetric convolution `Σ C(n,k)·D(k)`; this is proven `= n!`
over `Int` by a paired induction on the invariant `(TZ n = n!, BZ n = n·n!)`, where
`BZ n = Σ C(n,k)·D(k+1)`.  The two recurrences
  * `TZ(n+1) = TZ n + BZ n` (Pascal split + reindex, top term vanishes by
    `choose_eq_zero_of_lt`), and
  * `BZ(n+1) = (n+1)·BZ n + TZ(n+1)` (one-term derangement recurrence
    `derange_one_term` `D(k+1)=(k+1)D(k)+(−1)^{k+1}` + the vanishing alternating
    row sum `alt_binom_sum` `Σ(−1)ᵏC(n+1,k)=0` + the absorption `choose_succ_mul`
    `(k+1)C(n+1,k+1)=(n+1)C(n,k)`)
close the induction.  Cast back to `Nat` via `sumTo_cast` + `Int.ofNat.inj`.  All
∅-axiom.  (Note: `ring_intZ` is used only on ≤2-distinct-atom Int steps; the
3-atom `↑k·↑choose·↑derange` reassociations go through explicit PURE algebra
lemmas `split_succ_mul`/`zero_mul_mul`.)
-/

namespace E213.Lib.Math.Combinatorics.DerangementConvolution

open E213.Lib.Math.Combinatorics.Derangements (derange derange_one_term)
open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_succ_succ choose_eq_zero_of_lt
   choose_self choose_symm_sum choose_succ_mul)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_congr)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial
  (sumZ sumZ_zero sumZ_succ alt_binom_sum)
open E213.Meta.Int213.PolyIntM (powInt)

/-! ## Sum reversal (Nat) -/

/-- Reverse a sum over `[0, n]`: `Σ_{k=0}^{n} f k = Σ_{k=0}^{n} f (n − k)`. -/
theorem sumTo_reverse : ∀ (n : Nat) (f : Nat → Nat),
    sumTo (n + 1) f = sumTo (n + 1) (fun k => f (n - k))
  | 0, _ => rfl
  | m + 1, f => by
    have ih := sumTo_reverse m
    rw [sumTo_split_first (m + 1) f]
    rw [sumTo_succ (m + 1) (fun k => f ((m + 1) - k))]
    show f 0 + sumTo (m + 1) (fun k => f (k + 1))
       = sumTo (m + 1) (fun k => f ((m + 1) - k)) + f ((m + 1) - (m + 1))
    rw [Nat.sub_self]
    rw [ih (fun k => f (k + 1))]
    rw [Nat.add_comm (sumTo (m + 1) (fun k => f ((m + 1) - k))) (f 0)]
    have hcong : sumTo (m + 1) (fun k => f ((m - k) + 1))
               = sumTo (m + 1) (fun k => f ((m + 1) - k)) := by
      apply sumTo_congr
      intro k hk
      show f ((m - k) + 1) = f ((m + 1) - k)
      rw [E213.Meta.Nat.NatRing213.nat_succ_sub (Nat.le_of_lt_succ hk)]
    rw [hcong]

/-! ## Int-sum (`sumZ`) helper lemmas -/

/-- Split off the first term of an `Int` sum. -/
theorem sumZ_split_first : ∀ (n : Nat) (f : Nat → Int),
    sumZ (n + 1) f = f 0 + sumZ n (fun k => f (k + 1))
  | 0, f => by
      show (0 : Int) + f 0 = f 0 + 0
      rw [E213.Meta.Int213.zero_add, Int.add_zero]
  | n + 1, f => by
      show sumZ (n + 1) f + f (n + 1)
         = f 0 + (sumZ n (fun k => f (k + 1)) + f (n + 1))
      rw [sumZ_split_first n f, E213.Meta.Int213.add_assoc]

/-- `Int` sum distributes over pointwise add. -/
theorem sumZ_add_func : ∀ (n : Nat) (f g : Nat → Int),
    sumZ n f + sumZ n g = sumZ n (fun k => f k + g k)
  | 0, _, _ => by show (0 : Int) + 0 = 0; rw [Int.add_zero]
  | n + 1, f, g => by
      show (sumZ n f + f n) + (sumZ n g + g n)
         = sumZ n (fun k => f k + g k) + (f n + g n)
      rw [← sumZ_add_func n f g]
      rw [E213.Meta.Int213.add_assoc (sumZ n f) (f n) (sumZ n g + g n)]
      rw [← E213.Meta.Int213.add_assoc (f n) (sumZ n g) (g n)]
      rw [E213.Meta.Int213.add_comm (f n) (sumZ n g)]
      rw [E213.Meta.Int213.add_assoc (sumZ n g) (f n) (g n)]
      rw [← E213.Meta.Int213.add_assoc (sumZ n f) (sumZ n g) (f n + g n)]

/-- Factor a scalar out of an `Int` sum. -/
theorem sumZ_mul_left (a : Int) : ∀ (n : Nat) (f : Nat → Int),
    a * sumZ n f = sumZ n (fun k => a * f k)
  | 0, _ => by show a * 0 = (0 : Int); rw [E213.Meta.Int213.PolyIntM.mul_zeroZ]
  | n + 1, f => by
      show a * (sumZ n f + f n) = sumZ n (fun k => a * f k) + a * f n
      rw [E213.Meta.Int213.mul_add, sumZ_mul_left a n f]

/-- `Int`-sum congruence (no `funext`). -/
theorem sumZ_congr : ∀ (n : Nat) (f g : Nat → Int),
    (∀ k, k < n → f k = g k) → sumZ n f = sumZ n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
      show sumZ n f + f n = sumZ n g + g n
      rw [sumZ_congr n f g (fun k hk => h k (Nat.lt_succ_of_lt hk))]
      rw [h n (Nat.lt_succ_self n)]

/-- Cast bridge: a `Nat`-sum cast to `Int` is the `Int`-sum of the casts. -/
theorem sumTo_cast : ∀ (n : Nat) (f : Nat → Nat),
    ((sumTo n f : Nat) : Int) = sumZ n (fun k => (f k : Int))
  | 0, _ => rfl
  | n + 1, f => by
      show ((sumTo n f + f n : Nat) : Int) = sumZ n (fun k => (f k : Int)) + (f n : Int)
      rw [show ((sumTo n f + f n : Nat) : Int) = ((sumTo n f : Nat) : Int) + (f n : Int)
            from rfl]
      rw [sumTo_cast n f]

/-! ### Abstract `Int` algebra helpers (3-atom, avoid `ring_intZ` atom-limit) -/

/-- `(x+1)·c·d = x·c·d + c·d`. -/
theorem split_succ_mul (x c d : Int) : (x + 1) * c * d = x * c * d + c * d := by
  rw [E213.Meta.Int213.add_mul x 1 c, E213.Meta.Int213.PolyIntM.one_mulZ,
      E213.Meta.Int213.add_mul (x * c) c d]

/-- `0·c·d = 0`. -/
theorem zero_mul_mul (c d : Int) : (0 : Int) * c * d = 0 := by
  rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_mul]

/-! ## The two `Int`-convolutions and their recurrences -/

/-- Symmetric convolution `TZ n = Σ_{k=0}^{n} C(n,k)·D(k)` (in `Int`). -/
def TZ (n : Nat) : Int := sumZ (n + 1) (fun k => (choose n k : Int) * (derange k : Int))

/-- Shifted convolution `BZ n = Σ_{k=0}^{n} C(n,k)·D(k+1)` (in `Int`). -/
def BZ (n : Nat) : Int := sumZ (n + 1) (fun k => (choose n k : Int) * (derange (k + 1) : Int))

/-- `TZ` split off its `k=0` head (which is `D 0 = 1`):
    `TZ n = 1 + Σ_{k<n} C(n,k+1)·D(k+1)`. -/
theorem TZ_split_head (n : Nat) :
    TZ n = 1 + sumZ n (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int)) := by
  show sumZ (n + 1) (fun k => (choose n k : Int) * (derange k : Int)) = _
  rw [sumZ_split_first n (fun k => (choose n k : Int) * (derange k : Int))]
  show (choose n 0 : Int) * (derange 0 : Int)
       + sumZ n (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int)) = _
  rw [choose_zero_right]
  show ((1 : Nat) : Int) * (derange 0 : Int) + _ = (1 : Int) + _
  rw [show ((1 : Nat) : Int) = (1 : Int) from rfl, show (derange 0 : Int) = 1 from rfl,
      E213.Meta.Int213.PolyIntM.one_mulZ]

/-- ★ Recurrence T: `TZ (n+1) = TZ n + BZ n`. -/
theorem TZ_rec (n : Nat) : TZ (n + 1) = TZ n + BZ n := by
  show sumZ (n + 2) (fun k => (choose (n + 1) k : Int) * (derange k : Int)) = TZ n + BZ n
  rw [sumZ_split_first (n + 1) (fun k => (choose (n + 1) k : Int) * (derange k : Int))]
  show (1 : Int)
       + sumZ (n + 1) (fun k => (choose (n + 1) (k + 1) : Int) * (derange (k + 1) : Int))
     = TZ n + BZ n
  rw [sumZ_congr (n + 1)
        (fun k => (choose (n + 1) (k + 1) : Int) * (derange (k + 1) : Int))
        (fun k => (choose n k : Int) * (derange (k + 1) : Int)
                  + (choose n (k + 1) : Int) * (derange (k + 1) : Int))
        (fun k _ => by
          show (choose (n + 1) (k + 1) : Int) * (derange (k + 1) : Int)
             = (choose n k : Int) * (derange (k + 1) : Int)
               + (choose n (k + 1) : Int) * (derange (k + 1) : Int)
          rw [choose_succ_succ n k,
              show ((choose n k + choose n (k + 1) : Nat) : Int)
                 = (choose n k : Int) + (choose n (k + 1) : Int) from rfl,
              E213.Meta.Int213.add_mul])]
  rw [← sumZ_add_func (n + 1)
        (fun k => (choose n k : Int) * (derange (k + 1) : Int))
        (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int))]
  show (1 : Int)
       + (BZ n
          + sumZ (n + 1) (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int)))
     = TZ n + BZ n
  have hdrop : sumZ (n + 1) (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int))
             = sumZ n (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int)) := by
    rw [sumZ_succ n (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int))]
    show sumZ n (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int))
         + (choose n (n + 1) : Int) * (derange (n + 1) : Int)
       = sumZ n (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int))
    rw [choose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]
    show _ + (0 : Int) * _ = _
    rw [E213.Meta.Int213.zero_mul, Int.add_zero]
  rw [hdrop]
  rw [TZ_split_head n]
  rw [E213.Meta.Int213.add_comm (BZ n)
        (sumZ n (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int)))]
  rw [← E213.Meta.Int213.add_assoc (1 : Int)
        (sumZ n (fun k => (choose n (k + 1) : Int) * (derange (k + 1) : Int))) (BZ n)]

/-! ### Recurrence B -/

/-- The one-term derangement recurrence, as a cast-pushed `Int` rewrite of the
    `BZ`-summand: `C(n+1,k)·D(k+1) = (k+1)·C(n+1,k)·D(k) + C(n+1,k)·(−1)^{k+1}`. -/
theorem bz_summand (n k : Nat) :
    (choose (n + 1) k : Int) * (derange (k + 1) : Int)
      = ((k : Int) + 1) * (choose (n + 1) k : Int) * (derange k : Int)
        + (choose (n + 1) k : Int) * powInt (-1) (k + 1) := by
  rw [derange_one_term k]
  ring_intZ

/-- ★ Recurrence B: `BZ (n+1) = ((n:Int)+1)·BZ n + TZ (n+1)`. -/
theorem BZ_rec (n : Nat) :
    BZ (n + 1) = ((n : Int) + 1) * BZ n + TZ (n + 1) := by
  show sumZ (n + 2) (fun k => (choose (n + 1) k : Int) * (derange (k + 1) : Int))
     = ((n : Int) + 1) * BZ n + TZ (n + 1)
  rw [sumZ_congr (n + 2)
        (fun k => (choose (n + 1) k : Int) * (derange (k + 1) : Int))
        (fun k => ((k : Int) + 1) * (choose (n + 1) k : Int) * (derange k : Int)
                  + (choose (n + 1) k : Int) * powInt (-1) (k + 1))
        (fun k _ => bz_summand n k)]
  rw [← sumZ_add_func (n + 2)
        (fun k => ((k : Int) + 1) * (choose (n + 1) k : Int) * (derange k : Int))
        (fun k => (choose (n + 1) k : Int) * powInt (-1) (k + 1))]
  have halt : sumZ (n + 2) (fun k => (choose (n + 1) k : Int) * powInt (-1) (k + 1)) = 0 := by
    have h := alt_binom_sum n
    have hneg : sumZ (n + 2) (fun k => (choose (n + 1) k : Int) * powInt (-1) (k + 1))
              = (-1 : Int) * sumZ (n + 2) (fun k => powInt (-1) k * (choose (n + 1) k : Int)) := by
      rw [sumZ_mul_left (-1 : Int) (n + 2)
            (fun k => powInt (-1) k * (choose (n + 1) k : Int))]
      apply sumZ_congr
      intro k _
      show (choose (n + 1) k : Int) * powInt (-1) (k + 1)
         = (-1 : Int) * (powInt (-1) k * (choose (n + 1) k : Int))
      have hp : powInt (-1 : Int) (k + 1) = powInt (-1) k * (-1) := rfl
      rw [hp]; ring_intZ
    rw [hneg, h, E213.Meta.Int213.PolyIntM.mul_zeroZ]
  rw [halt, Int.add_zero]
  rw [sumZ_congr (n + 2)
        (fun k => ((k : Int) + 1) * (choose (n + 1) k : Int) * (derange k : Int))
        (fun k => (k : Int) * (choose (n + 1) k : Int) * (derange k : Int)
                  + (choose (n + 1) k : Int) * (derange k : Int))
        (fun k _ => split_succ_mul (k : Int) (choose (n + 1) k : Int) (derange k : Int))]
  rw [← sumZ_add_func (n + 2)
        (fun k => (k : Int) * (choose (n + 1) k : Int) * (derange k : Int))
        (fun k => (choose (n + 1) k : Int) * (derange k : Int))]
  show sumZ (n + 2) (fun k => (k : Int) * (choose (n + 1) k : Int) * (derange k : Int))
       + TZ (n + 1)
     = ((n : Int) + 1) * BZ n + TZ (n + 1)
  have hQ : sumZ (n + 2) (fun k => (k : Int) * (choose (n + 1) k : Int) * (derange k : Int))
          = ((n : Int) + 1) * BZ n := by
    rw [sumZ_split_first (n + 1)
          (fun k => (k : Int) * (choose (n + 1) k : Int) * (derange k : Int))]
    show (0 : Int) * (choose (n + 1) 0 : Int) * (derange 0 : Int)
         + sumZ (n + 1)
             (fun k => ((k + 1 : Nat) : Int) * (choose (n + 1) (k + 1) : Int)
                       * (derange (k + 1) : Int))
       = ((n : Int) + 1) * BZ n
    rw [zero_mul_mul (choose (n + 1) 0 : Int) (derange 0 : Int),
        E213.Meta.Int213.zero_add]
    rw [sumZ_congr (n + 1)
          (fun k => ((k + 1 : Nat) : Int) * (choose (n + 1) (k + 1) : Int)
                    * (derange (k + 1) : Int))
          (fun k => ((n : Int) + 1) * ((choose n k : Int) * (derange (k + 1) : Int)))
          (fun k _ => by
            have habs : (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k :=
              choose_succ_mul n k
            have habsZ : ((k + 1 : Nat) : Int) * (choose (n + 1) (k + 1) : Int)
                       = ((n + 1 : Nat) : Int) * (choose n k : Int) := by
              rw [show ((k + 1 : Nat) : Int) * (choose (n + 1) (k + 1) : Int)
                    = (((k + 1) * choose (n + 1) (k + 1) : Nat) : Int) from rfl,
                  habs,
                  show (((n + 1) * choose n k : Nat) : Int)
                    = ((n + 1 : Nat) : Int) * (choose n k : Int) from rfl]
            show ((k + 1 : Nat) : Int) * (choose (n + 1) (k + 1) : Int)
                   * (derange (k + 1) : Int)
               = ((n : Int) + 1) * ((choose n k : Int) * (derange (k + 1) : Int))
            rw [habsZ]
            rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 from rfl]
            rw [E213.Meta.Int213.mul_assoc])]
    rw [← sumZ_mul_left ((n : Int) + 1) (n + 1)
          (fun k => (choose n k : Int) * (derange (k + 1) : Int))]
    rfl
  rw [hQ]

/-! ## The paired induction -/

/-- Paired invariant `TZ n = n!` ∧ `BZ n = n·n!`, by induction on `n`. -/
theorem TZ_BZ_pair : ∀ n : Nat,
    TZ n = (fact n : Int) ∧ BZ n = (n : Int) * (fact n : Int)
  | 0 => by
      refine ⟨?_, ?_⟩
      · show sumZ 1 (fun k => (choose 0 k : Int) * (derange k : Int)) = (fact 0 : Int)
        decide
      · show sumZ 1 (fun k => (choose 0 k : Int) * (derange (k + 1) : Int))
              = (0 : Int) * (fact 0 : Int)
        decide
  | n + 1 => by
      obtain ⟨ihT, ihB⟩ := TZ_BZ_pair n
      have hT : TZ (n + 1) = (fact (n + 1) : Int) := by
        rw [TZ_rec n, ihT, ihB]
        show (fact n : Int) + (n : Int) * (fact n : Int) = (fact (n + 1) : Int)
        rw [show (fact (n + 1) : Int) = ((n : Int) + 1) * (fact n : Int) from by
              show (((n + 1) * fact n : Nat) : Int) = ((n : Int) + 1) * (fact n : Int)
              rw [show (((n + 1) * fact n : Nat) : Int)
                    = ((n + 1 : Nat) : Int) * (fact n : Int) from rfl,
                  show ((n + 1 : Nat) : Int) = (n : Int) + 1 from rfl]]
        ring_intZ
      refine ⟨hT, ?_⟩
      rw [BZ_rec n, ihB, hT]
      show ((n : Int) + 1) * ((n : Int) * (fact n : Int)) + (fact (n + 1) : Int)
         = ((n + 1 : Nat) : Int) * (fact (n + 1) : Int)
      rw [show (fact (n + 1) : Int) = ((n : Int) + 1) * (fact n : Int) from by
            show (((n + 1) * fact n : Nat) : Int) = ((n : Int) + 1) * (fact n : Int)
            rw [show (((n + 1) * fact n : Nat) : Int)
                  = ((n + 1 : Nat) : Int) * (fact n : Int) from rfl,
                show ((n + 1 : Nat) : Int) = (n : Int) + 1 from rfl]]
      rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 from rfl]
      ring_intZ

/-- ★ `TZ n = n!` over `Int`. -/
theorem TZ_eq_fact (n : Nat) : TZ n = (fact n : Int) := (TZ_BZ_pair n).1

/-! ## Transfer to the `Nat` reversed-convolution goal -/

/-- Derangement–permutation convolution sum (the goal's `Nat` form). -/
def dpc (n : Nat) : Nat := sumTo (n + 1) (fun k => choose n k * derange (n - k))

/-- `dpc n = Σ_{k=0}^{n} C(n,k)·D(k)` (reverse the index + binomial symmetry). -/
theorem dpc_eq_symm (n : Nat) :
    dpc n = sumTo (n + 1) (fun k => choose n k * derange k) := by
  show sumTo (n + 1) (fun k => choose n k * derange (n - k)) = _
  rw [sumTo_reverse n (fun k => choose n k * derange (n - k))]
  apply sumTo_congr
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ hk
  show choose n (n - k) * derange (n - (n - k)) = choose n k * derange k
  rw [E213.Tactic.NatHelper.sub_sub_self hkn]
  have hsum : (n - k) + k = n := by
    rw [Nat.add_comm]; exact E213.Tactic.NatHelper.add_sub_of_le hkn
  rw [choose_symm_sum n (n - k) k hsum]

/-- ★★★ **Derangement–permutation convolution**:
    `Σ_{k=0}^{n} C(n,k)·D(n−k) = n!`. -/
theorem derange_convolution (n : Nat) :
    sumTo (n + 1) (fun k => choose n k * derange (n - k)) = fact n := by
  have hcast : ((sumTo (n + 1) (fun k => choose n k * derange k) : Nat) : Int)
             = (fact n : Int) := by
    rw [sumTo_cast (n + 1) (fun k => choose n k * derange k)]
    show sumZ (n + 1) (fun k => ((choose n k * derange k : Nat) : Int)) = (fact n : Int)
    rw [sumZ_congr (n + 1)
          (fun k => ((choose n k * derange k : Nat) : Int))
          (fun k => (choose n k : Int) * (derange k : Int))
          (fun k _ => rfl)]
    exact TZ_eq_fact n
  have hnat : sumTo (n + 1) (fun k => choose n k * derange k) = fact n :=
    Int.ofNat.inj hcast
  show dpc n = fact n
  rw [dpc_eq_symm n]
  exact hnat

/-- Smoke: `Σ_{k=0}^{5} C(5,k)·D(5−k) = 5! = 120`. -/
theorem derange_convolution_smoke :
    sumTo 6 (fun k => choose 5 k * derange (5 - k)) = fact 5 := by decide

end E213.Lib.Math.Combinatorics.DerangementConvolution
