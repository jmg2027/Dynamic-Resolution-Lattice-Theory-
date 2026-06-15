import E213.Meta.Int213.Core
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.Foundations.CauchySchwarzGeneral

/-!
# Chebyshev sum identity + inequality (general `n`, over `Int`, ∅-axiom)

The bilinear analog of `lagrange_identity` (`CauchySchwarzGeneral.lean`), reusing its
`sumZ` toolkit.

  * ★★ `chebyshev_identity` — doubled form
    `2·[n·Σaᵢbᵢ − (Σaᵢ)(Σbᵢ)] = Σ_{i<n}Σ_{j<n} (aᵢ−aⱼ)(bᵢ−bⱼ)`.
  * ★★★ `chebyshev_sum_ineq` — if every cross term `(aᵢ−aⱼ)(bᵢ−bⱼ) ≥ 0` (e.g. `a,b`
    similarly sorted), then `(Σaᵢ)(Σbᵢ) ≤ n·Σaᵢbᵢ`.

Proof: `chebRow_expand` (inner row, mirroring `rowSq_expand`) summed over the outer
index gives the identity; the inequality follows since `chebDouble ≥ 0`.  Genuinely
absent (only the fixed n=2 `Positivity.chebyshev_sum_2` existed).  All ∅-axiom.
-/

namespace E213.Lib.Math.Foundations.Chebyshev

open E213.Meta.Int213
open E213.Lib.Math.Foundations.CauchySchwarzGeneral

/-- `sumZ n (fun _ => c) = (n : Int) * c`. -/
theorem sumZ_const (n : Nat) (c : Int) :
    sumZ n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => show (0 : Int) = (0 : Int) * c; rw [zero_mul]
  | succ m ih =>
    rw [sumZ_succ, ih]
    have hcast : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by rw [Int.ofNat_succ]
    rw [hcast]
    generalize (m : Int) = M
    ring_intZ

/-- Pointwise cross-product expansion. -/
theorem cheb_cross (am bm aj bj : Int) :
    (am - aj) * (bm - bj)
      = am * bm + aj * bj + (- am) * bj + (- bm) * aj := by
  ring_intZ

/-- Inner row at fixed `m`:
    `Σ_{j<n} (aₘ−aⱼ)(bₘ−bⱼ) = n·aₘbₘ + Σaⱼbⱼ − aₘ·Σbⱼ − bₘ·Σaⱼ`. -/
theorem chebRow_expand (a b : Nat → Int) (n m : Nat) :
    sumZ n (fun j => (a m - a j) * (b m - b j))
      = (n : Int) * (a m * b m) + dot a b n
        + (- a m) * sumZ n (fun j => b j)
        + (- b m) * sumZ n (fun j => a j) := by
  rw [sumZ_congr n
        (fun j => (a m - a j) * (b m - b j))
        (fun j => a m * b m + a j * b j + (- a m) * b j + (- b m) * a j)
        (fun j _ => cheb_cross (a m) (b m) (a j) (b j))]
  rw [← sumZ_add_func n
        (fun j => a m * b m + a j * b j + (- a m) * b j)
        (fun j => (- b m) * a j)]
  rw [← sumZ_add_func n
        (fun j => a m * b m + a j * b j)
        (fun j => (- a m) * b j)]
  rw [← sumZ_add_func n
        (fun j => a m * b m)
        (fun j => a j * b j)]
  rw [← sumZ_mul_left (- a m) n (fun j => b j)]
  rw [← sumZ_mul_left (- b m) n (fun j => a j)]
  rw [sumZ_const n (a m * b m)]
  show (n : Int) * (a m * b m) + sumZ n (fun j => a j * b j)
       + (- a m) * sumZ n (fun j => b j)
       + (- b m) * sumZ n (fun j => a j)
     = (n : Int) * (a m * b m) + dot a b n
       + (- a m) * sumZ n (fun j => b j)
       + (- b m) * sumZ n (fun j => a j)
  rfl

/-- `(- x) * c = (- c) * x`. -/
theorem negmul_comm (x c : Int) : (- x) * c = (- c) * x := by
  generalize x = X
  generalize c = C
  ring_intZ

/-- Full Chebyshev double sum `Σ_{m<n} Σ_{j<n} (aₘ−aⱼ)(bₘ−bⱼ)`. -/
def chebDouble (a b : Nat → Int) (n : Nat) : Int :=
  sumZ n (fun m => sumZ n (fun j => (a m - a j) * (b m - b j)))

/-- ★★ **Chebyshev sum identity** (doubled form, general `n`, over `Int`):
    `2·[n·Σaᵢbᵢ − (Σaᵢ)(Σbᵢ)] = Σ_{i<n}Σ_{j<n} (aᵢ−aⱼ)(bᵢ−bⱼ)`. -/
theorem chebyshev_identity (a b : Nat → Int) (n : Nat) :
    2 * ((n : Int) * dot a b n
          - sumZ n (fun i => a i) * sumZ n (fun i => b i))
      = chebDouble a b n := by
  show 2 * ((n : Int) * dot a b n
              - sumZ n (fun i => a i) * sumZ n (fun i => b i))
     = sumZ n (fun m => sumZ n (fun j => (a m - a j) * (b m - b j)))
  rw [sumZ_congr n
        (fun m => sumZ n (fun j => (a m - a j) * (b m - b j)))
        (fun m => (n : Int) * (a m * b m) + dot a b n
                  + (- a m) * sumZ n (fun j => b j)
                  + (- b m) * sumZ n (fun j => a j))
        (fun m _ => chebRow_expand a b n m)]
  rw [← sumZ_add_func n
        (fun m => (n : Int) * (a m * b m) + dot a b n
                  + (- a m) * sumZ n (fun j => b j))
        (fun m => (- b m) * sumZ n (fun j => a j))]
  rw [← sumZ_add_func n
        (fun m => (n : Int) * (a m * b m) + dot a b n)
        (fun m => (- a m) * sumZ n (fun j => b j))]
  rw [← sumZ_add_func n
        (fun m => (n : Int) * (a m * b m))
        (fun m => dot a b n)]
  rw [sumZ_const n (dot a b n)]
  rw [← sumZ_mul_left (n : Int) n (fun m => a m * b m)]
  rw [sumZ_congr n
        (fun m => (- a m) * sumZ n (fun j => b j))
        (fun m => (- sumZ n (fun j => b j)) * a m)
        (fun m _ => negmul_comm (a m) (sumZ n (fun j => b j)))]
  rw [sumZ_congr n
        (fun m => (- b m) * sumZ n (fun j => a j))
        (fun m => (- sumZ n (fun j => a j)) * b m)
        (fun m _ => negmul_comm (b m) (sumZ n (fun j => a j)))]
  rw [← sumZ_mul_left (- sumZ n (fun j => b j)) n (fun m => a m)]
  rw [← sumZ_mul_left (- sumZ n (fun j => a j)) n (fun m => b m)]
  show 2 * ((n : Int) * dot a b n
              - sumZ n (fun i => a i) * sumZ n (fun i => b i))
     = (n : Int) * sumZ n (fun m => a m * b m) + (n : Int) * dot a b n
       + (- sumZ n (fun j => b j)) * sumZ n (fun m => a m)
       + (- sumZ n (fun j => a j)) * sumZ n (fun m => b m)
  show 2 * ((n : Int) * dot a b n
              - sumZ n (fun i => a i) * sumZ n (fun i => b i))
     = (n : Int) * dot a b n + (n : Int) * dot a b n
       + (- sumZ n (fun i => b i)) * sumZ n (fun i => a i)
       + (- sumZ n (fun i => a i)) * sumZ n (fun i => b i)
  generalize (n : Int) = N
  generalize dot a b n = D
  generalize sumZ n (fun i => a i) = SA
  generalize sumZ n (fun i => b i) = SB
  ring_intZ

/-- `0 ≤ 2·G ⟹ 0 ≤ G` over `Int` (sign trichotomy, no division). -/
theorem nonneg_of_two_nonneg (G : Int) (h : (0 : Int) ≤ 2 * G) : (0 : Int) ≤ G := by
  rcases Order.pos_zero_or_neg G with hpos | hzero | hneg
  · exact Order.le_of_lt hpos
  · rw [hzero]; exact Order.le_refl 0
  · exfalso
    have hsum : G + G < 0 + G := Order.add_lt_add_right hneg G
    have hsum2 : G + G < 0 := by
      have : (0 : Int) + G = G := zero_add G
      rw [this] at hsum
      exact Order.lt_trans hsum hneg
    have htwo : 2 * G = G + G := by generalize G = X; ring_intZ
    rw [htwo] at h
    exact Order.not_le_of_lt hsum2 h

/-- A `sumZ` of pointwise-nonnegative terms is nonnegative. -/
theorem sumZ_nonneg (f : Nat → Int) (h : ∀ k, 0 ≤ f k) :
    ∀ n, 0 ≤ sumZ n f
  | 0 => Order.le_refl 0
  | n + 1 => add_nonneg (sumZ_nonneg f h n) (h n)

/-- `chebDouble ≥ 0` when every cross term `(aᵢ−aⱼ)(bᵢ−bⱼ) ≥ 0`. -/
theorem chebDouble_nonneg (a b : Nat → Int) (n : Nat)
    (h : ∀ i j, (0 : Int) ≤ (a i - a j) * (b i - b j)) :
    (0 : Int) ≤ chebDouble a b n := by
  show 0 ≤ sumZ n (fun m => sumZ n (fun j => (a m - a j) * (b m - b j)))
  exact sumZ_nonneg
    (fun m => sumZ n (fun j => (a m - a j) * (b m - b j)))
    (fun m => sumZ_nonneg (fun j => (a m - a j) * (b m - b j)) (fun j => h m j) n)
    n

/-- ★★★ **Chebyshev's sum inequality** (general `n`, over `Int`): if every cross term
    `(aᵢ−aⱼ)(bᵢ−bⱼ) ≥ 0` (e.g. `a,b` similarly sorted), then
    `(Σ aᵢ)(Σ bᵢ) ≤ n·Σ aᵢbᵢ`. -/
theorem chebyshev_sum_ineq (a b : Nat → Int) (n : Nat)
    (h : ∀ i j, (0 : Int) ≤ (a i - a j) * (b i - b j)) :
    sumZ n (fun i => a i) * sumZ n (fun i => b i) ≤ (n : Int) * dot a b n := by
  have hdbl : (0 : Int) ≤
      2 * ((n : Int) * dot a b n
            - sumZ n (fun i => a i) * sumZ n (fun i => b i)) := by
    rw [chebyshev_identity a b n]; exact chebDouble_nonneg a b n h
  have hg : (0 : Int) ≤ (n : Int) * dot a b n
                          - sumZ n (fun i => a i) * sumZ n (fun i => b i) :=
    nonneg_of_two_nonneg _ hdbl
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hg)

end E213.Lib.Math.Foundations.Chebyshev
