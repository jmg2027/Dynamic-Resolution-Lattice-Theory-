import E213.Meta.Nat.Convolution213
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Vandermonde

/-!
# ConvolutionBinomial — the cut-product computes the binomial corpus

The abstract Cauchy product `conv` (split-then-reglue over `natSplits`) is welded to the
named combinatorial sequences, via the reindexing **bridge** between the cut-enumeration
`natSplits k = {(0,k),(1,k−1),…,(k,0)}` and the range-sum `sumTo (k+1)`:

> `sumMap_natSplits_eq_sumTo` : `Σ_{(i,j)∈natSplits k} F i j = Σ_{j≤k} F j (k−j)`.

Payoff — **Vandermonde's identity as a `conv`-product**:

> ★★ `conv_brow` : `conv (brow a) (brow b) k = C(a+b, k)`,

i.e. `(1+x)^a · (1+x)^b = (1+x)^{a+b}` computed by split-then-reglue equals the existing
`vandermonde`.  The first time the abstract comultiplication product computes a named
combinatorial sequence, retiring the "two disjoint summation engines" gap.

All zero-axiom.
-/

namespace E213.Lib.Math.Combinatorics.ConvolutionBinomial

open E213.Meta.Nat.Convolution213 (conv natSplits sumMap sumMap_map delta conv_congr_left conv_comm conv_delta_left conv_delta_right)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Vandermonde (vand vandermonde)

/-! ## §1 — sumTo front-peel and congruence -/

/-- `sumTo` peeled from the **front**: `Σ_{j<m+1} g j = g 0 + Σ_{j<m} g (j+1)`. -/
theorem sumTo_front (g : Nat → Nat) : ∀ m, sumTo (m + 1) g = g 0 + sumTo m (fun j => g (j + 1))
  | 0     => by
      show (0 : Nat) + g 0 = g 0 + 0
      rw [Nat.zero_add, Nat.add_zero]
  | m + 1 => by
      show sumTo (m + 1 + 1) g = g 0 + sumTo (m + 1) (fun j => g (j + 1))
      rw [show sumTo (m + 1 + 1) g = sumTo (m + 1) g + g (m + 1) from rfl,
          sumTo_front g m,
          show sumTo (m + 1) (fun j => g (j + 1))
              = sumTo m (fun j => g (j + 1)) + g (m + 1) from rfl,
          Nat.add_assoc]

/-- `sumTo` respects pointwise equality of the summand. -/
theorem sumTo_congr {g1 g2 : Nat → Nat} (h : ∀ j, g1 j = g2 j) :
    ∀ m, sumTo m g1 = sumTo m g2
  | 0     => rfl
  | m + 1 => by
      show sumTo m g1 + g1 m = sumTo m g2 + g2 m
      rw [sumTo_congr h m, h m]

/-! ## §2 — the cut/range reindexing bridge -/

/-- ★★ **The cut-enumeration is the range-sum.**  `Σ_{(i,j)∈natSplits k} F i j = Σ_{j≤k} F j
    (k−j)` — the comultiplication cuts `(0,k),(1,k−1),…,(k,0)` summed in order are the
    range sum over `j`. -/
theorem sumMap_natSplits_eq_sumTo : ∀ (F : Nat → Nat → Nat) (k : Nat),
    sumMap (fun p => F p.1 p.2) (natSplits k) = sumTo (k + 1) (fun j => F j (k - j))
  | F, 0     => by
      show F 0 0 + 0 = 0 + F 0 0
      rw [Nat.add_zero, Nat.zero_add]
  | F, k + 1 => by
      show F 0 (k + 1)
          + sumMap (fun p => F p.1 p.2) ((natSplits k).map (fun p => (p.1 + 1, p.2)))
        = sumTo (k + 1 + 1) (fun j => F j (k + 1 - j))
      rw [sumMap_map]
      show F 0 (k + 1) + sumMap (fun p => F (p.1 + 1) p.2) (natSplits k)
        = sumTo (k + 1 + 1) (fun j => F j (k + 1 - j))
      rw [show sumMap (fun p => F (p.1 + 1) p.2) (natSplits k)
            = sumTo (k + 1) (fun j => F (j + 1) (k - j))
          from sumMap_natSplits_eq_sumTo (fun i j => F (i + 1) j) k,
          sumTo_front (fun j => F j (k + 1 - j)) (k + 1)]
      show F 0 (k + 1) + sumTo (k + 1) (fun j => F (j + 1) (k - j))
        = F 0 (k + 1) + sumTo (k + 1) (fun j => F (j + 1) (k + 1 - (j + 1)))
      rw [sumTo_congr (g1 := fun j => F (j + 1) (k - j))
            (g2 := fun j => F (j + 1) (k + 1 - (j + 1)))
            (fun j => by
              show F (j + 1) (k - j) = F (j + 1) (k + 1 - (j + 1))
              rw [E213.Tactic.NatHelper.add_sub_add_right]) (k + 1)]

/-! ## §3 — Vandermonde as a convolution product -/

/-- The `m`-th binomial row `k ↦ C(m,k)` (the coefficient sequence of `(1+x)^m`). -/
def brow (m : Nat) : Nat → Nat := fun k => choose m k

/-- ★★ **Vandermonde's identity, as a `conv`-product.**  `conv (brow a) (brow b) k =
    C(a+b, k)` — `(1+x)^a·(1+x)^b = (1+x)^{a+b}` computed by split-then-reglue equals the
    existing `vandermonde`.  The abstract cut-product computes the binomial corpus. -/
theorem conv_brow (a b k : Nat) : conv (brow a) (brow b) k = choose (a + b) k := by
  show sumMap (fun p => choose a p.1 * choose b p.2) (natSplits k) = choose (a + b) k
  rw [show sumMap (fun p => choose a p.1 * choose b p.2) (natSplits k)
        = sumTo (k + 1) (fun j => choose a j * choose b (k - j))
      from sumMap_natSplits_eq_sumTo (fun i j => choose a i * choose b j) k]
  exact vandermonde a b k

/-! ## §4 — the binomial theorem: (1+x)^n by iterated split-then-reglue is Pascal -/

/-- `δ` is the `0`-th binomial row: `δ = C(0,·)`. -/
theorem delta_eq_choose0 : ∀ m, delta m = choose 0 m
  | 0     => rfl
  | _ + 1 => rfl

/-- Iterated convolution power: `convPow f 0 = δ`, `convPow f (n+1) = conv (convPow f n) f`. -/
def convPow (f : Nat → Nat) : Nat → (Nat → Nat)
  | 0     => delta
  | n + 1 => conv (convPow f n) f

/-- ★★★ **The binomial theorem as a convolution power.**  `convPow (brow 1) n k = C(n,k)` —
    the `n`-fold cut-product of the `(1+x)` row `brow 1 = [1,1,0,…]` is the binomial row
    `C(n,·)`.  `(1+x)^n` computed by repeated split-then-reglue equals Pascal, by induction
    through `conv_brow` (Vandermonde): `conv (brow n)(brow 1) = brow (n+1)`. -/
theorem convPow_brow1 : ∀ (n k : Nat), convPow (brow 1) n k = choose n k
  | 0,     k => delta_eq_choose0 k
  | n + 1, k => by
      show conv (convPow (brow 1) n) (brow 1) k = choose (n + 1) k
      rw [conv_congr_left (f1 := convPow (brow 1) n) (f2 := brow n) (g := brow 1)
            (fun m => convPow_brow1 n m) k,
          conv_brow n 1]

/-- ★★ **The exponential law / monoid homomorphism** `(ℕ,+) → (conv)`:
    `convPow (brow 1) (m+n) = conv (convPow (brow 1) m) (convPow (brow 1) n)` — i.e.
    `(1+x)^{m+n} = (1+x)^m · (1+x)^n` at the cut-product level.  `n ↦ (1+x)^n` is a monoid
    homomorphism from addition to convolution, via `conv_brow` (Vandermonde). -/
theorem convPow_add (m n k : Nat) :
    convPow (brow 1) (m + n) k
      = conv (convPow (brow 1) m) (convPow (brow 1) n) k := by
  rw [convPow_brow1,
      conv_congr_left (f1 := convPow (brow 1) m) (f2 := brow m) (g := convPow (brow 1) n)
        (fun i => convPow_brow1 m i) k,
      conv_comm (brow m) (convPow (brow 1) n),
      conv_congr_left (f1 := convPow (brow 1) n) (f2 := brow n) (g := brow m)
        (fun i => convPow_brow1 n i) k,
      conv_brow n m, Nat.add_comm n m]

/-- ★★ **Generalized binomial power**: `convPow (brow a) n k = C(a·n, k)` — the `n`-fold
    cut-product of the `(1+x)^a` row is the `(a·n)` binomial row, `((1+x)^a)^n = (1+x)^{a·n}`.
    Generalizes `convPow_brow1` (`a=1`); together with `convPow_add` this makes
    `(a,n) ↦ brow(a·n)` respect the bimonoid structure. -/
theorem convPow_brow_gen : ∀ (a n k : Nat), convPow (brow a) n k = choose (a * n) k
  | a, 0,     k => by
      show delta k = choose (a * 0) k
      rw [Nat.mul_zero]; exact delta_eq_choose0 k
  | a, n + 1, k => by
      show conv (convPow (brow a) n) (brow a) k = choose (a * (n + 1)) k
      rw [conv_congr_left (f1 := convPow (brow a) n) (f2 := brow (a * n)) (g := brow a)
            (fun m => convPow_brow_gen a n m) k,
          conv_brow (a * n) a,
          show a * n + a = a * (n + 1) from by rw [Nat.mul_succ]]

/-- `convPow f 1 = f` (the first power is the sequence itself, `δ ∗ f = f`). -/
theorem convPow_one (f : Nat → Nat) (k : Nat) : convPow f 1 k = f k := by
  show conv (convPow f 0) f k = f k
  exact conv_delta_left f k

/-- ★ `convPow δ n = δ`: the unit is idempotent under the convolution power
    (`δ ∗ δ ∗ ⋯ = δ`). -/
theorem convPow_delta : ∀ (n k : Nat), convPow delta n k = delta k
  | 0,     k => rfl
  | n + 1, k => by
      show conv (convPow delta n) delta k = delta k
      rw [conv_congr_left (f1 := convPow delta n) (f2 := delta) (g := delta)
            (fun m => convPow_delta n m) k,
          conv_delta_right delta k]

end E213.Lib.Math.Combinatorics.ConvolutionBinomial
