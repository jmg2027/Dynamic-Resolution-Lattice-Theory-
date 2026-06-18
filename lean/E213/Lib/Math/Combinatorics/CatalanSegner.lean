import E213.Meta.Nat.Convolution213
import E213.Lib.Math.Combinatorics.ConvolutionBinomial

/-!
# CatalanSegner — Catalan numbers as the convolution self-square (Segner's recurrence)

The Catalan numbers are the unique sequence with `C 0 = 1` and the **Segner / Euler
triangulation recurrence** `C(n+1) = Σ_{i=0}^{n} C(i)·C(n−i)` — i.e. `C = 1 + x·C²` in the
generating-function ring: Catalan is the **conv self-square fixed point**, the one
combinatorial sequence whose defining recurrence is *quadratic in itself*.

A fuel-indexed definition (mirroring the corpus's Motzkin/Bell/Schröder pattern) gives the
recurrence for **all** `n` (the existing `Catalan.lean` has only the table `n ≤ 7`):

> ★★★ `catSeg_succ` : `catSeg (n+1) = conv catSeg catSeg n`,

stated through the abstract cut-product `conv` (via the `natSplits ↔ sumTo` bridge), welding
Catalan into the convolution-ring vein as its defining nonlinearity.

All zero-axiom.
-/

namespace E213.Lib.Math.Combinatorics.CatalanSegner

open E213.Meta.Nat.Convolution213 (conv)
open E213.Lib.Math.Combinatorics.ConvolutionBinomial (sumMap_natSplits_eq_sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr)

/-- Fuel-indexed Catalan via the Segner self-convolution recurrence. -/
def catSegF : Nat → Nat → Nat
  | 0,     _     => 1
  | _ + 1, 0     => 1
  | f + 1, n + 1 => sumTo (n + 1) (fun i => catSegF f i * catSegF f (n - i))

/-- The Catalan number `C(n)` (fuel = index). -/
def catSeg (n : Nat) : Nat := catSegF n n

/-- Fuel-independence: `catSegF f n` is the same for every `f ≥ n`. -/
theorem catSegF_eq : ∀ n f g, n ≤ f → n ≤ g → catSegF f n = catSegF g n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f g hf hg
    match n, f, g, hf, hg with
    | 0,     f,     g,     _,  _  => cases f <;> cases g <;> rfl
    | n + 1, f + 1, g + 1, hf, hg =>
      show sumTo (n + 1) (fun i => catSegF f i * catSegF f (n - i))
         = sumTo (n + 1) (fun i => catSegF g i * catSegF g (n - i))
      have hnf : n ≤ f := Nat.le_of_succ_le_succ hf
      have hng : n ≤ g := Nat.le_of_succ_le_succ hg
      refine sumTo_congr (n + 1) _ _ ?_
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ hi
      have hni : n - i ≤ n := Nat.sub_le n i
      have h1 : catSegF f i = catSegF g i :=
        ih i hi f g (Nat.le_trans hin hnf) (Nat.le_trans hin hng)
      have h2 : catSegF f (n - i) = catSegF g (n - i) :=
        ih (n - i) (Nat.lt_succ_of_le hni) f g (Nat.le_trans hni hnf) (Nat.le_trans hni hng)
      rw [h1, h2]

/-- `catSegF f n = catSeg n` whenever `fuel ≥ n`. -/
theorem catSegF_eq_catSeg (f n : Nat) (h : n ≤ f) : catSegF f n = catSeg n :=
  catSegF_eq n f n h (Nat.le_refl n)

/-- The Segner recurrence in `sumTo` form: `C(n+1) = Σ_{i≤n} C(i)·C(n−i)`. -/
theorem catSeg_succ_sumTo (n : Nat) :
    catSeg (n + 1) = sumTo (n + 1) (fun i => catSeg i * catSeg (n - i)) := by
  show sumTo (n + 1) (fun i => catSegF n i * catSegF n (n - i))
      = sumTo (n + 1) (fun i => catSeg i * catSeg (n - i))
  refine sumTo_congr (n + 1) _ _ ?_
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ hi
  have hni : n - i ≤ n := Nat.sub_le n i
  rw [catSegF_eq_catSeg n i hin, catSegF_eq_catSeg n (n - i) hni]

/-- ★★★ **Catalan is the convolution self-square**: `catSeg (n+1) = conv catSeg catSeg n`
    (`C = 1 + x·C²`).  The Segner recurrence through the abstract cut-product `conv`, via the
    `natSplits ↔ sumTo` bridge — Catalan welded into the convolution ring as its defining
    quadratic nonlinearity. -/
theorem catSeg_succ (n : Nat) : catSeg (n + 1) = conv catSeg catSeg n := by
  rw [catSeg_succ_sumTo]
  exact (sumMap_natSplits_eq_sumTo (fun i j => catSeg i * catSeg j) n).symm

/-- Smoke: `catSeg` reproduces the Catalan numbers `1,1,2,5,14,42`. -/
theorem catSeg_smoke :
    catSeg 0 = 1 ∧ catSeg 1 = 1 ∧ catSeg 2 = 2 ∧ catSeg 3 = 5 ∧ catSeg 4 = 14 := by decide

end E213.Lib.Math.Combinatorics.CatalanSegner
