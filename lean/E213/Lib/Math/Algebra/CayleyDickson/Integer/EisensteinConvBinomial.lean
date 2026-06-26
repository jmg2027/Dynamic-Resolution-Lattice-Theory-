import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinBinomial

/-!
# The binomial theorem for convolution in `R[C_p]` (∅-axiom, Phase B2e.2c)

★★★★★ `convPow_add_pow` : the binomial theorem for the convolution power, **coefficient-wise**:

  `(f ⊕ g)^{⋆n}(k) = Σ_{j=0}^{n} binom n j · (f^{⋆j} ⋆ g^{⋆(n−j)})(k)`   for `k < p`,

where `⊕` is pointwise `+` and `⋆` is convolution.  This is the group-ring analog of
`EisensteinBinomial.add_pow` — proven by the same Pascal induction, but with the convolution
machinery in place of the `ℤ[ω]` ring ops: `conv_add_right` (distribute over `f⊕g`), `conv_congr` +
`conv_sumRange_left` (push the inductive binomial sum through the outer convolution),
`convProd_mul_{f,g}` (raise the `⋆`-exponents), and `convOne_{left,right}` (the `e_0` boundary terms).
Equality is coefficient-wise because function equality in `R[C_p]` would need the forbidden
`funext`/`Quot.sound`.

Toward the convolution freshman's dream `(f ⊕ g)^{⋆q} ≡ f^{⋆q} ⊕ g^{⋆q} (mod q)` and the Gauss-sum
Frobenius `g(χ)^{⋆q} ≡ χ̄(q)·g(χ) (mod q)` (Phase B2).  ∅-axiom up to allowed `propext`.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvBinomial

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing
  (conv conv_add_right conv_scalar_left conv_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow
  (delta convPow convPow_zero convPow_succ convOne_left convOne_right conv_sumRange_left
   convProd_mul_f convProd_mul_g)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinBinomial
  (cz cz_zero cz_diag cz_pascal sumRange_succ_bottom)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
  (sumRange sumRange_succ sum_add sum_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (one one_mul)
open E213.Meta.Algebra213.Ring213 (add_assoc add_comm add_mul zero_add)

/-- ★★★★★ **The convolution binomial theorem (coefficient-wise)** —
    `(f ⊕ g)^{⋆n}(k) = Σ_{j=0}^{n} binom n j · (f^{⋆j} ⋆ g^{⋆(n−j)})(k)` for `k < p`.  Pascal induction
    on `n`, with the convolution machinery replacing the `ℤ[ω]` ring ops.  ∅-axiom up to allowed
    `propext`. -/
theorem convPow_add_pow (p : Nat) (f g : Nat → ZOmega) : ∀ (n k : Nat), k < p →
    convPow p (fun i => f i + g i) n k
      = sumRange (fun j => cz n j * conv p (convPow p f j) (convPow p g (n - j)) k) (n + 1)
  | 0, k, hk => by
      show convPow p (fun i => f i + g i) 0 k
         = 0 + cz 0 0 * conv p (convPow p f 0) (convPow p g (0 - 0)) k
      rw [Nat.sub_zero, cz_diag, convPow_zero p f, convPow_zero p g,
          convOne_left p delta hk, one_mul, zero_add, convPow_zero p (fun i => f i + g i)]
  | n + 1, k, hk => by
      have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
      -- S1 := conv (convPow h n) f k,  reduced to a binomial sum (raising the f-exponent)
      have hS1 : conv p (convPow p (fun i => f i + g i) n) f k
          = sumRange
              (fun j => cz n j * conv p (convPow p f (j + 1)) (convPow p g (n - j)) k) (n + 1) := by
        rw [conv_congr p k hp (fun i hi => convPow_add_pow p f g n i hi) (fun _ _ => rfl),
            conv_sumRange_left p
              (fun j i => cz n j * conv p (convPow p f j) (convPow p g (n - j)) i) f k (n + 1)]
        exact sum_congr (n + 1) (fun j _ => by
          rw [conv_scalar_left p (cz n j)
                (fun i => conv p (convPow p f j) (convPow p g (n - j)) i) f k,
              convProd_mul_f p f g j (n - j) hk])
      -- S2 := conv (convPow h n) g k,  raising the g-exponent
      have hS2 : conv p (convPow p (fun i => f i + g i) n) g k
          = sumRange
              (fun j => cz n j * conv p (convPow p f j) (convPow p g ((n - j) + 1)) k) (n + 1) := by
        rw [conv_congr p k hp (fun i hi => convPow_add_pow p f g n i hi) (fun _ _ => rfl),
            conv_sumRange_left p
              (fun j i => cz n j * conv p (convPow p f j) (convPow p g (n - j)) i) g k (n + 1)]
        exact sum_congr (n + 1) (fun j _ => by
          rw [conv_scalar_left p (cz n j)
                (fun i => conv p (convPow p f j) (convPow p g (n - j)) i) g k,
              convProd_mul_g p f g j (n - j) hk])
      -- (f⊕g)^{⋆(n+1)} = S1 + S2
      rw [convPow_succ, conv_add_right p (convPow p (fun i => f i + g i) n) f g k, hS1, hS2,
          sumRange_succ
            (fun j => cz n j * conv p (convPow p f (j + 1)) (convPow p g (n - j)) k) n,
          sumRange_succ_bottom
            (fun j => cz n j * conv p (convPow p f j) (convPow p g ((n - j) + 1)) k) n]
      -- boundary terms of S1 (top, j=n → f^{⋆(n+1)}) and S2 (bottom, j=0 → g^{⋆(n+1)})
      rw [show cz n n * conv p (convPow p f (n + 1)) (convPow p g (n - n)) k
            = convPow p f (n + 1) k by
            rw [Nat.sub_self, cz_diag, convPow_zero, convOne_right p (convPow p f (n + 1)) hk,
                E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality.one_mul],
          show cz n 0 * conv p (convPow p f 0) (convPow p g ((n - 0) + 1)) k
            = convPow p g (n + 1) k by
            rw [Nat.sub_zero, cz_zero, convPow_zero, convOne_left p (convPow p g (n + 1)) hk,
                E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality.one_mul]]
      -- target: peel top (j=n+1 → f^{⋆(n+1)}) and bottom (j=0 → g^{⋆(n+1)})
      rw [sumRange_succ
            (fun j => cz (n + 1) j * conv p (convPow p f j) (convPow p g ((n + 1) - j)) k) (n + 1),
          sumRange_succ_bottom
            (fun j => cz (n + 1) j * conv p (convPow p f j) (convPow p g ((n + 1) - j)) k) n,
          show cz (n + 1) (n + 1)
                 * conv p (convPow p f (n + 1)) (convPow p g ((n + 1) - (n + 1))) k
            = convPow p f (n + 1) k by
            rw [Nat.sub_self, cz_diag, convPow_zero, convOne_right p (convPow p f (n + 1)) hk,
                E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality.one_mul],
          show cz (n + 1) 0 * conv p (convPow p f 0) (convPow p g ((n + 1) - 0)) k
            = convPow p g (n + 1) k by
            rw [Nat.sub_zero, cz_zero, convPow_zero, convOne_left p (convPow p g (n + 1)) hk,
                E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality.one_mul]]
      -- combine the two interior sums via Pascal, matching the target interior
      have hmerge :
          sumRange (fun j => cz n j * conv p (convPow p f (j + 1)) (convPow p g (n - j)) k) n
            + sumRange (fun j => cz n (j + 1)
                * conv p (convPow p f (j + 1)) (convPow p g ((n - (j + 1)) + 1)) k) n
          = sumRange (fun j => cz (n + 1) (j + 1)
                * conv p (convPow p f (j + 1)) (convPow p g ((n + 1) - (j + 1))) k) n := by
        rw [← sum_add (fun j => cz n j * conv p (convPow p f (j + 1)) (convPow p g (n - j)) k)
              (fun j => cz n (j + 1)
                * conv p (convPow p f (j + 1)) (convPow p g ((n - (j + 1)) + 1)) k) n]
        exact sum_congr n (fun j hj => by
          have hbexp : (n - (j + 1)) + 1 = n - j := by
            rw [← Nat.sub_sub, Nat.sub_add_cancel (Nat.sub_pos_of_lt hj)]
          have hbexp2 : (n + 1) - (j + 1) = n - j := Nat.succ_sub_succ n j
          rw [hbexp, hbexp2, ← add_mul, ← cz_pascal n j])
      rw [← hmerge]
      generalize sumRange
        (fun j => cz n j * conv p (convPow p f (j + 1)) (convPow p g (n - j)) k) n = sA
      generalize sumRange (fun j => cz n (j + 1)
        * conv p (convPow p f (j + 1)) (convPow p g ((n - (j + 1)) + 1)) k) n = sB
      generalize convPow p f (n + 1) k = pa
      generalize convPow p g (n + 1) k = pb
      rw [add_assoc sA pa (pb + sB), add_comm pa (pb + sB), ← add_assoc sA (pb + sB) pa,
          ← add_assoc sA pb sB, add_comm sA pb, add_assoc pb sA sB]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvBinomial
