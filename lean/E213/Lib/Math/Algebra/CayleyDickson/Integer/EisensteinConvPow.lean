import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality

/-!
# The convolution identity and power in the group ring `R[C_p]` (∅-axiom, Phase B2e)

The substrate for the **group-ring (convolution) Frobenius** `g^{⋆q} ≡ χ̄(q)·g (mod q)`.  The free
group ring `R[C_p]` (`EisensteinGroupRing`) has convolution `⋆` as multiplication; this file adds its
**identity** `delta = e_0` (the basis vector at `0`) and the **convolution power** `convPow p f n`
(the `n`-fold `⋆`-power, `= e_0` at `n=0`).

  `convOne_left`   : `(e_0 ⋆ f)(k) = f k`   for `k < p`  (the left identity law),
  `convPow_succ`   : `f^{⋆(n+1)} = f^{⋆n} ⋆ f`,
  `convPow_one`    : `f^{⋆1}(k) = f k`       for `k < p`.

Toward the convolution binomial theorem `(f ⊕ g)^{⋆n} = ⊕_k C(n,k)·(f^{⋆k} ⋆ g^{⋆(n−k)})` and the
freshman's dream mod `q` (coefficient-wise, since function equality in `R[C_p]` would need the
forbidden `funext`/`Quot.sound`).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv conv_add_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (one one_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
  (sumRange sum_single sum_congr sum_zero_fun)
open E213.Meta.Algebra213.Ring213 (zero_mul)

/-- The convolution identity `e_0 ∈ R[C_p]` — the basis vector at index `0` (`δ_{i,0}`). -/
def delta : Nat → ZOmega := fun i => if i = 0 then one else 0

/-- The `n`-fold convolution power `f^{⋆n}` in `R[C_p]`, `f^{⋆0} = e_0`, `f^{⋆(n+1)} = f^{⋆n} ⋆ f`. -/
def convPow (p : Nat) (f : Nat → ZOmega) : Nat → (Nat → ZOmega)
  | 0     => delta
  | n + 1 => conv p (convPow p f n) f

/-- `f^{⋆0} = e_0`. -/
theorem convPow_zero (p : Nat) (f : Nat → ZOmega) : convPow p f 0 = delta := rfl

/-- `f^{⋆(n+1)} = f^{⋆n} ⋆ f`. -/
theorem convPow_succ (p : Nat) (f : Nat → ZOmega) (n : Nat) :
    convPow p f (n + 1) = conv p (convPow p f n) f := rfl

/-- ★★★★ **The left identity law** — `(e_0 ⋆ f)(k) = f k` for `k < p`.  Only the `i=0` term of the
    convolution survives (`δ_{i,0}`), and `(k + p − 0) % p = k`.  ∅-axiom. -/
theorem convOne_left (p : Nat) (f : Nat → ZOmega) {k : Nat} (hk : k < p) :
    conv p delta f k = f k := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  show sumRange (fun i => delta i * f ((k + p - i) % p)) p = f k
  rw [sum_single p 0 hp (fun i => delta i * f ((k + p - i) % p))
        (fun i _ hi0 => by
          show (if i = 0 then one else 0) * f ((k + p - i) % p) = 0
          rw [if_neg hi0, zero_mul])]
  show (if (0 : Nat) = 0 then one else 0) * f ((k + p - 0) % p) = f k
  rw [if_pos rfl, one_mul, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hk]

/-- `f^{⋆1}(k) = f k` for `k < p`. -/
theorem convPow_one (p : Nat) (f : Nat → ZOmega) {k : Nat} (hk : k < p) :
    convPow p f 1 k = f k := by
  rw [convPow_succ, convPow_zero]
  exact convOne_left p f hk

/-! ## Convolution is linear over finite sums of group-ring elements (toward the binomial theorem) -/

/-- `(0 ⋆ g)(k) = 0` — convolution by the zero element. -/
theorem conv_zero_left (p : Nat) (g : Nat → ZOmega) (k : Nat) :
    conv p (fun _ => (0 : ZOmega)) g k = 0 := by
  show sumRange (fun i => (0 : ZOmega) * g ((k + p - i) % p)) p = 0
  rw [sum_congr p (fun i _ => zero_mul (g ((k + p - i) % p)))]
  exact sum_zero_fun p

/-- ★★★★ **Convolution distributes over a finite sum on the left** — for a family `F j` of group-ring
    elements, `((Σ_{j<m} F j) ⋆ g)(k) = Σ_{j<m} (F j ⋆ g)(k)`.  By induction on `m` from
    `conv_add_left` (binary bilinearity) and `conv_zero_left`.  The left-linearity needed to expand a
    binomial sum inside an outer convolution.  ∅-axiom. -/
theorem conv_sumRange_left (p : Nat) (F : Nat → (Nat → ZOmega)) (g : Nat → ZOmega) (k : Nat) :
    ∀ m, conv p (fun i => sumRange (fun j => F j i) m) g k
       = sumRange (fun j => conv p (F j) g k) m
  | 0 => by
      show conv p (fun _ => (0 : ZOmega)) g k = (0 : ZOmega)
      exact conv_zero_left p g k
  | m + 1 => by
      show conv p (fun i => sumRange (fun j => F j i) m + F m i) g k
         = sumRange (fun j => conv p (F j) g k) m + conv p (F m) g k
      rw [conv_add_left p (fun i => sumRange (fun j => F j i) m) (F m) g k,
          conv_sumRange_left p F g k m]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow
