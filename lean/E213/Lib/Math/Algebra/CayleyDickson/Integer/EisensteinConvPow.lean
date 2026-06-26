import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssoc
import E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality

/-!
# The convolution identity and power in the group ring `R[C_p]` (∅-axiom)

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
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing
  (conv conv_add_left conv_scalar_left conv_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm (conv_comm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssoc (conv_assoc)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality
  (one one_mul pow pow_zero pow_succ)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
  (sumRange sum_single sum_congr sum_zero_fun sum_mul_left)
open E213.Meta.Algebra213.Ring213 (zero_mul mul_zero mul_assoc)
open E213.Meta.Algebra213.CommRing213 (mul_comm)

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

/-- ★★★★ **The right identity law** — `(f ⋆ e_0)(k) = f k` for `k < p`.  Immediate from
    `convOne_left` via commutativity (`conv_comm`).  ∅-axiom. -/
theorem convOne_right (p : Nat) (f : Nat → ZOmega) {k : Nat} (hk : k < p) :
    conv p f delta k = f k := by
  rw [conv_comm p f delta hk]; exact convOne_left p f hk

/-- `f^{⋆1}(k) = f k` for `k < p`. -/
theorem convPow_one (p : Nat) (f : Nat → ZOmega) {k : Nat} (hk : k < p) :
    convPow p f 1 k = f k := by
  rw [convPow_succ, convPow_zero]
  exact convOne_left p f hk

/-- ★★★★ **The convolution power respects agreement on `[0,p)`** — if `f i = f' i` for all `i < p`,
    then `f^{⋆q}(k) = f'^{⋆q}(k)` for `k < p`.  By induction on `q` via `conv_congr`.  Lets a base
    function be swapped for any `[0,p)`-equal representative inside a `⋆`-power.  ∅-axiom. -/
theorem convPow_congr (p : Nat) {f f' : Nat → ZOmega} (hp : 0 < p)
    (hff : ∀ i, i < p → f i = f' i) :
    ∀ (q : Nat) {k : Nat}, k < p → convPow p f q k = convPow p f' q k
  | 0, _, _ => rfl
  | q + 1, k, hk => by
      rw [convPow_succ, convPow_succ]
      exact conv_congr p k hp (fun i hi => convPow_congr p hp hff q hi) (fun i hi => hff i hi)

/-! ## Convolution is linear over finite sums of group-ring elements (toward the binomial theorem) -/

/-- `(0 ⋆ g)(k) = 0` — convolution by the zero element. -/
theorem conv_zero_left (p : Nat) (g : Nat → ZOmega) (k : Nat) :
    conv p (fun _ => (0 : ZOmega)) g k = 0 := by
  show sumRange (fun i => (0 : ZOmega) * g ((k + p - i) % p)) p = 0
  rw [sum_congr p (fun i _ => zero_mul (g ((k + p - i) % p)))]
  exact sum_zero_fun p

/-- `(f ⋆ 0)(k) = 0` — convolution by the zero element on the right. -/
theorem conv_zero_right (p : Nat) (f : Nat → ZOmega) (k : Nat) :
    conv p f (fun _ => (0 : ZOmega)) k = 0 := by
  show sumRange (fun i => f i * (0 : ZOmega)) p = 0
  rw [sum_congr p (fun i _ => mul_zero (f i))]
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

/-! ## Right scalar pull and the scalar convolution power -/

/-- **Right scalar pull** — `(f ⋆ (c·g))(k) = c·(f ⋆ g)(k)`.  `mul_comm`/`mul_assoc` termwise, then
    `sum_mul_left`.  The companion of `conv_scalar_left`.  ∅-axiom. -/
theorem conv_scalar_right (p : Nat) (c : ZOmega) (f g : Nat → ZOmega) (k : Nat) :
    conv p f (fun i => c * g i) k = c * conv p f g k := by
  show sumRange (fun i => f i * (c * g ((k + p - i) % p))) p
     = c * sumRange (fun i => f i * g ((k + p - i) % p)) p
  rw [← sum_mul_left c (fun i => f i * g ((k + p - i) % p)) p]
  exact sum_congr p (fun i _ => by
    rw [← mul_assoc (f i) c (g ((k + p - i) % p)), mul_comm (f i) c,
        mul_assoc c (f i) (g ((k + p - i) % p))])

/-- ★★★★ **The scalar convolution power** — `(c · h)^{⋆q}(k) = c^q · h^{⋆q}(k)` for `k < p`.  By
    induction: `(c·h)^{⋆(q+1)} = (c^q·h^{⋆q}) ⋆ (c·h) = c^q·c·(h^{⋆q} ⋆ h) = c^{q+1}·h^{⋆(q+1)}`
    (`conv_scalar_left` + `conv_scalar_right`).  Lets a scaled basis vector `χ(t)·e_t` be powered:
    `(χ(t)·e_t)^{⋆q} = χ(t)^q · e_t^{⋆q}`.  ∅-axiom. -/
theorem convPow_scalar (p : Nat) (c : ZOmega) (h : Nat → ZOmega) :
    ∀ (q : Nat) {k : Nat}, k < p → convPow p (fun i => c * h i) q k = pow c q * convPow p h q k
  | 0, k, _ => by
      show delta k = pow c 0 * delta k
      rw [pow_zero, one_mul]
  | q + 1, k, hk => by
      have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
      rw [convPow_succ,
          conv_congr p k hp (fun i hi => convPow_scalar p c h q hi) (fun _ _ => rfl),
          conv_scalar_left p (pow c q) (convPow p h q) (fun i => c * h i) k,
          conv_scalar_right p c (convPow p h q) h k,
          convPow_succ, pow_succ, mul_assoc (pow c q) c (conv p (convPow p h q) h k)]

/-! ## Convolution-power exponent raising (the `⋆`-analogs of `bterm_mul_a` / `bterm_mul_b`) -/

/-- **Raise the `f`-exponent** — `((f^{⋆j} ⋆ g^{⋆m}) ⋆ f)(k) = (f^{⋆(j+1)} ⋆ g^{⋆m})(k)` for `k<p`.
    `conv_assoc` to `f^{⋆j} ⋆ (g^{⋆m} ⋆ f)`, `conv_comm` to commute `g^{⋆m} ⋆ f`, `conv_assoc` back,
    then `convPow_succ` (`f^{⋆j} ⋆ f = f^{⋆(j+1)}`).  ∅-axiom. -/
theorem convProd_mul_f (p : Nat) (f g : Nat → ZOmega) (j m : Nat) {k : Nat} (hk : k < p) :
    conv p (fun i => conv p (convPow p f j) (convPow p g m) i) f k
      = conv p (convPow p f (j + 1)) (convPow p g m) k := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  rw [conv_assoc p (convPow p f j) (convPow p g m) f hk,
      conv_congr p k hp (fun _ _ => rfl) (fun i hi => conv_comm p (convPow p g m) f hi),
      ← conv_assoc p (convPow p f j) f (convPow p g m) hk]
  exact conv_congr p k hp (fun _ _ => rfl) (fun _ _ => rfl)

/-- **Raise the `g`-exponent** — `((f^{⋆j} ⋆ g^{⋆m}) ⋆ g)(k) = (f^{⋆j} ⋆ g^{⋆(m+1)})(k)` for `k<p`.
    `conv_assoc` then `convPow_succ` (`g^{⋆m} ⋆ g = g^{⋆(m+1)}`); no commutation needed.  ∅-axiom. -/
theorem convProd_mul_g (p : Nat) (f g : Nat → ZOmega) (j m : Nat) {k : Nat} (hk : k < p) :
    conv p (fun i => conv p (convPow p f j) (convPow p g m) i) g k
      = conv p (convPow p f j) (convPow p g (m + 1)) k := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  rw [conv_assoc p (convPow p f j) (convPow p g m) g hk]
  exact conv_congr p k hp (fun _ _ => rfl) (fun _ _ => rfl)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow
