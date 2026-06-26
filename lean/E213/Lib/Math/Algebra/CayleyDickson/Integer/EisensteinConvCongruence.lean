import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence

/-!
# Congruence `mod M` propagates through convolution in `R[C_p]` (∅-axiom)

The mod-`M` congruence `ModEq` (the residue relation `M ∣ (α − β)`) is preserved when both sides are
convolved by a fixed group-ring element, and — by induction — through the convolution power:

  `conv_modEq_left`  : `(∀ i<p, f i ≡ f' i) ⟹ (f ⋆ g)(k) ≡ (f' ⋆ g)(k)`,
  `conv_modEq_right` : `(∀ i<p, g i ≡ g' i) ⟹ (f ⋆ g)(k) ≡ (f ⋆ g')(k)`,
  `convPow_modEq`    : `(∀ i<p, f i ≡ f' i) ⟹ f^{⋆q}(k) ≡ f'^{⋆q}(k)`.

This is the bridge that carries the Gauss-sum Frobenius congruence `g(χ)^{⋆q} ≡ χ(q)·g(χ̄) (mod q)` into
products: combining it with the cube `g³ = p·J` or the norm `g ⋆ ḡ = Yfun` (both `⋆`-identities) needs
`≡` to survive the convolution.  The congruence layer over the convolution layer.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvCongruence

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence
  (ModEq refl trans add_compat mul_left mul_right)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow (convPow convPow_succ)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sumRange_succ)

/-- **Congruence propagates through a finite sum** — termwise `ModEq` lifts to `ModEq` of the sums.
    Induction on `n` via `add_compat`.  ∅-axiom. -/
theorem sumRange_modEq {M : ZOmega} (F F' : Nat → ZOmega) :
    ∀ n, (∀ i, i < n → ModEq M (F i) (F' i)) → ModEq M (sumRange F n) (sumRange F' n)
  | 0, _ => refl M 0
  | n + 1, h => by
      rw [sumRange_succ, sumRange_succ]
      exact add_compat (sumRange_modEq F F' n (fun i hi => h i (Nat.lt_succ_of_lt hi)))
        (h n (Nat.lt_succ_self n))

/-- ★★★ **Convolution preserves congruence on the left** — `(∀ i<p, f i ≡ f' i) ⟹ (f⋆g)(k) ≡ (f'⋆g)(k)`.
    Each summand `f i · g(…) ≡ f' i · g(…)` by `mul_right`; `sumRange_modEq` lifts it.  ∅-axiom. -/
theorem conv_modEq_left {M : ZOmega} (p : Nat) {f f' : Nat → ZOmega} (g : Nat → ZOmega) (k : Nat)
    (h : ∀ i, i < p → ModEq M (f i) (f' i)) :
    ModEq M (conv p f g k) (conv p f' g k) :=
  sumRange_modEq _ _ p (fun i hi => mul_right (h i hi) (g ((k + p - i) % p)))

/-- ★★★ **Convolution preserves congruence on the right** — `(∀ i<p, g i ≡ g' i) ⟹ (f⋆g)(k) ≡ (f⋆g')(k)`.
    Each summand `f i · g(idx) ≡ f i · g'(idx)` by `mul_left` (the shifted index `(k+p−i)%p < p`).
    ∅-axiom. -/
theorem conv_modEq_right {M : ZOmega} (p : Nat) (f : Nat → ZOmega) {g g' : Nat → ZOmega} (k : Nat)
    (h : ∀ i, i < p → ModEq M (g i) (g' i)) :
    ModEq M (conv p f g k) (conv p f g' k) :=
  sumRange_modEq _ _ p (fun i hi =>
    mul_left (h ((k + p - i) % p) (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))) (f i))

/-- ★★★★ **The convolution power preserves congruence in the base** —
    `(∀ i<p, f i ≡ f' i) ⟹ f^{⋆q}(k) ≡ f'^{⋆q}(k)` for `k < p`.  Induction on `q`: the `convPow_succ`
    step `f^{⋆(q+1)} = f^{⋆q} ⋆ f` chains `conv_modEq_left` (inductive base congruence) and
    `conv_modEq_right` (`f ≡ f'`).  Lifts a Gauss-sum congruence to its `⋆`-powers.  ∅-axiom. -/
theorem convPow_modEq {M : ZOmega} (p : Nat) {f f' : Nat → ZOmega}
    (h : ∀ i, i < p → ModEq M (f i) (f' i)) :
    ∀ (q : Nat) {k : Nat}, k < p → ModEq M (convPow p f q k) (convPow p f' q k)
  | 0, _, _ => refl M _
  | q + 1, k, hk => by
      rw [convPow_succ, convPow_succ]
      exact trans
        (conv_modEq_left p f k (fun i hi => convPow_modEq p h q hi))
        (conv_modEq_right p (convPow p f' q) k (fun i hi => h i hi))

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvCongruence
