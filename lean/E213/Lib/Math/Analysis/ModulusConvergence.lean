import E213.Lib.Math.Analysis.UniformLimitContinuous

/-!
# Modulus convergence: uniqueness of limits + convergent ⟹ Cauchy (∅-axiom)

Basic limit theory on the `MetricModulus` structure (this session's
`1/2^m`-graduated dyadic metric, `Analysis/UniformLimitContinuous`).  A sequence
*converges with a modulus* `r` when `∀ m, ∀ n ≥ r m, close m (a n) L`.  Two
unconditional ∅-axiom facts, each a single halving-triangle (`ctri`) argument:

* `limit_unique` — a sequence has at most one limit, **located** to every scale
  (`∀ m, close m L L'`): the residue picture (the limit is reached by none, but
  two limits coincide at every resolution).
* `conv_imp_cauchy` — a convergent sequence is Cauchy, with the Cauchy modulus
  *computed* from the convergence modulus (`r (m+1)`).

Companion to `ExtremeValue` / `UniformLimitContinuous` / `BanachFixedPoint`,
which all ride on the same four metric laws.
-/

namespace E213.Lib.Math.Analysis.ModulusConvergence

open E213.Lib.Math.Analysis.UniformLimitContinuous (MetricModulus distMet)

variable {X : Type} (M : MetricModulus X)

/-- `a` converges to `L` with modulus `r`: within `1/2^m` from index `r m` on. -/
def ConvergesWith (a : Nat → X) (L : X) (r : Nat → Nat) : Prop :=
  ∀ m n, r m ≤ n → M.close m (a n) L

/-- A constant sequence converges to its value (modulus `0`). -/
theorem const_converges (c : X) : ConvergesWith M (fun _ => c) c (fun _ => 0) :=
  fun m _ _ => M.crefl m c

/-- ★ **Uniqueness of limits, located to every scale.**  If `a → L` and `a → L'`
    (each with a modulus), then `close m L L'` for every `m`: the two limits
    coincide at every resolution.  One halving triangle through a common index
    `n ≥ r(m+1), r'(m+1)`. -/
theorem limit_unique {a : Nat → X} {L L' : X} {r r' : Nat → Nat}
    (h : ConvergesWith M a L r) (h' : ConvergesWith M a L' r') :
    ∀ m, M.close m L L' := by
  intro m
  have hn1 : r (m + 1) ≤ r (m + 1) + r' (m + 1) := Nat.le_add_right _ _
  have hn2 : r' (m + 1) ≤ r (m + 1) + r' (m + 1) := Nat.le_add_left _ _
  have c1 : M.close (m + 1) (a (r (m + 1) + r' (m + 1))) L := h (m + 1) _ hn1
  have c2 : M.close (m + 1) (a (r (m + 1) + r' (m + 1))) L' := h' (m + 1) _ hn2
  exact M.ctri m L _ L' (M.csymm (m + 1) _ L c1) c2

/-- ★ **Convergent ⟹ Cauchy, modulus computed.**  If `a → L` with modulus `r`,
    then for `p, q ≥ r (m+1)`, `close m (a p) (a q)` — the Cauchy modulus
    `r (·+1)` is read off the convergence modulus.  One halving triangle
    through `L`. -/
theorem conv_imp_cauchy {a : Nat → X} {L : X} {r : Nat → Nat}
    (h : ConvergesWith M a L r) :
    ∀ m p q, r (m + 1) ≤ p → r (m + 1) ≤ q → M.close m (a p) (a q) := by
  intro m p q hp hq
  have c1 : M.close (m + 1) (a p) L := h (m + 1) p hp
  have c2 : M.close (m + 1) (a q) L := h (m + 1) q hq
  exact M.ctri m (a p) L (a q) c1 (M.csymm (m + 1) (a q) L c2)

/-- A subsequence (via any index map `g` with `g n ≥ n`) converges to the same
    limit with the same modulus — the limit is index-reparametrisation-invariant. -/
theorem subseq_converges {a : Nat → X} {L : X} {r : Nat → Nat}
    (h : ConvergesWith M a L r) (g : Nat → Nat) (hg : ∀ n, n ≤ g n) :
    ConvergesWith M (fun n => a (g n)) L (fun m => r m) :=
  fun m n hn => h m (g n) (Nat.le_trans hn (hg n))

/-! ## Non-vacuous: the concrete `distMet` metric on `Nat` -/

/-- `limit_unique` instantiated on `distMet 0`: a `Nat`-valued sequence has a
    located-unique limit. -/
theorem limit_unique_distMet {a : Nat → Nat} {L L' : Nat} {r r' : Nat → Nat}
    (h : ConvergesWith (distMet 0) a L r) (h' : ConvergesWith (distMet 0) a L' r') :
    ∀ m, (distMet 0).close m L L' :=
  limit_unique (distMet 0) h h'

end E213.Lib.Math.Analysis.ModulusConvergence
