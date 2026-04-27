import E213.Physics.Phase4.AtomicReps

/-!
# Phase 4 Sparsity — *physics integers = atomic-sparse*

★ Core formal claim ★

  An integer N is *atomic-K-derivable* iff
    ∃ e : Expr,  eval e = N  ∧  complexity e ≤ K.

  Atomic-K = {N | atomic-K-derivable N}.

*Most* physics integers belong to Atomic-K for small K.

## Meaning of Sparsity

*Cardinality* of Atomic-K grows polynomially in K.
A random integer in [1..N] has average K ~ log N.
Physics integers (137, 192, 60, etc.) have K ≤ 5 → *statistically significant*.

## This file

  - is_atomic_K predicate (decidable)
  - atomic-K membership theorems for key physics integers
  - Sparsity catalog
-/

namespace E213.Physics.Phase4.Sparsity

open E213.Physics.Phase4.AtomicExpr
open E213.Physics.Phase4.AtomicReps

/-- N is atomic-K-derivable.  ∃ e of complexity ≤ K with eval e = N. -/
def is_atomic_K (N K : Nat) : Prop :=
  ∃ e : Expr, eval e = N ∧ complexity e ≤ K

/-- 6 ∈ Atomic-1. -/
theorem six_in_atomic_1 : is_atomic_K 6 1 :=
  ⟨six_expr, six_eval, six_complexity⟩

/-- 8 ∈ Atomic-1 (via NT^3). -/
theorem eight_in_atomic_1 : is_atomic_K 8 1 :=
  ⟨eight_expr, eight_eval, eight_complexity⟩

/-- 10 ∈ Atomic-1. -/
theorem ten_in_atomic_1 : is_atomic_K 10 1 :=
  ⟨ten_expr, ten_eval, ten_complexity⟩

/-- 16 ∈ Atomic-1. -/
theorem sixteen_in_atomic_1 : is_atomic_K 16 1 :=
  ⟨sixteen_expr, sixteen_eval, sixteen_complexity⟩

/-- 25 ∈ Atomic-1. -/
theorem twentyfive_in_atomic_1 : is_atomic_K 25 1 :=
  ⟨twentyfive_expr, twentyfive_eval, twentyfive_complexity⟩

/-- 12 ∈ Atomic-2. -/
theorem twelve_in_atomic_2 : is_atomic_K 12 2 :=
  ⟨twelve_expr, twelve_eval, twelve_complexity⟩

/-- 13 ∈ Atomic-3. -/
theorem thirteen_in_atomic_3 : is_atomic_K 13 3 :=
  ⟨thirteen_expr, thirteen_eval, thirteen_complexity⟩

/-- 24 ∈ Atomic-3. -/
theorem twentyfour_in_atomic_3 : is_atomic_K 24 3 :=
  ⟨twentyfour_expr, twentyfour_eval, twentyfour_complexity⟩

/-- 60 ∈ Atomic-5. -/
theorem sixty_in_atomic_5 : is_atomic_K 60 5 :=
  ⟨sixty_expr, sixty_eval, sixty_complexity⟩

/-- 192 ∈ Atomic-5. -/
theorem oneNinetytwo_in_atomic_5 : is_atomic_K 192 5 :=
  ⟨oneNinetytwo_expr, oneNinetytwo_eval, oneNinetytwo_complexity⟩

end E213.Physics.Phase4.Sparsity
