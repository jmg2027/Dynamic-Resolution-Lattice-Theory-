import E213.Math.Real213.CutSum

/-!
# Real213CauchyComplete: Cauchy completeness at cut level (3)

3 of `E1`: Cauchy completeness of Real213.

User insight (E1): "Since Real213 itself is (sequence + modulus),
Cauchy completeness is *almost trivial*".

Cut-level: sequence of cuts (cs : Nat → RealCut) is Cauchy iff it has
pointwise eventual agreement at each (m, k).  Limit = explicit witness via
modulus N.

## Definition

```
structure CauchyCutSeq where
  cs : Nat → Nat → Nat → Bool
  N : Nat → Nat → Nat
  cauchy : ∀ m k, ∀ i j ≥ N m k, cs i m k = cs j m k
```

`limit ccs := fun m k => ccs.cs (ccs.N m k) m k` — extract eventual.

## Significance

Sequence of cuts Cauchy → *direct* limit construction.  The 213 form
of Bishop completeness is trivial.
-/

namespace E213.Math.Analysis.CauchyComplete

open E213.Theory E213.Lens
open E213.Math.Cauchy.Archimedean

/-- **CauchyCutSeq**: Cauchy sequence of cuts with explicit modulus. -/
structure CauchyCutSeq where
  cs : Nat → Nat → Nat → Bool
  N : Nat → Nat → Nat
  cauchy : ∀ m k, ∀ i j, i ≥ N m k → j ≥ N m k → cs i m k = cs j m k

/-- **limit**: explicit limit extraction. -/
def CauchyCutSeq.limit (ccs : CauchyCutSeq) : Nat → Nat → Bool :=
  fun m k => ccs.cs (ccs.N m k) m k

/-- **Limit stability**: limit equals cs at *any* index past N. -/
theorem CauchyCutSeq.limit_eq_at (ccs : CauchyCutSeq)
    (m k : Nat) (i : Nat) (hi : i ≥ ccs.N m k) :
    ccs.limit m k = ccs.cs i m k := by
  unfold CauchyCutSeq.limit
  exact ccs.cauchy m k (ccs.N m k) i (Nat.le_refl _) hi

open E213.Theory E213.Lens

/-! ### Constant Cauchy sequence — sanity check -/

/-- Const cut sequence at fixed cut c (c for all i). -/
def constCauchyCutSeq (c : Nat → Nat → Bool) : CauchyCutSeq where
  cs := fun _ => c
  N := fun _ _ => 0
  cauchy := fun _ _ _ _ _ _ => rfl

/-- The limit of a constant Cauchy sequence is c. -/
theorem constCauchyCutSeq_limit (c : Nat → Nat → Bool) :
    (constCauchyCutSeq c).limit = c := rfl

end E213.Math.Analysis.CauchyComplete
