import E213.Hypervisor.Lens
import E213.Research.DiagonalClassification

/-!
# Research.NegSqLens: fifth category of diagonal classification

The 4-way classification of Note 35 (Collapse / Idempotent /
Escalate / Multiply) is not exhaustive.  Over Bool there exists a
combine giving **sq = negation** (involution):

```
def negSqLens.combine u v := if u = v then !u else true
```

- `combine v v = !v` → sq is the negation function.
- Does not belong to any of the four categories.

The §5 claim "essentially 4 + special cases" is correct — this is one
of those special cases.

## Structural interpretation

sq is an involution: `sq (sq v) = v`.  The `not` function on Bool.
The 4-way classification covers the cases where `sq` is constant /
id / linear / quadratic; involution is a fifth possibility.
-/

namespace E213.Research.NegSqLens

open E213.Firmware E213.Hypervisor E213.Research.DiagonalClassification

/-- Negation-sq Lens on Bool.  !v on the diagonal, true off-diagonal. -/
def negSqLens : Lens Bool where
  base_a := false
  base_b := true
  combine u v := if u = v then !u else true

/-- sq negSqLens v = !v (negation). -/
theorem negSqLens_sq (v : Bool) : sq negSqLens v = !v := by
  cases v <;> rfl

/-- negSqLens is not Idempotent (sq v = !v ≠ v). -/
theorem negSqLens_not_idempotent : ¬ Idempotent negSqLens := by
  intro h
  have : (!true : Bool) = true := h true
  cases this

/-- negSqLens is not Collapse for any e (sq is non-constant). -/
theorem negSqLens_not_collapse : ¬ ∃ e : Bool, Collapse negSqLens e := by
  intro ⟨e, hC⟩
  have h1 : (!true : Bool) = e := hC true
  have h2 : (!false : Bool) = e := hC false
  have hfalse : (!true : Bool) = false := rfl
  have htrue : (!false : Bool) = true := rfl
  rw [hfalse] at h1
  rw [htrue] at h2
  rw [← h1] at h2
  cases h2

/-- combine is symmetric (satisfies the Lens AXIOM requirement). -/
theorem negSqLens_symmetric :
    ∀ u v : Bool, negSqLens.combine u v = negSqLens.combine v u := by
  intro u v; cases u <;> cases v <;> rfl

end E213.Research.NegSqLens
