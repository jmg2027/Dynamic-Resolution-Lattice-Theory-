/-!
# Hypervisor.Lens.Instances.CochainEntry — cochain-entry lens

The pattern formalised by `delta_pointwise_eq` (Cohomology/Delta/
Pointwise.lean).  A cochain `σ : Cochain n k = Fin (binom n k) →
Bool` is viewed through its **per-entry value** at each Fin index.

Concrete realisation:

  - `Cochain n k = Fin (binom n k) → Bool`
  - Per-entry projection: `entry σ i = σ i`
  - `delta_pointwise_eq`: if `σ i = τ i ∀ i`, then `delta σ = delta τ`
    pointwise — lifting cochain entry-eq to delta entry-eq.
  - Used in `dsq_zero_prop_3_0`, `dsq_zero_prop_5_0`,
    `dsq_zero_prop_3_1`, etc. (parts 9-15 cohomology cleanup).

This lens is what makes Universal δ²=0 propositional lifts strict
∅-axiom: instead of using funext to lift `pattern_eq` to function
eq, we apply `delta_pointwise_eq` twice and stay at the entry level.
-/

namespace E213.Lens.Instances.CochainEntry

/-- The entry projection: `σ i` for a cochain σ at Fin index i. -/
def entry {N : Nat} (σ : Fin N → Bool) (i : Fin N) : Bool := σ i

/-- Entry-wise equivalence: two cochains agree at every Fin index. -/
def entryEq {N : Nat} (σ τ : Fin N → Bool) : Prop :=
  ∀ i : Fin N, σ i = τ i

theorem entryEq_refl {N : Nat} (σ : Fin N → Bool) : entryEq σ σ :=
  fun _ => rfl

theorem entryEq_symm {N : Nat} {σ τ : Fin N → Bool}
    (h : entryEq σ τ) : entryEq τ σ := fun i => (h i).symm

theorem entryEq_trans {N : Nat} {σ τ ρ : Fin N → Bool}
    (hστ : entryEq σ τ) (hτρ : entryEq τ ρ) : entryEq σ ρ :=
  fun i => (hστ i).trans (hτρ i)

end E213.Lens.Instances.CochainEntry
