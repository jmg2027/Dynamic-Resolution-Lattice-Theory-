/-!
# Lens.Instances.PointwiseProjection — pointwise projection lens

The pattern that drove the Real213 funext refactor (parts 1-15 +
Tier 3 F1).  Conceptually a Lens that views a *function*
`f : α → β → γ` through its **point-wise evaluation stream**
indexed by `(a, b) : α × β` — a function-level lens whose codomain
is the indexed family of single-point evaluations.

Concrete realisation in 213:

  - For `f : Nat → Nat → Bool` (the cut-function shape), the
    pointwise projection at `(m, k)` is the Bool `f m k`.
  - The associated equivalence is **pointwise eq**: `f ~ g` iff
    `∀ m k, f m k = g m k`.
  - This is strictly weaker than function eq `f = g` (which
    requires `funext` = `Quot.sound` in Lean's intensional type
    theory).

The Real213 `_at` variants (e.g. `cutMul_one_one_at`,
`cutSum_half_half_at`, `mvt_passthrough_unit_forward_at`) are all
witnesses that downstream theorems hold under this pointwise
projection — i.e., they live in the category of pointwise-equal
cut-functions, where the funext lens is NOT applied.
-/

namespace E213.Lens.Instances.PointwiseProjection

/-- The pointwise projection of a `Nat → Nat → Bool` function at
    a query point `(m, k)`.  The "lens view" is just function
    application — the lens itself is the implicit choice to use
    pointwise equality rather than function equality. -/
def project (f : Nat → Nat → Bool) (m k : Nat) : Bool := f m k

/-- Pointwise equivalence (the lens kernel). -/
def pointwiseEq (f g : Nat → Nat → Bool) : Prop :=
  ∀ m k, f m k = g m k

theorem pointwiseEq_refl (f : Nat → Nat → Bool) : pointwiseEq f f :=
  fun _ _ => rfl

theorem pointwiseEq_symm {f g : Nat → Nat → Bool}
    (h : pointwiseEq f g) : pointwiseEq g f :=
  fun m k => (h m k).symm

theorem pointwiseEq_trans {f g h : Nat → Nat → Bool}
    (hfg : pointwiseEq f g) (hgh : pointwiseEq g h) : pointwiseEq f h :=
  fun m k => (hfg m k).trans (hgh m k)

end E213.Lens.Instances.PointwiseProjection
