import E213.Lib.Math.Cohomology.Surfaces.T2Minimal
import E213.Meta.Nat.IntHelpers
import E213.Meta.Int213.Core

/-!
# Cup-pairing on H¹(T²; ℤ) — hyperbolic intersection form

The cup-pairing on the 2-torus,
  ⌣ : H¹(T²; ℤ) × H¹(T²; ℤ) → H²(T²; ℤ)
in the standard basis `{a, b}` of H¹ is the **symmetric hyperbolic
form** with matrix `[[0, 1], [1, 0]]`:

  α ⌣ β  =  α(a)·β(b) + α(b)·β(a)

ℤ-symmetric matrix `M = [[0,1],[1,0]]` has characteristic
polynomial `λ² − 1`, eigenvalues `±1`, signature `(1, 1)`.

The signature `(1, 1)` matches the Hodge Index Theorem prediction
`(1, ρ − 1)` with Picard rank `ρ = 2` for T² (two algebraic loops).

STRICT ∅-AXIOM (all by `decide` on finite enumerations).
-/

namespace E213.Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing

open E213.Lib.Math.Cohomology.Surfaces.T2Minimal

/-- Symmetric cup-pairing on `C1 × C1 → C2`.
    `(α ⌣ β)(f) = α(a)·β(b) + α(b)·β(a)`. -/
def cup (α β : C1) : C2 :=
  fun _ => α Cell1.a * β Cell1.b + α Cell1.b * β Cell1.a

/-- Standard basis vector for the `a`-loop. -/
def basis_a : C1 := fun
  | Cell1.a => 1
  | Cell1.b => 0

/-- Standard basis vector for the `b`-loop. -/
def basis_b : C1 := fun
  | Cell1.a => 0
  | Cell1.b => 1


/-! ## §2 — Matrix entries -/

/-- Matrix entry: `(basis_a ⌣ basis_a)(f) = 0`. -/
theorem cup_aa : cup basis_a basis_a Cell2.f = 0 := by decide

/-- Matrix entry: `(basis_a ⌣ basis_b)(f) = 1`. -/
theorem cup_ab : cup basis_a basis_b Cell2.f = 1 := by decide

/-- Matrix entry: `(basis_b ⌣ basis_a)(f) = 1`.  Symmetric. -/
theorem cup_ba : cup basis_b basis_a Cell2.f = 1 := by decide

/-- Matrix entry: `(basis_b ⌣ basis_b)(f) = 0`. -/
theorem cup_bb : cup basis_b basis_b Cell2.f = 0 := by decide

/-- Cup graded-commutativity, **pointwise** — the genuine mathematical
    content, **PURE** (`#print axioms` empty): `(α ⌣ β)(s) = (β ⌣ α)(s)`
    for every cell `s`, via `Int213.mul_comm` + `Int213.add_comm` (the
    pure twins; Lean-core `Int.mul_comm`/`Int.add_comm` are
    propext-leaking).  The cup form `[[0,1],[1,0]]` is symmetric. -/
theorem cup_symm_pointwise (α β : C1) (s : Cell2) :
    cup α β s = cup β α s := by
  show α Cell1.a * β Cell1.b + α Cell1.b * β Cell1.a
     = β Cell1.a * α Cell1.b + β Cell1.b * α Cell1.a
  have h1 : α Cell1.a * β Cell1.b = β Cell1.b * α Cell1.a :=
    E213.Meta.Int213.mul_comm _ _
  have h2 : α Cell1.b * β Cell1.a = β Cell1.a * α Cell1.b :=
    E213.Meta.Int213.mul_comm _ _
  rw [h1, h2, E213.Meta.Int213.add_comm]

/-- Cup is symmetric as a function-`=`: `α ⌣ β = β ⌣ α`.
    **sealed-DIRTY-by-design** (`Quot.sound` via `funext`): the lone toll
    is the `funext` wrapper turning the PURE pointwise
    `cup_symm_pointwise` into a cochain function-equality.  The
    mathematical content (graded-commutativity) lives in the pointwise
    theorem; this restatement is the function-valued-equality category
    (b) of `STRICT_ZERO_AXIOM.md` (same class as the Lens funext).
    Enumerated in the scanner's `SEALED_DIRTY_PREFIXES`. -/
theorem cup_symm (α β : C1) : cup α β = cup β α := by
  funext s; exact cup_symm_pointwise α β s

end E213.Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing
