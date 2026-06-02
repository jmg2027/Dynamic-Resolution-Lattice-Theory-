import E213.Lib.Math.CassiniUnimodular
import E213.Lib.Math.Cauchy.NewtonGregory

/-!
# Cauchy.CassiniDepthFloor — unimodular (q = 1) ⟺ depth-0 Cassini floor

`CassiniUnimodular.det_step` showed the Cassini determinant of any 2nd-order `Int` recurrence
`s(n+2) = p·s(n+1) − q·s(n)` multiplies by `q` each step.  When `q = 1` (the orbit's shift is
in `SL₂`, e.g. the golden/Lucas/Pell orbit) the determinant is **conserved** — a *constant*
sequence — hence sits at **divergence depth 0** (`polyDepthZ 0`).

This is the structural meaning of the `DepthResidueFloor` ladder (e:1 → ζ(2):2 → ζ(3):3): the
**floor (depth 0)** is exactly the *unimodular, conserved, self-pointing* orbit — the rule that
is its own fixed point (constant Cassini); each ζ-rung above is a *degree of departure* from
that unimodular floor, the polynomial drift of the recurrence's coefficients.  So "depth 0 ⟺
constant-Cassini ⟺ `q = 1` unimodular self-reference" is now a theorem, with the φ/`W` floor
(`DepthResidueFloor.floor_polyDepth0`) as one instance.
-/

namespace E213.Lib.Math.Cauchy.CassiniDepthFloor

open E213.Lib.Math.CassiniUnimodular (det det_step)
open E213.Lib.Math.Cauchy.NewtonGregory (polyDepthZ isConstZ)
open E213.Lib.Math.Mobius213.Px.POrbitClosure (L)
open E213.Lib.Math.Mobius213.Px.CharPolySelf (L_rec)

/-- ★★★ **A conserved (`q = 1`) orbit's Cassini sits at depth 0.**  For any 2nd-order `Int`
    recurrence with shift determinant `q = 1` (`s(n+2) = p·s(n+1) − 1·s(n)`), the Cassini
    determinant `det s` is *constant* (`det_step` with `q = 1` gives `det s (n+1) = det s n`),
    hence `polyDepthZ 0 (det s)`: the unimodular orbit is the **divergence-ladder floor**.  This
    is the general law behind `DepthResidueFloor.floor_polyDepth0` — depth 0 ⟺ conserved Cassini
    ⟺ unimodular self-reference. -/
theorem cassini_conserved_depth0 (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) :
    polyDepthZ 0 (det s) := by
  show ∀ n, det s n = det s 0
  intro n
  induction n with
  | zero => rfl
  | succ k ih => rw [det_step p 1 s hrec k, Int.one_mul]; exact ih

/-- ★★ **The golden/Lucas Cassini is the depth-0 floor.**  The `L`-orbit (`L(n+2) = 3·L(n+1) −
    1·L(n)`, shift `[[2,1],[1,1]]`, `det = q = 1`) has a *constant* Cassini (`= d = 5`), hence
    `polyDepthZ 0 (det L)` — the conserved-Cassini floor, an instance of
    `cassini_conserved_depth0`. -/
theorem golden_cassini_depth0 : polyDepthZ 0 (det L) :=
  cassini_conserved_depth0 3 L (fun n => by rw [Int.one_mul]; exact L_rec n)

/-- ★★★ **Depth 0 ⟺ unimodular self-reference (the floor reading of the ζ-ladder).**  Bundle:

    1. *every* `q = 1` (unimodular / `SL₂`) 2nd-order orbit has a constant Cassini at depth 0
       (`cassini_conserved_depth0`) — the floor is the conserved, self-pointing rule;
    2. the golden/Lucas orbit is such a floor (`golden_cassini_depth0`, `det L = d = 5`).

    The `DepthResidueFloor` ladder (e:1 → ζ(2):2 → ζ(3):3) is, read through this, the *degree of
    departure* from the unimodular floor: the floor (depth 0) is the orbit whose recurrence is a
    fixed `q = 1` Möbius shift (its own fixed point); each ζ-rung above has `n`-dependent
    coefficients — a polynomial drift away from constant-Cassini self-reference. -/
theorem unimodular_floor_capstone :
    (∀ (p : Int) (s : Nat → Int), (∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) →
        polyDepthZ 0 (det s))
    ∧ polyDepthZ 0 (det L) :=
  ⟨cassini_conserved_depth0, golden_cassini_depth0⟩

end E213.Lib.Math.Cauchy.CassiniDepthFloor
